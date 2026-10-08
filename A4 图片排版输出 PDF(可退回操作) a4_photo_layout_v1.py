# -*- coding: utf-8 -*-
"""
A4 照片排版工具 V3
==================

功能：
 1. 添加图片（可多选）
 2. 左侧列表支持从 Windows 资源管理器拖入单张/多张图片
 3. 支持拖入一个或多个文件夹，并递归扫描图片
 4. 自动跳过重复图片
 5. 左侧列表与右侧预览联动
 6. 长按右侧图片后拖动调整图片顺序
 7. 顺时针 / 逆时针 90° 旋转
 8. 导出 A4 PDF
 9. 【V3 新增】把导出的 PDF 重新导入，继续编辑
10. Windows 打印（稳定的"选择打印机"窗口 + 正确的纸张比例）
11. 【V3 新增】排版可选：1×1 / 2×2 / 2×3 / 3×2 / 3×3（默认）/ 3×4 / 4×3 / 4×4
    （工具栏第二行"排版"下拉框；导出的 PDF 会记录排版，重新导入时自动恢复）

V3 新增的"PDF 可再编辑"是怎么做的
---------------------------------
导出 PDF 时，除了页面本身，还会在 PDF 里写一个独立的流对象
（/Type /A4PLState），里面用 zlib 压缩保存了一份 JSON：

    {"grid":[3,3], "margin_mm":10.0, "padding_mm":1.5, "dpi":300,
     "images":[{"p":"C:/照片/IMG_0001.jpg","r":90}, ...]}

这个对象不被任何页面引用，Acrobat / Edge / 打印机都会忽略它，但本工具
可以把它读回来，于是"顺序、旋转、排版参数"都能还原，照片仍然是原始文件
（不是从 PDF 里抠出来的低质量副本）。

再次导入这个 PDF 时：
  * 有编辑信息  -> 原样恢复照片列表；某张原图如果被移动/删除，
                   就从 PDF 页面对应的格子里把那张照片抠出来顶替它；
  * 没有编辑信息 -> 先把页面自己合成出来（解析内容流里的 cm/Do 摆放关系，
                   相当于"扫描"这一页），再按四种方式之一导入：
                     按空白间隔自动拆分 / 每页一张整页图片 /
                     按网格等分拆分（行列可选）/ 每张位图分别导入。
                   这样别的软件生成的图片型 PDF（扫描件、水印相机照片表、
                   报表截图导出）也能拆成照片继续编辑。

V3 相对 V2 的修正
-----------------
  * 带 EXIF 方向的手机照片不再被拉伸变形（宽高按修正后的方向记录）
  * 打印不再按纸张物理尺寸硬铺满（非 A4 纸张不再变形），改为等比缩放居中
  * 打印用的分辨率不再跟随"导出质量"（2400 DPI 会直接把内存打爆）
  * 导出改为逐页流式写入，内存占用恒定，页数多也不会吃满内存
  * PDF 内 JPEG 质量可调（V2 用的是 Pillow 默认值 75，照片偏软）
  * 高 DPI 选项收敛为 150 / 300 / 450 / 600

运行环境：Python 3.8+、Pillow；拖放需要 tkinterdnd2，打印需要 pywin32。
"""

import atexit
import io
import json
import os
import re
import shutil
import struct
import sys
import tempfile
import time
import traceback
import zlib

from tkinter import *
from tkinter import ttk, filedialog, messagebox

from PIL import Image, ImageDraw, ImageOps, ImageTk

# ---------- Windows 文件拖放 ----------
DND_AVAILABLE = False
try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    DND_AVAILABLE = True
except ImportError:
    TkinterDnD = None
    DND_FILES = None

# ---------- Windows 打印 ----------
PRINT_AVAILABLE = False
try:
    import win32print
    import win32ui
    import win32con
    import win32gui
    from PIL import ImageWin
    PRINT_AVAILABLE = True
except ImportError:
    win32print = None
    win32ui = None
    win32con = None
    win32gui = None
    ImageWin = None

APP_NAME = "A4 照片排版工具 V3"
APP_TAG = "A4PhotoLayout"

# ==============================================================
# PDF 引擎（自包含，无第三方依赖）
# --------------------------------------------------------------
# 这一节负责两件事：
#   1) 写入 PDF —— 逐页流式写，内存占用恒定；同时在 PDF 里写入
#      一个 /Type /A4PLState 的流对象，保存"可再编辑信息"。
#      该对象不被任何页面引用，Acrobat / 浏览器 / 打印机都会忽略它。
#   2) 读取 PDF —— 支持传统 xref 表、xref 流、对象流，支持常见的
#      图像过滤器（Flate/DCT/JPX/CCITT/LZW/ASCIIHex/ASCII85/RunLength），
#      用于把 PDF 里的照片重新提取出来。
# 这一节可以整体复制到别的脚本里独立使用。
# ==============================================================
import io
import json
import re
import struct
import time
import zlib

from PIL import Image

try:  # numpy 只用于加速（可选）
    import numpy as _np
except Exception:  # pragma: no cover
    _np = None

HAVE_NUMPY = _np is not None

A4_W_MM = 210.0
A4_H_MM = 297.0
MM_TO_PT = 72.0 / 25.4
A4_W_PT = A4_W_MM * MM_TO_PT
A4_H_PT = A4_H_MM * MM_TO_PT

STATE_VERSION = 3
STATE_TYPE = "A4PLState"


class PdfError(Exception):
    """PDF 解析/写入错误。"""


# ==============================================================
# 1. PDF 基础对象
# ==============================================================
class PdfName(str):
    """PDF 名字对象（/Name）。"""
    __slots__ = ()

    def __repr__(self):
        return "/" + str(self)


class PdfRef(object):
    """间接引用（num gen R）。"""
    __slots__ = ("num", "gen")

    def __init__(self, num, gen=0):
        self.num = int(num)
        self.gen = int(gen)

    def __repr__(self):
        return "%d %d R" % (self.num, self.gen)

    def __eq__(self, other):
        return isinstance(other, PdfRef) and (self.num, self.gen) == (other.num, other.gen)

    def __hash__(self):
        return hash((self.num, self.gen))


class PdfStream(object):
    """流对象：dict 为流字典，raw 为原始（未解码）字节。"""
    __slots__ = ("dict", "raw", "_doc", "_data")

    def __init__(self, d, raw, doc=None):
        self.dict = d
        self.raw = raw
        self._doc = doc
        self._data = None

    @property
    def data(self):
        """按 /Filter 解码后的字节。"""
        if self._data is None:
            if self._doc is None:
                self._data = self.raw
            else:
                self._data = self._doc.stream_data(self)
        return self._data

    def __repr__(self):
        return "<PdfStream len=%d %s>" % (len(self.raw), self.dict)


# ==============================================================
# 2. 语法解析
# ==============================================================
_WS = b"\x00\t\n\x0c\r "
_DELIM = b"()<>[]{}/%"
_NUM_RE = re.compile(rb"[+-]?(?:\d+\.\d*|\.\d+|\d+)")
_NAME_RE = re.compile(rb"/[^\x00\t\n\x0c\r ()<>\[\]{}/%]*")
_REF_RE = re.compile(rb"(\d{1,10})\s+(\d{1,5})\s+R(?![A-Za-z0-9])")
_OBJ_RE = re.compile(rb"(\d{1,10})\s+(\d{1,5})\s+obj\b")
_HEX_RE = re.compile(rb"[0-9A-Fa-f\s]*")
_XREF_ENTRY_RE = re.compile(rb"(\d{1,10})\s+(\d{1,5})\s+([nf])")
_WS_RE = re.compile(rb"[\x00\t\n\x0c\r ]*")


def _decode_name(raw):
    """把 /Name 里的 #XX 转义还原。"""
    if b"#" not in raw:
        return raw.decode("latin-1")
    out = bytearray()
    i = 0
    while i < len(raw):
        c = raw[i]
        if c == 0x23 and i + 2 < len(raw):
            try:
                out.append(int(raw[i + 1:i + 3], 16))
                i += 3
                continue
            except ValueError:
                pass
        out.append(c)
        i += 1
    return bytes(out).decode("latin-1")


class _Parser(object):
    """极简 PDF 语法解析器。"""

    def __init__(self, data, pos=0, doc=None):
        self.data = data
        self.pos = pos
        self.doc = doc

    def skip_ws(self):
        """跳过空白和 % 注释（注释在真实 PDF 的字典/数组里很常见）。"""
        d = self.data
        n = len(d)
        i = self.pos
        while i < n:
            c = d[i]
            if c in _WS:
                i += 1
            elif c == 0x25:  # '%'
                j = d.find(b"\n", i)
                if j < 0:
                    i = n
                    break
                i = j + 1
            else:
                break
        self.pos = i

    def read_word(self):
        d = self.data
        i = self.pos
        n = len(d)
        while i < n and d[i] not in _WS and d[i] not in _DELIM:
            i += 1
        word = d[self.pos:i]
        self.pos = i
        return word

    def parse(self):
        self.skip_ws()
        d = self.data
        i = self.pos
        if i >= len(d):
            raise PdfError("意外的文件结尾")
        c = d[i:i + 1]
        if c == b"<":
            if d[i:i + 2] == b"<<":
                self.pos = i + 2
                return self._parse_dict()
            return self._parse_hex_string()
        if c == b"[":
            self.pos = i + 1
            return self._parse_array()
        if c == b"(":
            return self._parse_literal_string()
        if c == b"/":
            m = _NAME_RE.match(d, i)
            self.pos = m.end()
            return PdfName(_decode_name(m.group()[1:]))
        m = _REF_RE.match(d, i)
        if m:
            self.pos = m.end()
            return PdfRef(int(m.group(1)), int(m.group(2)))
        m = _NUM_RE.match(d, i)
        if m:
            self.pos = m.end()
            t = m.group()
            return float(t) if (b"." in t) else int(t)
        word = self.read_word()
        if word == b"true":
            return True
        if word == b"false":
            return False
        if word == b"null":
            return None
        if word == b"":
            raise PdfError("无法解析的对象 @%d" % i)
        return PdfName(word.decode("latin-1"))

    def _parse_dict(self):
        result = {}
        while True:
            self.skip_ws()
            d = self.data
            if d[self.pos:self.pos + 2] == b">>":
                self.pos += 2
                break
            if self.pos >= len(d):
                raise PdfError("字典未闭合")
            key = self.parse()
            if not isinstance(key, PdfName):
                raise PdfError("字典键不是名字对象：%r" % (key,))
            result[str(key)] = self.parse()
        # 流对象？
        save = self.pos
        self.skip_ws()
        if self.data[self.pos:self.pos + 6] == b"stream":
            self.pos += 6
            if self.data[self.pos:self.pos + 2] == b"\r\n":
                self.pos += 2
            elif self.data[self.pos:self.pos + 1] in (b"\n", b"\r"):
                self.pos += 1
            start = self.pos
            length = result.get("Length")
            if isinstance(length, PdfRef) and self.doc is not None:
                try:
                    length = self.doc.get(length)
                except Exception:
                    length = None
            raw = None
            if isinstance(length, (int, float)) and length >= 0:
                end = start + int(length)
                if end <= len(self.data):
                    tail = self.data[end:end + 24]
                    if b"endstream" in tail:
                        raw = self.data[start:end]
                        self.pos = end
            if raw is None:  # /Length 不可用时直接找 endstream
                j = self.data.find(b"endstream", start)
                if j < 0:
                    raise PdfError("流没有 endstream")
                raw = self.data[start:j]
                if raw.endswith(b"\r\n"):
                    raw = raw[:-2]
                elif raw.endswith(b"\n") or raw.endswith(b"\r"):
                    raw = raw[:-1]
                self.pos = j + 9
            else:
                j = self.data.find(b"endstream", self.pos)
                if j >= 0:
                    self.pos = j + 9
            return PdfStream(result, raw, self.doc)
        self.pos = save
        return result

    def _parse_array(self):
        out = []
        while True:
            self.skip_ws()
            d = self.data
            if d[self.pos:self.pos + 1] == b"]":
                self.pos += 1
                break
            if self.pos >= len(d):
                raise PdfError("数组未闭合")
            out.append(self.parse())
        return out

    def _parse_literal_string(self):
        d = self.data
        i = self.pos + 1
        depth = 1
        out = bytearray()
        n = len(d)
        while i < n:
            c = d[i]
            if c == 0x5C:  # backslash
                i += 1
                if i >= n:
                    break
                e = d[i]
                if e in b"nrtbf":
                    out.append({0x6E: 10, 0x72: 13, 0x74: 9, 0x62: 8, 0x66: 12}[e])
                    i += 1
                elif e in b"()\\":
                    out.append(e)
                    i += 1
                elif 0x30 <= e <= 0x37:  # 八进制
                    j = i
                    oct_digits = b""
                    while j < n and len(oct_digits) < 3 and 0x30 <= d[j] <= 0x37:
                        oct_digits += d[j:j + 1]
                        j += 1
                    out.append(int(oct_digits, 8) & 0xFF)
                    i = j
                elif e in b"\r\n":  # 续行
                    i += 2 if d[i:i + 2] == b"\r\n" else 1
                else:
                    out.append(e)
                    i += 1
                continue
            if c == 0x28:
                depth += 1
            elif c == 0x29:
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            out.append(c)
            i += 1
        self.pos = i
        return bytes(out)

    def _parse_hex_string(self):
        d = self.data
        m = _HEX_RE.match(d, self.pos + 1)
        text = re.sub(rb"\s", b"", m.group())
        self.pos = d.find(b">", m.end())
        self.pos = len(d) if self.pos < 0 else self.pos + 1
        if len(text) % 2:
            text += b"0"
        try:
            return bytes.fromhex(text.decode("ascii"))
        except ValueError:
            return b""


# ==============================================================
# 3. 过滤器解码
# ==============================================================
def _apply_predictor(data, parms, default_bpc=8):
    """实现 PDF 的 /Predictor（PNG 预测器 10-15，TIFF 预测器 2）。"""
    predictor = int(parms.get("Predictor", 1) or 1)
    if predictor <= 1:
        return data
    colors = int(parms.get("Colors", 1) or 1)
    bpc = int(parms.get("BitsPerComponent", default_bpc) or default_bpc)
    columns = int(parms.get("Columns", 1) or 1)
    rowlen = (columns * colors * bpc + 7) // 8
    if rowlen <= 0:
        return data

    if predictor == 2:  # TIFF 预测器：同一行内按分量累加
        if bpc != 8:
            return data
        bpp = max(1, (colors + 7) // 8)
        return _predict_sub(data, rowlen, bpp)

    # PNG 预测器：每行前面有 1 字节过滤器类型
    if len(data) < rowlen + 1:
        return data
    rows = len(data) // (rowlen + 1)
    bpp = max(1, (colors * bpc + 7) // 8)
    if _np is not None:
        try:
            return _predict_png_numpy(data, rowlen, bpp, rows)
        except Exception:
            pass
    out = bytearray()
    prev = bytearray(rowlen)
    pos = 0
    for _ in range(rows):
        ft = data[pos]
        row = bytearray(data[pos + 1:pos + 1 + rowlen])
        pos += 1 + rowlen
        if ft == 1:
            for i in range(bpp, rowlen):
                row[i] = (row[i] + row[i - bpp]) & 0xFF
        elif ft == 2:
            for i in range(rowlen):
                row[i] = (row[i] + prev[i]) & 0xFF
        elif ft == 3:
            for i in range(rowlen):
                left = row[i - bpp] if i >= bpp else 0
                row[i] = (row[i] + ((left + prev[i]) >> 1)) & 0xFF
        elif ft == 4:
            for i in range(rowlen):
                a = row[i - bpp] if i >= bpp else 0
                b = prev[i]
                c = prev[i - bpp] if i >= bpp else 0
                pa = abs(b - c)
                pb = abs(a - c)
                pc = abs(a + b - 2 * c)
                pr = a if (pa <= pb and pa <= pc) else (b if pb <= pc else c)
                row[i] = (row[i] + pr) & 0xFF
        out += row
        prev = row
    return bytes(out)


def _predict_sub(data, rowlen, bpp):
    """Sub / TIFF 预测器：按相位累加（numpy 加速）。"""
    if _np is not None:
        arr = _np.frombuffer(data, dtype=_np.uint8)
        usable = (len(arr) // rowlen) * rowlen
        if usable == 0:
            return data
        arr = arr[:usable].reshape(-1, rowlen).astype(_np.int64)
        for p in range(bpp):
            arr[:, p::bpp] = _np.cumsum(arr[:, p::bpp], axis=1) & 0xFF
        return arr.astype(_np.uint8).tobytes()
    out = bytearray(data)
    for row_start in range(0, len(out) - rowlen + 1, rowlen):
        for i in range(row_start + bpp, row_start + rowlen):
            out[i] = (out[i] + out[i - bpp]) & 0xFF
    return bytes(out)


def _predict_png_numpy(data, rowlen, bpp, rows):
    arr = _np.frombuffer(data, dtype=_np.uint8)
    arr = arr[:rows * (rowlen + 1)].reshape(rows, rowlen + 1)
    ftypes = arr[:, 0]
    body = arr[:, 1:].astype(_np.int64)
    out = _np.empty_like(body)
    prev = _np.zeros(rowlen, dtype=_np.int64)
    for i in range(rows):
        ft = int(ftypes[i])
        row = body[i].copy()
        if ft == 0:
            cur = row
        elif ft == 1:
            for p in range(bpp):
                row[p::bpp] = _np.cumsum(row[p::bpp]) & 0xFF
            cur = row
        elif ft == 2:
            cur = (row + prev) & 0xFF
        elif ft == 3:
            for j in range(rowlen):
                left = row[j - bpp] if j >= bpp else 0
                row[j] = (row[j] + ((left + prev[j]) >> 1)) & 0xFF
            cur = row
        elif ft == 4:
            for j in range(rowlen):
                a = row[j - bpp] if j >= bpp else 0
                b = prev[j]
                c = prev[j - bpp] if j >= bpp else 0
                pa = abs(b - c)
                pb = abs(a - c)
                pc = abs(a + b - 2 * c)
                pr = a if (pa <= pb and pa <= pc) else (b if pb <= pc else c)
                row[j] = (row[j] + pr) & 0xFF
            cur = row
        else:
            cur = row
        out[i] = cur
        prev = cur
    return out.astype(_np.uint8).tobytes()


def _lzw_decode(data, early=1):
    """PDF LZWDecode（MSB first）。仅作尽力解析。"""
    table = [bytes([i]) for i in range(256)] + [b"", b""]
    out = bytearray()
    bitpos = 0
    codelen = 9
    prev = None
    total = len(data) * 8
    while bitpos + codelen <= total:
        byte_i = bitpos >> 3
        shift = bitpos & 7
        chunk = int.from_bytes(data[byte_i:byte_i + 3].ljust(3, b"\x00"), "big")
        code = (chunk >> (24 - shift - codelen)) & ((1 << codelen) - 1)
        bitpos += codelen
        if code == 256:
            table = table[:258]
            codelen = 9
            prev = None
            continue
        if code == 257:
            break
        if prev is None:
            if code >= len(table):
                break
            entry = table[code]
        else:
            if code < len(table):
                entry = table[code]
            elif code == len(table):
                entry = prev + prev[:1]
            else:
                break
            table.append(prev + entry[:1])
            if len(table) + early >= (1 << codelen) and codelen < 12:
                codelen += 1
        out += entry
        prev = entry
    return bytes(out)


def _ascii_hex_decode(data):
    text = re.sub(rb"[^0-9A-Fa-f]", b"", data.split(b">")[0])
    if len(text) % 2:
        text += b"0"
    return bytes.fromhex(text.decode("ascii"))


_ASCII85_RE = re.compile(rb"z|[!-u]{2,5}")


def _ascii85_decode(data):
    data = data.split(b"~>")[0]
    out = bytearray()
    for m in _ASCII85_RE.finditer(data):
        tok = m.group()
        if tok == b"z":
            out += b"\x00\x00\x00\x00"
            continue
        if len(tok) < 2:
            continue
        value = 0
        for ch in tok:
            value = value * 85 + (ch - 33)
        pad = 5 - len(tok)
        # 末组用 'u'(84) 补齐，并且只输出 len(tok)-1 个字节
        for _ in range(pad):
            value = value * 85 + 84
        chunk = value.to_bytes(4, "big")
        out += chunk[:4 - pad] if pad else chunk
    return bytes(out)


def _runlength_decode(data):
    out = bytearray()
    i = 0
    n = len(data)
    while i < n:
        l = data[i]
        i += 1
        if l == 128:
            break
        if l < 128:
            out += data[i:i + l + 1]
            i += l + 1
        else:
            if i < n:
                out += bytes([data[i]]) * (257 - l)
                i += 1
    return bytes(out)


_RAW_PASS = {"DCTDecode", "DCT", "JPXDecode", "CCITTFaxDecode", "CCF", "JBIG2Decode"}


def _decode_filter(name, data, parms):
    if name in ("FlateDecode", "Fl"):
        try:
            out = zlib.decompress(data)
        except zlib.error:
            try:
                out = zlib.decompressobj().decompress(data)
            except zlib.error:
                try:
                    out = zlib.decompressobj(-15).decompress(data)
                except zlib.error as e:
                    raise PdfError("FlateDecode 失败：%s" % e)
        if parms:
            out = _apply_predictor(out, parms)
        return out
    if name in ("LZWDecode", "LZW"):
        early = int(parms.get("EarlyChange", 1)) if parms else 1
        out = _lzw_decode(data, early)
        if parms:
            out = _apply_predictor(out, parms)
        return out
    if name in ("ASCIIHexDecode", "AHx"):
        return _ascii_hex_decode(data)
    if name in ("ASCII85Decode", "A85"):
        return _ascii85_decode(data)
    if name in ("RunLengthDecode", "RL"):
        return _runlength_decode(data)
    if name in _RAW_PASS:
        return data  # 由图像解码环节处理
    if name in ("Crypt",):
        raise PdfError("PDF 已加密，无法读取")
    raise PdfError("不支持的过滤器：%s" % name)


# ==============================================================
# 4. PDF 文档读取
# ==============================================================
class PdfDocument(object):
    def __init__(self, data):
        self.data = data
        self.xref = {}
        self.trailer = {}
        self.cache = {}
        self._objstm_cache = {}
        self.encrypted = False
        self.used_scan_fallback = False
        self._load()

    # ---------- 载入 ----------
    def _load(self):
        try:
            self._load_xref()
        except Exception:
            self.xref = {}
            self.trailer = {}
        if not self.xref or not self._has_root():
            self._scan_objects()
        if "Encrypt" in self.trailer:
            self.encrypted = True
        elif b"/Encrypt" in self.data:
            self.encrypted = True

    def _has_root(self):
        return isinstance(self.trailer.get("Root"), PdfRef)

    def _load_xref(self):
        idx = self.data.rfind(b"startxref")
        if idx < 0:
            raise PdfError("没有 startxref")
        m = _NUM_RE.search(self.data, idx + 9)
        if not m:
            raise PdfError("startxref 没有数字")
        offset = int(m.group())
        seen = set()
        while offset is not None and 0 <= offset < len(self.data) and offset not in seen:
            seen.add(offset)
            trailer = self._read_xref_section(offset)
            if trailer is None:
                break
            if not self.trailer:
                self.trailer = dict(trailer)
            else:
                for k, v in trailer.items():
                    self.trailer.setdefault(k, v)
            hybrid = trailer.get("XRefStm")
            if isinstance(hybrid, (int, float)) and 0 <= int(hybrid) < len(self.data):
                try:
                    self._read_xref_section(int(hybrid))
                except Exception:
                    pass
            prev = trailer.get("Prev")
            if isinstance(prev, PdfRef):
                try:
                    prev = self.get(prev)
                except Exception:
                    prev = None
            offset = int(prev) if isinstance(prev, (int, float)) else None

    def _read_xref_section(self, pos):
        p = _Parser(self.data, pos, self)
        p.skip_ws()
        if self.data[p.pos:p.pos + 4] == b"xref":
            p.pos += 4
            while True:
                p.skip_ws()
                if self.data[p.pos:p.pos + 7] == b"trailer":
                    p.pos += 7
                    trailer = p.parse()
                    return trailer if isinstance(trailer, dict) else {}
                try:
                    first = p.parse()
                    count = p.parse()
                except Exception:
                    raise PdfError("xref 表损坏")
                if not isinstance(first, (int, float)) or not isinstance(count, (int, float)):
                    raise PdfError("xref 子段损坏")
                for k in range(int(count)):
                    p.skip_ws()
                    m = _XREF_ENTRY_RE.match(self.data, p.pos)
                    if not m:
                        raise PdfError("xref 条目损坏")
                    p.pos = m.end()
                    if m.group(3) == b"n":
                        self.xref.setdefault(int(m.group(1)), ("n", int(m.group(2)), 0))
        # xref 流：先跳过 "N G obj" 头
        m = _OBJ_RE.match(self.data, p.pos)
        if m:
            p.pos = m.end()
        obj = p.parse()
        if not isinstance(obj, PdfStream):
            raise PdfError("未知的 xref 结构")
        if str(obj.dict.get("Type", "")) != "XRef":
            raise PdfError("不是 XRef 流")
        self._parse_xref_stream(obj)
        return obj.dict

    def _parse_xref_stream(self, stream):
        d = stream.dict
        try:
            w = [int(self.get(x)) for x in self.get(d.get("W", []))]
            index = self.get(d.get("Index"))
            if index is None:
                index = [0, int(self.get(d.get("Size", 0)) or 0)]
            else:
                index = [int(self.get(x)) for x in index]
        except Exception as e:
            raise PdfError("XRef 流字典损坏：%s" % e)
        data = stream.data
        rowlen = sum(w)
        if rowlen <= 0:
            return
        pos = 0
        for i in range(0, len(index) - 1, 2):
            first = index[i]
            count = index[i + 1]
            for k in range(count):
                if pos + rowlen > len(data):
                    return
                fields = []
                for width in w:
                    if width == 0:
                        fields.append(None)
                    else:
                        fields.append(int.from_bytes(data[pos:pos + width], "big"))
                        pos += width
                ftype = 1 if fields[0] is None else fields[0]
                if ftype == 1:
                    self.xref.setdefault(first + k, ("n", fields[1] or 0, fields[2] or 0))
                elif ftype == 2:
                    self.xref.setdefault(first + k, ("c", fields[1] or 0, fields[2] or 0))

    def _scan_objects(self):
        """xref 不可用时的兜底：直接扫描所有 "N G obj"。"""
        self.used_scan_fallback = True
        for m in _OBJ_RE.finditer(self.data):
            self.xref[int(m.group(1))] = ("n", m.start(), int(m.group(2)))
        if not self.trailer:
            i = self.data.rfind(b"trailer")
            if i >= 0:
                try:
                    t = _Parser(self.data, i + 7, self).parse()
                    if isinstance(t, dict):
                        self.trailer = t
                except Exception:
                    pass
        if not self._has_root():
            for num in sorted(self.xref):
                try:
                    obj = self._get_object(num)
                except Exception:
                    continue
                if isinstance(obj, dict) and str(obj.get("Type", "")) == "Catalog":
                    self.trailer["Root"] = PdfRef(num)
                    break

    # ---------- 对象访问 ----------
    def get(self, obj):
        depth = 0
        while isinstance(obj, PdfRef):
            obj = self._get_object(obj.num, obj.gen)
            depth += 1
            if depth > 64:
                raise PdfError("引用循环")
        return obj

    def _get_object(self, num, gen=0):
        if num in self.cache:
            return self.cache[num]
        entry = self.xref.get(num)
        if entry is None:
            self._load_all_objstm()
            if num in self.cache:
                return self.cache[num]
            obj = self._find_object_by_scan(num)
            if obj is None:
                raise PdfError("找不到对象 %d" % num)
            self.cache[num] = obj
            return obj
        if entry[0] == "c":
            self._load_objstm(entry[1])
            if num in self.cache:
                return self.cache[num]
            raise PdfError("对象流 %d 中找不到对象 %d" % (entry[1], num))
        _, offset, _gen = entry
        obj = self._parse_object_at(num, offset)
        self.cache[num] = obj
        return obj

    def _parse_object_at(self, num, offset):
        if not (0 <= offset < len(self.data)):
            obj = self._find_object_by_scan(num)
            if obj is not None:
                return obj
            raise PdfError("对象 %d 偏移越界" % num)
        m = _OBJ_RE.match(self.data, offset)
        if not m or int(m.group(1)) != num:
            m2 = _OBJ_RE.match(self.data, max(0, offset - 2))
            if m2 and int(m2.group(1)) == num:
                m = m2
            else:
                obj = self._find_object_by_scan(num)
                if obj is not None:
                    return obj
                raise PdfError("对象 %d 的头部不匹配" % num)
        p = _Parser(self.data, m.end(), self)
        try:
            return p.parse()
        except Exception as e:
            obj = self._find_object_by_scan(num)
            if obj is not None:
                return obj
            raise PdfError("对象 %d 解析失败：%s" % (num, e))

    def _find_object_by_scan(self, num):
        pat = re.compile(rb"(?<![0-9])%d\s+\d{1,5}\s+obj\b" % num)
        for m in pat.finditer(self.data):
            try:
                p = _Parser(self.data, m.end(), self)
                return p.parse()
            except Exception:
                continue
        return None

    def _load_objstm(self, num):
        if num in self._objstm_cache:
            return
        self._objstm_cache[num] = {}
        try:
            stm = self._get_object(num)
            if not isinstance(stm, PdfStream):
                return
            data = stm.data
            n = int(self.get(stm.dict.get("N", 0)) or 0)
            first = int(self.get(stm.dict.get("First", 0)) or 0)
            nums = data[:first].split()
            table = []
            for k in range(n):
                try:
                    table.append((int(nums[2 * k]), int(nums[2 * k + 1])))
                except Exception:
                    break
            objs = {}
            for onum, off in table:
                try:
                    objs[onum] = _Parser(data, first + off, self).parse()
                except Exception:
                    pass
            self._objstm_cache[num] = objs
            for k, v in objs.items():
                self.cache.setdefault(k, v)
        except Exception:
            pass

    def _load_all_objstm(self):
        for num, entry in list(self.xref.items()):
            if entry[0] == "c":
                self._load_objstm(entry[1])

    # ---------- 流解码 ----------
    def stream_data(self, stream):
        d = stream.dict
        filters = self.get(d.get("Filter") if "Filter" in d else d.get("F"))
        if filters is None:
            return stream.raw
        if not isinstance(filters, list):
            filters = [filters]
        parms = self.get(d.get("DecodeParms", d.get("DP")))
        if not isinstance(parms, list):
            parms = [parms] * len(filters)
        data = stream.raw
        for i, f in enumerate(filters):
            name = str(self.get(f))
            pm = None
            if i < len(parms) and parms[i] is not None:
                pm = self.get(parms[i])
            if not isinstance(pm, dict):
                pm = None
            if name in ("FlateDecode", "LZWDecode", "Fl", "LZW") and pm is None:
                pm = d if "Predictor" in d else None
            data = _decode_filter(name, data, pm)
        return data

    # ---------- 结构 ----------
    def catalog(self):
        return self.get(self.trailer.get("Root")) if self._has_root() else None

    def info(self):
        ref = self.trailer.get("Info")
        if ref is None:
            return None
        try:
            obj = self.get(ref)
            return obj if isinstance(obj, dict) else None
        except Exception:
            return None

    def pages(self):
        root = self.catalog()
        pages_obj = None
        if isinstance(root, dict):
            try:
                pages_obj = self.get(root.get("Pages"))
            except Exception:
                pages_obj = None
        out = []
        self._walk_pages(pages_obj, {}, out, 0)
        return out

    def _walk_pages(self, node, inherited, out, depth):
        if depth > 64 or len(out) > 5000:
            return
        if not isinstance(node, dict):
            return
        if str(node.get("Type", "")) == "Page" or ("Kids" not in node and "Contents" in node):
            page = dict(node)
            for k, v in inherited.items():
                page.setdefault(k, v)
            out.append(page)
            return
        local = dict(inherited)
        for key in ("Resources", "MediaBox", "CropBox", "Rotate"):
            if key in node:
                local[key] = node[key]
        kids = node.get("Kids")
        if isinstance(kids, list):
            for kid in kids:
                try:
                    self._walk_pages(self.get(kid), local, out, depth + 1)
                except Exception:
                    continue

    def page_size_pt(self, page):
        box = page.get("MediaBox")
        try:
            box = [float(self.get(x)) for x in self.get(box)]
            return (abs(box[2] - box[0]), abs(box[3] - box[1]))
        except Exception:
            return (A4_W_PT, A4_H_PT)


def load_pdf(path):
    with open(path, "rb") as fh:
        return PdfDocument(fh.read())


# ==============================================================
# 5. 图像对象 → PIL 图像
# ==============================================================
def _filter_names(doc, d):
    f = doc.get(d.get("Filter") if "Filter" in d else d.get("F"))
    if f is None:
        return []
    if not isinstance(f, list):
        f = [f]
    return [str(doc.get(x)) for x in f]


def _color_space(doc, cs):
    """返回 (分量数, PIL 模式, 调色板字节) —— 未知返回 (None, None, None)。"""
    cs = doc.get(cs)
    if isinstance(cs, list) and cs:
        head = str(doc.get(cs[0]))
        if head in ("ICCBased", "ICCBased"):
            try:
                stm = doc.get(cs[1])
                n = int(doc.get(stm.dict.get("N", 3)))
            except Exception:
                n = 3
            return _mode_by_ncomp(n)
        if head in ("Indexed", "I"):
            try:
                base = doc.get(cs[1])
                hival = int(doc.get(cs[2]))
                lookup = doc.get(cs[3])
                if isinstance(lookup, PdfStream):
                    lookup = lookup.data
                if isinstance(lookup, PdfName):
                    lookup = str(lookup).encode("latin-1")
                if not isinstance(lookup, (bytes, bytearray)):
                    lookup = bytes(lookup)
            except Exception:
                return (1, "P", None)
            bn, bmode, _ = _color_space(doc, base)
            if bn is None:
                return (1, "P", None)
            palette = bytearray()
            stride = bn
            for i in range(hival + 1):
                chunk = lookup[i * stride:(i + 1) * stride]
                if len(chunk) < stride:
                    chunk = chunk + b"\x00" * (stride - len(chunk))
                if stride == 1:
                    palette += bytes([chunk[0]]) * 3
                elif stride == 3:
                    palette += chunk
                else:  # CMYK → RGB（近似）
                    c, m, y, k = [v / 255.0 for v in chunk[:4]]
                    palette += bytes([
                        int(255 * (1 - min(1.0, c + k))),
                        int(255 * (1 - min(1.0, m + k))),
                        int(255 * (1 - min(1.0, y + k))),
                    ])
            while len(palette) < 768:
                palette += b"\x00"
            return (1, "P", bytes(palette[:768]))
        if head == "CalRGB":
            return (3, "RGB", None)
        if head == "CalGray":
            return (1, "L", None)
        if head in ("DeviceN", "Separation"):
            return (1, "L", None)
        if head == "DeviceRGB":
            return (3, "RGB", None)
        if head == "DeviceGray":
            return (1, "L", None)
        if head == "DeviceCMYK":
            return (4, "CMYK", None)
        return (None, None, None)
    name = str(cs) if cs is not None else ""
    return {
        "DeviceRGB": (3, "RGB", None),
        "DeviceGray": (1, "L", None),
        "G": (1, "L", None),
        "DeviceCMYK": (4, "CMYK", None),
        "RGB": (3, "RGB", None),
    }.get(name, (None, None, None))


def _mode_by_ncomp(n):
    return {1: (1, "L", None), 3: (3, "RGB", None), 4: (4, "CMYK", None)}.get(n, (None, None, None))


def _expand_bits(data, count, bpc):
    """把 bpc=1/2/4 的紧排样本展开成每样本一字节（numpy 加速）。"""
    if _np is not None:
        arr = _np.frombuffer(data, dtype=_np.uint8)
        bits = _np.unpackbits(arr)
        if bpc == 1:
            samples = bits[:count]
        else:
            per = 8 // bpc
            usable = (len(bits) // 8) * 8
            bits = bits[:usable].reshape(-1, per)
            shifts = _np.arange(per - 1, -1, -1) * bpc
            samples = ((bits.astype(_np.uint16) >> shifts) & ((1 << bpc) - 1)).reshape(-1)[:count]
        maxv = (1 << bpc) - 1
        if bpc != 1:
            samples = (samples.astype(_np.uint16) * 255 // maxv).astype(_np.uint8)
        else:
            samples = (samples * 255).astype(_np.uint8)
        return samples.tobytes()
    out = bytearray()
    maxv = (1 << bpc) - 1
    total = len(data) * 8 // bpc
    for i in range(min(count, total)):
        bit = i * bpc
        byte_i = bit >> 3
        shift = 8 - bpc - (bit & 7)
        val = (data[byte_i] >> shift) & maxv
        if bpc != 1:
            val = val * 255 // maxv
        else:
            val = val * 255
        out.append(val)
    while len(out) < count:
        out.append(0)
    return bytes(out)


def _apply_decode(data, decode, ncomp, bpc):
    """处理 /Decode（最常见的是 [1 0] 反色）。"""
    if not decode:
        return data
    try:
        dec = [float(x) for x in decode]
    except Exception:
        return data
    maxv = (1 << bpc) - 1
    inverted = all(dec[2 * i] == maxv and dec[2 * i + 1] == 0 for i in range(min(ncomp, len(dec) // 2)))
    if not inverted:
        return data
    if _np is not None:
        arr = _np.frombuffer(data, dtype=_np.uint8)
        return (255 - arr).astype(_np.uint8).tobytes()
    return bytes(255 - b for b in data)


def _build_raw_image(doc, d, data, w, h):
    colorspace = d.get("ColorSpace", d.get("CS"))
    bpc = int(doc.get(d.get("BitsPerComponent", 8)) or 8)
    is_mask = bool(doc.get(d.get("ImageMask", False)))
    ncomp, mode, palette = (1, "L", None) if is_mask else _color_space(doc, colorspace)
    if ncomp is None or mode is None:
        raise PdfError("不支持的色彩空间：%r" % (colorspace,))
    count = w * h * ncomp
    if bpc == 8:
        need = count
        if len(data) < need:
            data = data + b"\x00" * (need - len(data))
        data = _apply_decode(data[:need], doc.get(d.get("Decode")), ncomp, bpc)
        if mode == "P":
            img = Image.frombytes("P", (w, h), data[:w * h])
            if palette:
                img.putpalette(palette)
            return img.convert("RGB")
        img = Image.frombytes(mode, (w, h), data)
        if is_mask:
            img = img.point(lambda v: 255 - v)  # 掩膜：1 = 上色
        return img
    if bpc in (1, 2, 4):
        expanded = _expand_bits(data, count, bpc)
        if is_mask:
            # 掩膜语义：样本 1 = 绘制（黑）
            if _np is not None:
                arr = _np.frombuffer(expanded, dtype=_np.uint8)
                expanded = (255 - arr).astype(_np.uint8).tobytes()
            else:
                expanded = bytes(255 - v for v in expanded)
        if mode == "P":
            img = Image.frombytes("P", (w, h), expanded[:w * h])
            if palette:
                img.putpalette(palette)
            return img.convert("RGB")
        return Image.frombytes(mode, (w, h), expanded)
    if bpc == 16:
        # 取高字节
        return _build_raw_image(doc, dict(d, BitsPerComponent=8), data[0::2], w, h)
    raise PdfError("不支持的位深：%d" % bpc)


def _ccitt_to_image(doc, d, data, w, h):
    """把 CCITTFaxDecode 数据包一层 TIFF 头交给 Pillow 解码。"""
    parms = doc.get(d.get("DecodeParms")) or {}
    if not isinstance(parms, dict):
        parms = {}
    k = int(doc.get(parms.get("K", 0)) or 0)
    black1 = bool(doc.get(parms.get("BlackIs1", False)))
    if k < 0:
        compression = 4  # Group4
    elif k == 0:
        compression = 3  # Group3
    else:
        compression = 3
    photometric = 0 if black1 else 1
    tags = [
        (256, 3, 1, w), (257, 3, 1, h), (258, 3, 1, 1), (259, 3, 1, compression),
        (262, 3, 1, photometric), (273, 4, 1, 8), (277, 3, 1, 1),
        (278, 3, 1, h), (279, 4, 1, len(data)), (266, 3, 1, 1),
    ]
    entries = len(tags)
    ifd_offset = 8
    data_offset = ifd_offset + 2 + entries * 12 + 4
    out = bytearray()
    out += b"II*\x00" + struct.pack("<I", ifd_offset)
    out += struct.pack("<H", entries)
    for tag, typ, cnt, val in tags:
        out += struct.pack("<HHI", tag, typ, cnt) + struct.pack("<I", val)
    out += struct.pack("<I", 0)
    out += data
    try:
        img = Image.open(io.BytesIO(bytes(out)))
        img.load()
        return img.convert("L")
    except Exception as e:
        raise PdfError("CCITT 图像解码失败：%s" % e)


def image_from_stream(doc, stream):
    """把一个 /Subtype /Image 流解码成 PIL 图像（失败返回 None）。"""
    d = stream.dict
    try:
        w = int(doc.get(d.get("Width", d.get("W", 0))) or 0)
        h = int(doc.get(d.get("Height", d.get("H", 0))) or 0)
        if w <= 0 or h <= 0 or w * h > 4_000_000_000:
            return None
        filters = _filter_names(doc, d)
        data = doc.stream_data(stream)
        img = None
        if "DCTDecode" in filters or "JPXDecode" in filters:
            img = Image.open(io.BytesIO(data))
            img.load()
            if img.mode not in ("L", "RGB", "CMYK", "P", "1"):
                img = img.convert("RGB")
        elif "CCITTFaxDecode" in filters:
            img = _ccitt_to_image(doc, d, data, w, h)
        elif "JBIG2Decode" in filters:
            return None
        else:
            img = _build_raw_image(doc, d, data, w, h)

        # 透明通道
        smask_ref = d.get("SMask")
        if img is not None and smask_ref is not None:
            try:
                smask = doc.get(smask_ref)
                if isinstance(smask, PdfStream):
                    mask = image_from_stream(doc, smask)
                    if mask is not None:
                        if mask.size != img.size:
                            mask = mask.resize(img.size, Image.NEAREST)
                        base = img.convert("RGBA") if img.mode != "RGBA" else img
                        base.putalpha(mask.convert("L"))
                        bg = Image.new("RGB", base.size, "white")
                        bg.paste(base, mask=base.getchannel("A"))
                        img = bg
            except Exception:
                pass
        if img is not None and img.mode in ("CMYK", "P", "I;16", "1"):
            img = img.convert("RGB")
        return img
    except Exception:
        return None


def _collect_images(doc, resources, out, depth=0, seen=None):
    if depth > 4 or not isinstance(resources, dict):
        return out
    xobjects = doc.get(resources.get("XObject"))
    if not isinstance(xobjects, dict):
        return out
    for _name, ref in xobjects.items():
        try:
            obj = doc.get(ref)
        except Exception:
            continue
        if not isinstance(obj, PdfStream):
            continue
        subtype = str(obj.dict.get("Subtype", ""))
        if subtype == "Image":
            img = image_from_stream(doc, obj)
            if img is not None:
                out.append(img)
        elif subtype == "Form":
            sub = obj.dict.get("Resources")
            if sub is not None:
                try:
                    _collect_images(doc, doc.get(sub), out, depth + 1)
                except Exception:
                    pass
    return out


def page_images(doc, page):
    """返回该页里的所有位图（按资源顺序）。"""
    return _collect_images(doc, doc.get(page.get("Resources")), [])


def largest_page_image(doc, page):
    imgs = page_images(doc, page)
    if not imgs:
        return None
    return max(imgs, key=lambda im: im.size[0] * im.size[1])


# ==============================================================
# 6. 编辑状态（写入 PDF / 从 PDF 读回）
# ==============================================================
def make_state(images, rows, cols, margin_mm, padding_mm, dpi=None, extra=None):
    """images 为 [[path, w, h, rotation], ...]"""
    state = {
        "app": "A4PhotoLayout",
        "v": STATE_VERSION,
        "grid": [int(rows), int(cols)],
        "margin_mm": float(margin_mm),
        "padding_mm": float(padding_mm),
    }
    if dpi:
        state["dpi"] = int(dpi)
    if extra:
        state.update(extra)
    state["images"] = [{"p": str(item[0]), "r": int(item[3]) % 360} for item in images]
    return state


def state_to_bytes(state):
    raw = json.dumps(state, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return zlib.compress(raw, 9)


def bytes_to_state(blob):
    for candidate in (blob,):
        try:
            return json.loads(zlib.decompress(candidate).decode("utf-8"))
        except Exception:
            pass
    try:
        return json.loads(blob.decode("utf-8", "replace"))
    except Exception:
        return None


def validate_state(state):
    """检查状态结构是否可用；返回规范化的 images 列表或 None。"""
    if not isinstance(state, dict):
        return None
    imgs = state.get("images")
    if not isinstance(imgs, list):
        return None
    out = []
    for item in imgs:
        if isinstance(item, dict) and isinstance(item.get("p"), str):
            try:
                rot = int(item.get("r", 0)) % 360
            except Exception:
                rot = 0
            out.append([item["p"], None, None, rot])
        elif isinstance(item, str):
            out.append([item, None, None, 0])
    if not out:
        return None
    return {
        "images": out,
        "grid": state.get("grid") if isinstance(state.get("grid"), list) else None,
        "margin_mm": state.get("margin_mm"),
        "padding_mm": state.get("padding_mm"),
        "dpi": state.get("dpi"),
        "version": state.get("v"),
    }


def read_state_from_doc(doc):
    """优先从 Catalog/Info 的 /A4PLState 读取，再退化为全文件扫描。"""
    for container in (doc.catalog(), doc.info()):
        if not isinstance(container, dict):
            continue
        ref = container.get("A4PLState")
        if ref is None:
            continue
        try:
            obj = doc.get(ref)
        except Exception:
            continue
        if isinstance(obj, PdfStream):
            state = bytes_to_state(obj.data)
            if state:
                return state
    return None


def scan_state_bytes(data):
    """不依赖解析器的暴力扫描：适用于结构轻微损坏的 PDF。"""
    for m in re.finditer(rb"/Type\s*/" + STATE_TYPE.encode("ascii") + rb"\b", data):
        i = data.find(b"stream", m.end())
        if i < 0 or i - m.end() > 2000:
            continue
        j = i + 6
        if data[j:j + 2] == b"\r\n":
            j += 2
        elif data[j:j + 1] in (b"\n", b"\r"):
            j += 1
        k = data.find(b"endstream", j)
        if k < 0:
            continue
        state = bytes_to_state(data[j:k])
        if state:
            return state
    return None


def read_edit_state_bytes(data):
    """bytes 版本，避免同一个文件被读两遍。"""
    state = scan_state_bytes(data)
    if state:
        return state
    try:
        doc = PdfDocument(data)
    except Exception:
        return None
    return read_state_from_doc(doc)


def read_edit_state(path):
    """读取 PDF 里的编辑状态。"""
    with open(path, "rb") as fh:
        return read_edit_state_bytes(fh.read())


# ==============================================================
# 7. PDF 写入（逐页流式，内存占用恒定）
# ==============================================================
def _pdf_text(text):
    """文本字符串一律用 UTF-16BE 十六进制串，避免编码/转义问题。"""
    raw = str(text).encode("utf-16-be")
    return b"<FEFF" + raw.hex().upper().encode("ascii") + b">"


def _pdf_date(t=None):
    """PDF 日期必须是字符串对象（pypdf 等严格解析器会检查）。"""
    tm = time.localtime(t) if t else time.localtime()
    return b"(D:%04d%02d%02d%02d%02d%02d)" % tm[:6]


def write_pdf(path, page_count, render_page, info=None, state_bytes=None,
              page_w_pt=A4_W_PT, page_h_pt=A4_H_PT):
    """
    流式写出 PDF。

    render_page(index) -> (jpeg_bytes, pixel_width, pixel_height)
        只在该页即将写入时调用，因此同一时刻内存里只有一页。
    state_bytes: zlib 压缩后的编辑状态（会写成独立流对象，阅读器忽略它）。
    """
    info = dict(info or {})
    has_state = state_bytes is not None
    first_page_obj = 5 if has_state else 4
    page_bases = [first_page_obj + 3 * i for i in range(page_count)]
    max_obj = (first_page_obj + 3 * page_count - 1) if page_count else (4 if has_state else 3)

    with open(path, "wb") as fh:
        offsets = {}

        def begin(num):
            offsets[num] = fh.tell()
            fh.write(("%d 0 obj\n" % num).encode("ascii"))

        def end():
            fh.write(b"\nendobj\n")

        fh.write(b"%PDF-1.7\n")
        fh.write(b"%\xe2\xe3\xcf\xd3\n")

        # 1 目录
        begin(1)
        fh.write(b"<< /Type /Catalog /Pages 2 0 R")
        if has_state:
            fh.write(b" /A4PLState 4 0 R")
        fh.write(b" >>")
        end()

        # 2 页面树
        begin(2)
        kids = b" ".join(b"%d 0 R" % n for n in page_bases)
        fh.write(b"<< /Type /Pages /Count %d /Kids [%s] >>" % (page_count, kids))
        end()

        # 3 文档信息
        begin(3)
        fh.write(b"<<")
        if info.get("title"):
            fh.write(b" /Title " + _pdf_text(info["title"]))
        if info.get("author"):
            fh.write(b" /Author " + _pdf_text(info["author"]))
        if info.get("subject"):
            fh.write(b" /Subject " + _pdf_text(info["subject"]))
        fh.write(b" /Creator " + _pdf_text(info.get("creator", "A4 Photo Layout")))
        fh.write(b" /Producer " + _pdf_text(info.get("producer", "A4 Photo Layout")))
        if info.get("keywords"):
            fh.write(b" /Keywords " + _pdf_text(info["keywords"]))
        fh.write(b" /CreationDate " + _pdf_date())
        fh.write(b" /ModDate " + _pdf_date())
        if has_state:
            fh.write(b" /A4PLState 4 0 R")
        fh.write(b" >>")
        end()

        # 4 编辑状态流
        if has_state:
            begin(4)
            fh.write(b"<< /Type /%s /Version %d /Filter /FlateDecode /Length %d >>\nstream\n"
                     % (STATE_TYPE.encode("ascii"), STATE_VERSION, len(state_bytes)))
            fh.write(state_bytes)
            fh.write(b"\nendstream")
            end()

        # 各页
        for i in range(page_count):
            jpeg, px_w, px_h = render_page(i)
            page_num, content_num, image_num = page_bases[i], page_bases[i] + 1, page_bases[i] + 2

            begin(page_num)
            fh.write(
                b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %.4f %.4f] "
                b"/Resources << /XObject << /Im0 %d 0 R >> /ProcSet [/PDF /ImageC] >> "
                b"/Contents %d 0 R >>"
                % (page_w_pt, page_h_pt, image_num, content_num)
            )
            end()

            begin(content_num)
            body = b"q %.4f 0 0 %.4f 0 0 cm /Im0 Do Q\n" % (page_w_pt, page_h_pt)
            fh.write(b"<< /Length %d >>\nstream\n" % len(body))
            fh.write(body)
            fh.write(b"endstream")
            end()

            begin(image_num)
            fh.write(
                b"<< /Type /XObject /Subtype /Image /Width %d /Height %d "
                b"/ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length %d >>\nstream\n"
                % (px_w, px_h, len(jpeg))
            )
            fh.write(jpeg)
            fh.write(b"\nendstream")
            end()

        # 交叉引用表
        xref_offset = fh.tell()
        size = max_obj + 1
        fh.write(b"xref\n0 %d\n" % size)
        fh.write(b"0000000000 65535 f \r\n")
        for num in range(1, size):
            off = offsets.get(num)
            if off is None:
                fh.write(b"0000000000 65535 f \r\n")
            else:
                fh.write(("%010d 00000 n \r\n" % off).encode("ascii"))
        fh.write(b"trailer\n<< /Size %d /Root 1 0 R /Info 3 0 R >>\n" % size)
        fh.write(b"startxref\n%d\n%%%%EOF\n" % xref_offset)
    return path


# ==============================================================
# 默认排版参数
# ==============================================================
DEFAULT_ROWS = 3
DEFAULT_COLS = 3
DEFAULT_MARGIN_MM = 10.0
DEFAULT_PADDING_MM = 1.5

ROWS = DEFAULT_ROWS
COLS = DEFAULT_COLS
MAX_PER_PAGE = ROWS * COLS
MARGIN_MM = DEFAULT_MARGIN_MM
PADDING_MM = DEFAULT_PADDING_MM

PAGE_W = 460
PAGE_H = int(PAGE_W * A4_H_MM / A4_W_MM)
PAGE_GAP = 20
LONG_PRESS_TIME = 300

DPI_CHOICES = ["150", "300", "450", "600"]
LAYOUT_CHOICES = ["1 × 1", "2 × 2", "2 × 3", "3 × 2", "3 × 3",
                  "3 × 4", "4 × 3", "4 × 4"]
QUALITY_CHOICES = ["85", "90", "95"]
DEFAULT_DPI = 300
DEFAULT_QUALITY = 90
PRINT_MAX_DPI = 300
"""
打印时渲染页面的最高 DPI。

实测（Windows 自带的 Microsoft Print to PDF 驱动）：
    150 DPI 页面(1240×1754)  -> 正常
    300 DPI 页面(2480×3508)  -> 正常
    400 DPI 页面(3307×4677)  -> EndPage 失败(error -1)
    600 DPI 页面(4961×7016)  -> EndPage 失败(error -1)
也就是说这类驱动对单页位图有大小限制（约 870 万像素）。照片打印用
300 DPI 已经足够（V2 的默认值也是 300），再往上只会让文件更大、
更容易失败；打印机自己的驱动会按它的真实分辨率放大，画质不受影响。
"""

# GDI GetDeviceCaps 的索引值（wingdi.h）。
# 注意：win32print 并不导出这些常量（win32print.PHYSICALWIDTH 会 AttributeError，
# V2 的打印代码正是因此每次都悄悄走进 except 分支），所以这里直接写常量值。
CAP_HORZRES = 8            # 可打印区域宽度（设备单位）
CAP_VERTRES = 10           # 可打印区域高度（设备单位）
CAP_LOGPIXELSX = 88        # 水平 DPI
CAP_LOGPIXELSY = 90        # 垂直 DPI
CAP_PHYSICALWIDTH = 110    # 整张纸宽度（含不可打印边距）
CAP_PHYSICALHEIGHT = 111
CAP_PHYSICALOFFSETX = 112  # 不可打印边距偏移
CAP_PHYSICALOFFSETY = 113

IMAGE_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".bmp",
    ".gif", ".tif", ".tiff", ".webp"
}
PDF_EXTENSIONS = {".pdf"}


class _Cancelled(Exception):
    """用户在进度窗口里点了取消。"""


# ==============================================================
# 图片工具
# ==============================================================
def image_size_after_exif(path):
    """
    返回考虑 EXIF 方向之后的 (宽, 高)。

    V2 的 bug：用 Image.open().size 记录宽高，但渲染时又调用
    exif_transpose 把图片转过来了，两者不一致，导致竖拍手机照片
    在版面里被拉伸。这里统一按"转过之后"的尺寸记录。
    """
    with Image.open(path) as im:
        w, h = im.size
        try:
            orientation = im.getexif().get(274)
            if orientation in (5, 6, 7, 8):
                w, h = h, w
        except Exception:
            pass
    return int(w), int(h)


def load_photo_rgb(path, rotation=0):
    """
    读出照片，修正 EXIF 方向，再按"顺时针 rotation 度"旋转，返回 RGB 图。
    PIL 的 rotate 正角度是逆时针，所以顺时针要传 -rotation。
    """
    with Image.open(path) as src:
        img = src.copy()
    try:
        img = ImageOps.exif_transpose(img)
    except Exception:
        pass
    rotation = int(rotation) % 360
    if rotation:
        img = img.rotate(-rotation, expand=True)
    if img.mode == "RGBA":
        bg = Image.new("RGB", img.size, "white")
        bg.paste(img, mask=img.getchannel("A"))
        img = bg
    elif img.mode != "RGB":
        img = img.convert("RGB")
    return img


def fit_image(img, box_w, box_h):
    """按比例缩放到 box 内（可放大也可缩小），保证预览和 PDF 完全一致。"""
    box_w = max(1, float(box_w))
    box_h = max(1, float(box_h))
    factor = min(box_w / img.width, box_h / img.height)
    nw = max(1, int(round(img.width * factor)))
    nh = max(1, int(round(img.height * factor)))
    if (nw, nh) == img.size:
        return img
    return img.resize((nw, nh), Image.LANCZOS)


def render_page_raster(images, page_idx, dpi, rows, cols, margin_mm, padding_mm):
    """
    把某一页渲染成整页位图（A4，按 dpi）。

    只在这一页需要写入 PDF 时才调用，写完就释放 —— 这样即使导出
    600 DPI、几十页，内存占用也只是一页的大小。
    """
    scale = dpi / 25.4
    page_w_px = max(1, int(round(A4_W_MM * scale)))
    page_h_px = max(1, int(round(A4_H_MM * scale)))
    page = Image.new("RGB", (page_w_px, page_h_px), "white")

    cell_w_mm = (A4_W_MM - 2 * margin_mm) / cols
    cell_h_mm = (A4_H_MM - 2 * margin_mm) / rows
    per_page = rows * cols

    start = page_idx * per_page
    end = min(start + per_page, len(images))

    for k in range(start, end):
        item = images[k]
        path = item[0]
        rotation = item[3] if len(item) > 3 else 0
        row, col = divmod(k - start, cols)

        avail_w = (cell_w_mm - 2 * padding_mm) * scale
        avail_h = (cell_h_mm - 2 * padding_mm) * scale
        cx = (margin_mm + col * cell_w_mm + cell_w_mm / 2.0) * scale
        cy = (margin_mm + row * cell_h_mm + cell_h_mm / 2.0) * scale

        try:
            photo = load_photo_rgb(path, rotation)
        except Exception:
            photo = None

        if photo is None:  # 文件丢失/损坏：画红框占位，不影响导出
            draw = ImageDraw.Draw(page)
            x0 = int(cx - avail_w / 2)
            y0 = int(cy - avail_h / 2)
            draw.rectangle([x0, y0, x0 + int(avail_w), y0 + int(avail_h)],
                           outline="red", width=max(3, dpi // 100))
            draw.text((x0 + 12, y0 + 12), "MISSING", fill="red")
            continue

        fitted = fit_image(photo, avail_w, avail_h)
        page.paste(fitted, (int(round(cx - fitted.width / 2.0)),
                            int(round(cy - fitted.height / 2.0))))
        if fitted is not photo:
            fitted.close()
        photo.close()

    return page


# ==============================================================
# 从 PDF 里恢复照片
# ==============================================================
CELL_TRIM_TOL = 246      # 高于这个灰度算"白"，用于裁掉格子里的空白
CELL_TRIM_MIN = 0.02     # 有效内容少于格子面积的 2% 视为空格子
CELL_TRIM_PAD = 2        # 裁完留 2 像素白边


def cell_rects(page_img_w, page_img_h, rows, cols, margin_mm, padding_mm):
    """
    按 A4 版式算出每个格子在位图里的位置。

    本工具导出的 PDF，一页就是一张整页位图，所以直接用 A4 尺寸换算。
    """
    sx = page_img_w / A4_W_MM
    sy = page_img_h / A4_H_MM
    cell_w = (A4_W_MM - 2 * margin_mm) / cols
    cell_h = (A4_H_MM - 2 * margin_mm) / rows
    boxes = []
    for r in range(rows):
        for c in range(cols):
            x0 = (margin_mm + c * cell_w) * sx
            y0 = (margin_mm + r * cell_h) * sy
            x1 = (margin_mm + (c + 1) * cell_w) * sx
            y1 = (margin_mm + (r + 1) * cell_h) * sy
            boxes.append((int(round(x0)), int(round(y0)), int(round(x1)), int(round(y1))))
    return boxes


def trim_white(img, tol=CELL_TRIM_TOL):
    """裁掉四周白边；整格都是白（空格子）返回 None。"""
    gray = img.convert("L")
    mask = gray.point(lambda v: 255 if v < tol else 0)
    bbox = mask.getbbox()
    gray.close()
    mask.close()
    if not bbox:
        return None
    x0, y0, x1, y1 = bbox
    if (x1 - x0) * (y1 - y0) < CELL_TRIM_MIN * img.width * img.height:
        return None
    box = (max(0, x0 - CELL_TRIM_PAD), max(0, y0 - CELL_TRIM_PAD),
           min(img.width, x1 + CELL_TRIM_PAD), min(img.height, y1 + CELL_TRIM_PAD))
    return img.crop(box) if box != (0, 0, img.width, img.height) else img


def crop_cell(page_img, cell_index, rows, cols, margin_mm, padding_mm):
    """从整页位图里抠出第 cell_index 个格子里的照片（空格子返回 None）。"""
    boxes = cell_rects(page_img.width, page_img.height, rows, cols, margin_mm, padding_mm)
    if not (0 <= cell_index < len(boxes)):
        return None
    x0, y0, x1, y1 = boxes[cell_index]
    if x1 - x0 < 4 or y1 - y0 < 4:
        return None
    cell = page_img.crop((x0, y0, x1, y1))
    trimmed = trim_white(cell)
    if trimmed is None:
        cell.close()
        return None
    if trimmed is not cell:
        cell.close()
    return trimmed


# --------------------------------------------------------------
# 把"别的软件生成的 PDF 页面"自己合成出来（不需要任何渲染库）
# --------------------------------------------------------------
_CONTENT_NUM_RE = re.compile(rb"[+-]?(?:\d+\.?\d*|\.\d+)")
_CONTENT_NAME_RE = re.compile(rb"/[^\s/\[\]<>()%]*")
_CONTENT_OP_RE = re.compile(rb"[A-Za-z*'\"]+")
CONTENT_STREAM_LIMIT = 8 * 1024 * 1024     # 内容流过大就不合成，避免卡死
COMPOSE_MAX_PLACEMENTS = 5000


def _content_tokens(data):
    """把页面内容流切成 (类型, 值)：num / name / string / other / op。"""
    i = 0
    n = len(data)
    while i < n:
        c = data[i:i + 1]
        if c in b" \t\r\n\x00\x0c":
            i += 1
            continue
        if c == b"%":
            j = data.find(b"\n", i)
            i = n if j < 0 else j + 1
            continue
        if c == b"/":
            m = _CONTENT_NAME_RE.match(data, i)
            yield ("name", m.group()[1:].decode("latin-1"))
            i = m.end()
            continue
        if c == b"(":
            depth = 1
            j = i + 1
            while j < n and depth:
                if data[j:j + 1] == b"\\":
                    j += 2
                    continue
                if data[j:j + 1] == b"(":
                    depth += 1
                elif data[j:j + 1] == b")":
                    depth -= 1
                j += 1
            yield ("string", data[i:j])
            i = j
            continue
        if c in b"[]<>":
            j = i + 1
            depth = 1
            while j < n and depth:
                if data[j:j + 1] == b"[":
                    depth += 1
                elif data[j:j + 1] == b"]":
                    depth -= 1
                j += 1
            yield ("other", data[i:j])
            i = j
            continue
        m = _CONTENT_NUM_RE.match(data, i)
        if m:
            t = m.group()
            yield ("num", float(t) if b"." in t else int(t))
            i = m.end()
            continue
        m = _CONTENT_OP_RE.match(data, i)
        if m:
            yield ("op", m.group().decode("latin-1"))
            i = m.end()
            continue
        i += 1


def _matrix_mul(m1, m2):
    a1, b1, c1, d1, e1, f1 = m1
    a2, b2, c2, d2, e2, f2 = m2
    return (a1 * a2 + b1 * c2, a1 * b2 + b1 * d2,
            c1 * a2 + d1 * c2, c1 * b2 + d1 * d2,
            e1 * a2 + f1 * c2 + e2, e1 * b2 + f1 * d2 + f2)


def page_content_streams(doc, page):
    streams = []
    cont = doc.get(page.get("Contents"))
    if isinstance(cont, PdfStream):
        streams.append(cont.data)
    elif isinstance(cont, list):
        for c in cont:
            o = doc.get(c)
            if isinstance(o, PdfStream):
                streams.append(o.data)
    return streams


def collect_page_placement(doc, page):
    """
    解析页面的 cm / Do，返回 [(图像, 单位方块→页面的矩阵), ...]。

    只处理位图（文字/矢量不参与），这对"图片型 PDF"（扫描件、水印相机
    照片表、截图导出）已经足够，而且完全不需要额外的渲染库。
    """
    resources = doc.get(page.get("Resources")) or {}
    xobjects = doc.get(resources.get("XObject")) or {}
    cache = {}
    placements = []
    ctm = (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
    stack = []
    operands = []
    total = 0
    for blob in page_content_streams(doc, page):
        total += len(blob)
        if total > CONTENT_STREAM_LIMIT:
            break
        for kind, value in _content_tokens(blob):
            if kind != "op":
                operands.append(value)
                continue
            if value == "q":
                stack.append(ctm)
            elif value == "Q":
                ctm = stack.pop() if stack else (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
            elif value == "cm" and len(operands) >= 6:
                try:
                    ctm = _matrix_mul(ctm, tuple(float(v) for v in operands[-6:]))
                except Exception:
                    pass
            elif value == "Do" and operands:
                name = operands[-1]
                if isinstance(name, str):
                    if name not in cache:
                        img = None
                        ref = xobjects.get(name)
                        if ref is not None:
                            obj = doc.get(ref)
                            if (isinstance(obj, PdfStream)
                                    and str(obj.dict.get("Subtype", "")) == "Image"):
                                img = image_from_stream(doc, obj)
                        cache[name] = img
                    img = cache[name]
                    if img is not None:
                        placements.append((img, ctm))
                        if len(placements) >= COMPOSE_MAX_PLACEMENTS:
                            return placements
            operands = []
    return placements


def page_native_dpi(page, placements):
    """按"位图像素数 ÷ 它在页面上的尺寸"估算页面真实分辨率。"""
    from statistics import median
    ratios = []
    for img, (a, b, c, d, e, f) in placements:
        box_w_pt = max(abs(a), abs(c))
        box_h_pt = max(abs(b), abs(d))
        if box_w_pt < 1 or box_h_pt < 1:
            continue
        ratios.append(img.width / box_w_pt * 72.0)
        ratios.append(img.height / box_h_pt * 72.0)
    if not ratios:
        return 150.0
    return max(36.0, min(1200.0, median(ratios)))


def render_page_composed(doc, page, dpi):
    """
    把页面里的位图按 cm 摆放关系合成成整页位图（相当于"扫描"这张页面）。

    返回 (位图, 摆放数量)；页面上没有可直接使用的位图时返回 (None, 0)。
    """
    w_pt, h_pt = doc.page_size_pt(page)
    if w_pt < 1 or h_pt < 1:
        return None, 0
    placements = collect_page_placement(doc, page)
    if not placements:
        return None, 0

    scale = dpi / 72.0
    page_img = Image.new("RGB", (max(1, int(round(w_pt * scale))),
                                 max(1, int(round(h_pt * scale)))), "white")
    for img, (a, b, c, d, e, f) in placements:
        xs = [e, e + a, e + c, e + a + c]
        ys = [f, f + b, f + d, f + b + d]
        x0 = min(xs) * scale
        x1 = max(xs) * scale
        y_top = (h_pt - max(ys)) * scale          # PDF 的 y 轴向上，位图 y 轴向下
        y_bot = (h_pt - min(ys)) * scale
        box = (int(round(x0)), int(round(y_top)), int(round(x1)), int(round(y_bot)))
        tw = max(1, box[2] - box[0])
        th = max(1, box[3] - box[1])

        piece = img
        if d < 0:                                  # 上下翻转
            piece = piece.transpose(Image.FLIP_TOP_BOTTOM)
        if a < 0:                                  # 左右翻转
            piece = piece.transpose(Image.FLIP_LEFT_RIGHT)
        if (piece.width, piece.height) != (tw, th):
            piece = piece.resize((tw, th), Image.LANCZOS)
        page_img.paste(piece, (box[0], box[1]))
        if piece is not img:
            piece.close()
    return page_img, len(placements)


def content_segments(profile, threshold=1, min_gap=4, min_len=8):
    """
    在一维"内容投影"里找内容段：返回 [(start, end), ...]。

    profile 是每个位置的"内容量"序列（0 表示全白）。
    """
    segments = []
    start = None
    gap = 0
    for i, v in enumerate(profile):
        if v > threshold:
            if start is None:
                start = i
            gap = 0
        elif start is not None:
            gap += 1
            if gap >= min_gap:
                end = i - gap + 1
                if end - start >= min_len:
                    segments.append((start, end))
                start = None
                gap = 0
    if start is not None:
        end = len(profile) - gap
        if end - start >= min_len:
            segments.append((start, end))
    return segments


def _content_profile(img, tol=CELL_TRIM_TOL):
    """把图像压成一维/二维的"是否有内容"分布（用 BOX 缩放，C 层实现，很快）。"""
    gray = img.convert("L")
    mask = gray.point(lambda v: 255 if v < tol else 0)
    small = mask.resize((1, mask.height), Image.BOX)
    row_profile = list(small.tobytes())
    small.close()
    wide = mask.resize((mask.width, 1), Image.BOX)
    col_profile = list(wide.tobytes())
    wide.close()
    gray.close()
    mask.close()
    return row_profile, col_profile


def split_page_by_gaps(page_img, min_gap_px=None, tol=CELL_TRIM_TOL):
    """
    按"整行/整列都是空白"把页面自动切成若干张照片。

    水印相机照片表、多张照片拼在一页的 PDF、扫描件都适用：
    先找横向空白把页面分成若干"行带"，再在每个行带里找纵向空白分成照片。
    返回 [(box, 图像), ...]（按从上到下、从左到右排序）。
    """
    if page_img.width < 16 or page_img.height < 16:
        return []
    if min_gap_px is None:
        min_gap_px = max(3, int(round(min(page_img.size) * 0.006)))
    min_len = max(24, min_gap_px * 3)

    row_profile, _ = _content_profile(page_img, tol)
    bands = content_segments(row_profile, threshold=1, min_gap=min_gap_px, min_len=min_len)

    out = []
    for y0, y1 in bands:
        band = page_img.crop((0, y0, page_img.width, y1))
        _, col_profile = _content_profile(band, tol)
        cols = content_segments(col_profile, threshold=1, min_gap=min_gap_px, min_len=min_len)
        if not cols:
            cols = [(0, page_img.width)]
        for x0, x1 in cols:
            if (x1 - x0) < min_len or (y1 - y0) < min_len:
                continue
            box = (x0, y0, x1, y1)
            out.append((box, page_img.crop(box)))
        band.close()
    return out


def looks_like_our_export(doc, pages):
    """
    粗略判断"这是不是本工具导出的 PDF"：A4 页面 + 每页只有一张铺满整页的位图。
    用来给导入方式选一个合理的默认值。
    """
    hits = 0
    checked = 0
    for page in pages[:5]:
        w_pt, h_pt = doc.page_size_pt(page)
        if w_pt < 10 or h_pt < 10:
            continue
        checked += 1
        if abs(w_pt - A4_W_PT) > 4 or abs(h_pt - A4_H_PT) > 4:
            continue
        imgs = page_images(doc, page)
        if len(imgs) != 1:
            continue
        iw, ih = imgs[0].size
        if iw < 100 or ih < 100:
            continue
        if abs((iw / float(ih)) - (w_pt / h_pt)) < 0.05:
            hits += 1
    return checked > 0 and hits >= max(1, (checked + 1) // 2)


def describe_pdf(path):
    """导入前先看一眼这个 PDF：几页、有没有编辑信息、缺几张原图。"""
    info = {
        "path": path,
        "name": os.path.basename(path),
        "pages": 0,
        "has_state": False,
        "state_images": 0,
        "missing": 0,
        "encrypted": False,
        "looks_like_export": False,
        "first_page_images": 0,
        "composable": False,
        "error": None,
    }
    try:
        with open(path, "rb") as fh:
            data = fh.read()
        state = validate_state(read_edit_state_bytes(data))
        if state:
            info["has_state"] = True
            info["state_images"] = len(state["images"])
            info["missing"] = sum(
                1 for it in state["images"]
                if not (it[0] and os.path.isfile(it[0]))
            )
        doc = PdfDocument(data)
        info["encrypted"] = doc.encrypted
        pages = doc.pages()
        info["pages"] = len(pages)
        info["looks_like_export"] = looks_like_our_export(doc, pages)
        if pages:
            try:
                info["first_page_images"] = len(page_images(doc, pages[0]))
            except Exception:
                info["first_page_images"] = 0
            try:
                info["composable"] = bool(collect_page_placement(doc, pages[0]))
            except Exception:
                info["composable"] = False
    except Exception as e:
        info["error"] = str(e)
    return info


def import_pdf_file(path, mode, rows, cols, margin_mm, padding_mm, temp_dir,
                    progress=None):
    """
    从一个 PDF 里取出可编辑的照片列表。

    返回 dict：
        images   [[path, w, h, rotation], ...]
        mode     实际使用的模式："state" / "grid" / "page"
        grid     编辑信息里带的排版参数 (rows, cols) 或 None
        margin_mm / padding_mm
        warnings [提示信息, ...]
    """
    result = {
        "images": [], "mode": mode, "grid": None,
        "margin_mm": None, "padding_mm": None, "warnings": [],
    }
    warnings = result["warnings"]

    with open(path, "rb") as fh:
        data = fh.read()

    state = validate_state(read_edit_state_bytes(data))

    # ---------------- 1) 有编辑信息：原样恢复 ----------------
    if state:
        grid = state.get("grid") or [rows, cols]
        try:
            s_rows, s_cols = int(grid[0]), int(grid[1])
        except Exception:
            s_rows, s_cols = rows, cols
        s_rows = max(1, min(10, s_rows))
        s_cols = max(1, min(10, s_cols))
        s_margin = state.get("margin_mm")
        s_padding = state.get("padding_mm")
        s_margin = float(margin_mm if s_margin is None else s_margin)
        s_padding = float(padding_mm if s_padding is None else s_padding)

        doc = None
        pages = None
        rasters = {}
        per_page = s_rows * s_cols
        total = len(state["images"])

        for i, item in enumerate(state["images"]):
            src, _w, _h, rotation = item
            restored = False
            if src and os.path.isfile(src):
                try:
                    w, h = image_size_after_exif(src)
                    result["images"].append([src, w, h, rotation])
                    restored = True
                except Exception:
                    warnings.append("原图无法读取：%s" % src)
            if not restored:
                # 原图不在了：从 PDF 页里把这一格抠出来顶上
                try:
                    if doc is None:
                        doc = PdfDocument(data)
                        pages = doc.pages()
                    page_idx, cell_idx = divmod(i, per_page)
                    if page_idx >= len(pages):
                        warnings.append("原图缺失，且 PDF 里没有对应页：%s"
                                        % os.path.basename(src or "?"))
                        continue
                    if page_idx not in rasters:
                        rasters[page_idx] = largest_page_image(doc, pages[page_idx])
                    base = rasters[page_idx]
                    crop = crop_cell(base, cell_idx, s_rows, s_cols, s_margin, s_padding) \
                        if base is not None else None
                    if crop is None:
                        warnings.append("原图缺失，且该格是空的，已跳过：%s"
                                        % os.path.basename(src or "?"))
                        continue
                    out_path = os.path.join(temp_dir, "from_pdf_%d_%d.jpg" % (page_idx, cell_idx))
                    crop.save(out_path, "JPEG", quality=95, subsampling=0)
                    # 注意：从 PDF 里抠出来的像素已经旋转过了，rotation 记 0
                    result["images"].append([out_path, crop.width, crop.height, 0])
                    crop.close()
                    warnings.append("%s 原图缺失，已用 PDF 里的图像替代"
                                    % os.path.basename(src or "?"))
                except Exception as e:
                    warnings.append("无法从 PDF 恢复 %s：%s" % (os.path.basename(src or "?"), e))
            if progress:
                progress(i + 1, total)

        if result["images"]:
            result["mode"] = "state"
            result["grid"] = (s_rows, s_cols)
            result["margin_mm"] = s_margin
            result["padding_mm"] = s_padding
            return result
        warnings.append("PDF 里有编辑信息，但一张都没能恢复，改为按图像提取")

    # ---------------- 2) 没有编辑信息：按位图提取 ----------------
    doc = PdfDocument(data)
    if doc.encrypted:
        raise ValueError("这个 PDF 已加密/受保护，无法读取里面的图像。")
    pages = doc.pages()
    if not pages:
        raise ValueError("这个 PDF 里没有页面。")

    IMPORT_MAX_DPI = 600          # 合成页面时的分辨率上限（内存保护）
    IMPORT_MIN_DPI = 110

    if mode not in ("grid", "gaps", "page", "images"):
        if looks_like_our_export(doc, pages):
            mode = "grid"          # 本工具导出的（编辑信息丢了）：按排版网格拆回去
        else:
            mode = "gaps"          # 别的软件生成的：优先按空白间隔自动拆分
    result["mode"] = mode
    result["grid"] = (rows, cols)
    result["margin_mm"] = margin_mm
    result["padding_mm"] = padding_mm

    for page_idx, page in enumerate(pages):
        if mode == "images":
            # 把这一页里的每一张位图分别导入（水印相机把一张照片切成好几条就是这种）
            imgs = [im for im in page_images(doc, page) if im.width >= 24 and im.height >= 24]
            if not imgs:
                warnings.append("第 %d 页没有可提取的位图，已跳过" % (page_idx + 1))
            for k, im in enumerate(imgs):
                out_path = os.path.join(temp_dir, "pdf_p%d_img%d.jpg" % (page_idx, k))
                im.save(out_path, "JPEG", quality=95, subsampling=0)
                result["images"].append([out_path, im.width, im.height, 0])
            if progress:
                progress(page_idx + 1, len(pages))
            continue

        our_style = looks_like_our_export(doc, [page])
        base = None
        if mode == "grid" and our_style:
            # 本工具导出的页面本身就是一整张位图，直接用它最快
            base = largest_page_image(doc, page)
        else:
            # 其它 PDF：先把页面按 cm 摆放关系合成出来（相当于扫描这张页面）
            placements = collect_page_placement(doc, page)
            if placements:
                dpi = page_native_dpi(page, placements)
                dpi = max(IMPORT_MIN_DPI, min(IMPORT_MAX_DPI, dpi))
                base, placed = render_page_composed(doc, page, dpi)
                if placed:
                    result["composed_dpi"] = dpi

        if base is None:
            base = largest_page_image(doc, page)
            if base is None:
                warnings.append("第 %d 页没有可提取的位图，已跳过" % (page_idx + 1))
                if progress:
                    progress(page_idx + 1, len(pages))
                continue

        if mode == "page":
            out_path = os.path.join(temp_dir, "pdf_page_%d.jpg" % page_idx)
            base.save(out_path, "JPEG", quality=95, subsampling=0)
            result["images"].append([out_path, base.width, base.height, 0])

        elif mode == "gaps":
            pieces = split_page_by_gaps(base)
            if not pieces:
                # 找不到空白间隔（照片是紧挨着的）：退回整页一张，至少不丢内容
                out_path = os.path.join(temp_dir, "pdf_page_%d.jpg" % page_idx)
                base.save(out_path, "JPEG", quality=95, subsampling=0)
                result["images"].append([out_path, base.width, base.height, 0])
                warnings.append("第 %d 页没找到空白间隔，已按整页导入" % (page_idx + 1))
            else:
                for k, (box, piece) in enumerate(pieces):
                    out_path = os.path.join(temp_dir, "pdf_p%d_g%d.jpg" % (page_idx, k))
                    piece.save(out_path, "JPEG", quality=95, subsampling=0)
                    result["images"].append([out_path, piece.width, piece.height, 0])
                    piece.close()

        else:  # grid：按 rows×cols 等分
            boxes = cell_rects(base.width, base.height, rows, cols, margin_mm, padding_mm)
            kept = 0
            for cell_idx in range(len(boxes)):
                crop = crop_cell(base, cell_idx, rows, cols, margin_mm, padding_mm)
                if crop is None:
                    continue
                out_path = os.path.join(temp_dir, "pdf_p%d_c%d.jpg" % (page_idx, cell_idx))
                crop.save(out_path, "JPEG", quality=95, subsampling=0)
                result["images"].append([out_path, crop.width, crop.height, 0])
                crop.close()
                kept += 1
            if kept == 0:
                warnings.append("第 %d 页按 %d×%d 拆分后没有找到照片"
                                % (page_idx + 1, rows, cols))

        base.close()
        if progress:
            progress(page_idx + 1, len(pages))

    return result


# ==============================================================
# 打印辅助
# ==============================================================
def set_stretch_halftone(dc):
    """
    让 StretchBlt 走 HALFTONE 缩放模式（缩放照片时比默认的 COLORONCOLOR
    平滑得多）。pywin32 的 PyCDC 没有 SetStretchBltMode，所以退回用 ctypes
    调 gdi32；两种方式都失败也不影响打印，只是缩放质量差一点。
    """
    try:
        dc.SetStretchBltMode(4)              # HALFTONE
        return True
    except Exception:
        pass
    try:
        import ctypes
        ctypes.windll.gdi32.SetStretchBltMode(dc.GetSafeHdc(), 4)
        return True
    except Exception:
        return False


# ==============================================================
# 主程序
# ==============================================================
class PhotoLayoutApp:
    def __init__(self, root):
        self.root = root
        root.title(APP_NAME)
        root.geometry("1200x820")
        root.minsize(940, 620)

        # 图片列表：每项 [路径, 宽, 高, 旋转角度(顺时针)]
        self.images = []
        self.thumb_cache = {}

        # 排版参数（可以从 PDF 的编辑信息里恢复）
        self.rows = DEFAULT_ROWS
        self.cols = DEFAULT_COLS
        self.margin_mm = DEFAULT_MARGIN_MM
        self.padding_mm = DEFAULT_PADDING_MM
        self.max_per_page = self.rows * self.cols

        self.current_page = 0
        self.selected_preview_idx = None

        self.drag_follow_id = None
        self.drag_start_idx = None
        self._preview_images = []
        self._follow_images = []
        self.drop_indicator_id = None

        self.press_timer = None
        self.press_x = 0
        self.press_y = 0
        self.press_idx = None
        self.is_dragging = False

        self.dpi_var = StringVar(value=str(DEFAULT_DPI))
        self.quality_var = StringVar(value=str(DEFAULT_QUALITY))
        self.embed_var = BooleanVar(value=True)
        self.layout_var = StringVar(value="%d × %d" % (self.rows, self.cols))

        self._temp_dir = None
        self._progress_win = None
        self._progress_bar = None
        self._progress_label = None
        self._progress_cancelled = False
        self._progress_cancellable = False

        self._build_ui()
        self._bind_events()

        if DND_AVAILABLE:
            self._setup_external_drop()
        else:
            self.status.config(text="就绪（如需资源管理器拖拽，请安装 tkinterdnd2）")

        root.protocol("WM_DELETE_WINDOW", self.on_close)
        atexit.register(self._cleanup_temp)

        self.update_preview()
        self.root.after(100, lambda: self._scroll_to_page(0))

    # ==========================================================
    # 界面
    # ==========================================================
    def _build_ui(self):
        toolbar = ttk.Frame(self.root)
        toolbar.pack(fill=X, padx=5, pady=(5, 2))

        ttk.Button(toolbar, text="添加图片", command=self.add_images).pack(side=LEFT, padx=2)
        ttk.Button(toolbar, text="导入 PDF", command=self.import_pdf).pack(side=LEFT, padx=2)
        ttk.Button(toolbar, text="删除", command=self.remove_selected).pack(side=LEFT, padx=2)
        ttk.Button(toolbar, text="清空", command=self.clear_all).pack(side=LEFT, padx=2)

        ttk.Separator(toolbar, orient=VERTICAL).pack(side=LEFT, padx=8, fill=Y)

        ttk.Button(toolbar, text="顺时针90°",
                   command=lambda: self.rotate_selected(90)).pack(side=LEFT, padx=2)
        ttk.Button(toolbar, text="逆时针90°",
                   command=lambda: self.rotate_selected(-90)).pack(side=LEFT, padx=2)

        ttk.Separator(toolbar, orient=VERTICAL).pack(side=LEFT, padx=8, fill=Y)

        ttk.Button(toolbar, text="导出PDF", command=self.export_pdf).pack(side=LEFT, padx=2)
        ttk.Button(toolbar, text="打印", command=self.print_with_dialog).pack(side=LEFT, padx=2)

        # ---------------- 第二行：导出设置 ----------------
        opts = ttk.Frame(self.root)
        opts.pack(fill=X, padx=5, pady=(0, 4))

        ttk.Label(opts, text="导出分辨率(DPI):").pack(side=LEFT, padx=(2, 2))
        ttk.Combobox(opts, textvariable=self.dpi_var, values=DPI_CHOICES,
                     width=5, state="readonly").pack(side=LEFT, padx=2)

        ttk.Label(opts, text="JPEG 质量:").pack(side=LEFT, padx=(10, 2))
        ttk.Combobox(opts, textvariable=self.quality_var, values=QUALITY_CHOICES,
                     width=4, state="readonly").pack(side=LEFT, padx=2)

        ttk.Checkbutton(opts, text="在 PDF 中写入可再编辑信息（推荐）",
                        variable=self.embed_var).pack(side=LEFT, padx=(14, 2))

        layout_box = ttk.Frame(opts)
        layout_box.pack(side=RIGHT, padx=8)
        ttk.Label(layout_box, text="排版:").pack(side=LEFT)
        self.layout_combo = ttk.Combobox(
            layout_box, textvariable=self.layout_var, values=LAYOUT_CHOICES,
            width=7, state="readonly")
        self.layout_combo.pack(side=LEFT, padx=4)
        self.layout_combo.bind("<<ComboboxSelected>>", self._on_layout_changed)
        self.grid_label = ttk.Label(layout_box, text="")
        self.grid_label.pack(side=LEFT, padx=(4, 0))

        self._update_grid_label()

        # ---------------- 主分栏 ----------------
        self.pane = ttk.PanedWindow(self.root, orient=HORIZONTAL)
        self.pane.pack(fill=BOTH, expand=True, padx=5, pady=5)

        # 左侧
        left_frame = ttk.Frame(self.pane)
        self.pane.add(left_frame, weight=1)

        self.left_drop_hint = ttk.Label(
            left_frame,
            text="图片列表（点击选中）\n可将照片 / 文件夹 / 本工具导出的 PDF 拖到这里",
            anchor=CENTER, justify=CENTER)
        self.left_drop_hint.pack(fill=X, pady=(2, 5))

        list_frame = ttk.Frame(left_frame)
        list_frame.pack(fill=BOTH, expand=True, pady=2)
        list_scroll = ttk.Scrollbar(list_frame, orient=VERTICAL)
        self.listbox = Listbox(list_frame, selectmode=SINGLE, activestyle="none",
                               yscrollcommand=list_scroll.set)
        list_scroll.config(command=self.listbox.yview)
        list_scroll.pack(side=RIGHT, fill=Y)
        self.listbox.pack(side=LEFT, fill=BOTH, expand=True)

        # 右侧
        right_frame = ttk.Frame(self.pane)
        self.pane.add(right_frame, weight=4)

        canvas_frame = ttk.Frame(right_frame)
        canvas_frame.pack(fill=BOTH, expand=True)

        self.canvas = Canvas(canvas_frame, bg="white")
        h_scroll = ttk.Scrollbar(canvas_frame, orient=HORIZONTAL, command=self.canvas.xview)
        v_scroll = ttk.Scrollbar(canvas_frame, orient=VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=h_scroll.set, yscrollcommand=v_scroll.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        h_scroll.grid(row=1, column=0, sticky="ew")
        v_scroll.grid(row=0, column=1, sticky="ns")
        canvas_frame.grid_rowconfigure(0, weight=1)
        canvas_frame.grid_columnconfigure(0, weight=1)
        self.canvas.bind("<Configure>", self._on_canvas_configure)

        nav_frame = ttk.Frame(right_frame)
        nav_frame.pack(fill=X, pady=5)

        self.page_label = ttk.Label(nav_frame, text="页: 1/1")
        self.page_label.pack(side=LEFT, padx=10)

        ttk.Button(nav_frame, text="◀", width=4, command=self.prev_page).pack(side=LEFT, padx=2)
        ttk.Button(nav_frame, text="▶", width=4, command=self.next_page).pack(side=LEFT, padx=2)

        ttk.Label(
            nav_frame,
            text="提示：在右侧图片上按住鼠标约 0.3 秒再拖动，可调整顺序"
        ).pack(side=LEFT, padx=16)

        self.status = ttk.Label(self.root, text="就绪", relief=SUNKEN, anchor=W)
        self.status.pack(fill=X, side=BOTTOM, ipady=2)

        self._bind_preview_drag()

    def _update_grid_label(self):
        if hasattr(self, "grid_label"):
            self.grid_label.config(text="（每页 %d 张，边距 %.0fmm）"
                                        % (self.max_per_page, self.margin_mm))
        if hasattr(self, "layout_var"):
            text = "%d × %d" % (self.rows, self.cols)
            if self.layout_var.get() != text:
                self.layout_var.set(text)

    @staticmethod
    def _parse_layout(text):
        """把 "2 × 2" 之类的文本解析成 (行, 列)。"""
        try:
            parts = re.split(r"[×xX*,，\s]+", str(text).strip())
            nums = [int(p) for p in parts if p.isdigit()]
            if len(nums) >= 2:
                return max(1, min(8, nums[0])), max(1, min(8, nums[1]))
        except Exception:
            pass
        return DEFAULT_ROWS, DEFAULT_COLS

    def _on_layout_changed(self, event=None):
        """切换排版：2×2 / 3×3 / 3×4 …（默认 3×3）。"""
        rows, cols = self._parse_layout(self.layout_var.get())
        if (rows, cols) == (self.rows, self.cols):
            return
        self.rows, self.cols = rows, cols
        self.max_per_page = rows * cols
        self.thumb_cache.clear()
        if self.images:
            self.current_page = max(0, min(self.current_page, self.total_pages() - 1))
            if (self.selected_preview_idx is not None
                    and self.selected_preview_idx >= len(self.images)):
                self.selected_preview_idx = None
        else:
            self.current_page = 0
        self._update_grid_label()
        self.update_preview()
        self._scroll_to_page(self.current_page)
        self.status.config(
            text="排版已切换为 %d × %d：每页 %d 张，共 %d 页"
                 % (rows, cols, self.max_per_page, self.total_pages()))

    def _bind_events(self):
        self.listbox.bind("<<ListboxSelect>>", self.on_select)

        self.root.bind("<Control-o>", lambda e: self.add_images())
        self.root.bind("<Control-i>", lambda e: self.import_pdf())
        self.root.bind("<Control-e>", lambda e: self.export_pdf())
        self.root.bind("<Control-p>", lambda e: self.print_with_dialog())
        self.root.bind("<Delete>", lambda e: self.remove_selected())
        self.root.bind("<Prior>", lambda e: self.prev_page())
        self.root.bind("<Next>", lambda e: self.next_page())
        self.root.bind("<Left>", lambda e: self.prev_page())
        self.root.bind("<Right>", lambda e: self.next_page())
        self.root.bind("<r>", lambda e: self.rotate_selected(90))
        self.root.bind("<R>", lambda e: self.rotate_selected(-90))

    def _bind_preview_drag(self):
        self.canvas.bind("<Button-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_move)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)

    # ==========================================================
    # 拖放
    # ==========================================================
    def _setup_external_drop(self):
        for widget in (self.root, self.pane, self.left_drop_hint, self.listbox):
            try:
                widget.drop_target_register(DND_FILES)
                widget.dnd_bind("<<Drop>>", self.on_external_drop)
            except Exception:
                pass
        self.left_drop_hint.config(
            text="图片列表（点击选中）\n↓\n可拖入照片 / 多张照片 / 文件夹 / 本工具导出的 PDF")

    def on_external_drop(self, event):
        try:
            paths = self.root.tk.splitlist(event.data)
        except Exception:
            paths = []
        if paths:
            self.add_dropped_paths(paths)

    def add_dropped_paths(self, paths):
        image_paths = []
        pdf_paths = []
        folder_count = 0

        for raw_path in paths:
            path = os.path.normpath(raw_path.strip("{}"))
            if os.path.isfile(path):
                if self._is_image_file(path):
                    image_paths.append(path)
                elif os.path.splitext(path)[1].lower() in PDF_EXTENSIONS:
                    pdf_paths.append(path)
            elif os.path.isdir(path):
                folder_count += 1
                self.status.config(text="正在扫描文件夹：%s ..." % os.path.basename(path))
                self.root.update_idletasks()
                # 文件夹里的图片和 PDF 分开处理，避免同一个 PDF 被导入两次
                for found in self._scan_folder_for_images(path):
                    if os.path.splitext(found)[1].lower() in PDF_EXTENSIONS:
                        pdf_paths.append(found)
                    else:
                        image_paths.append(found)

        # 去重（同一份 PDF 只导入一次）
        unique_pdfs, seen_pdf = [], set()
        for p in pdf_paths:
            key = os.path.normcase(os.path.abspath(p))
            if key not in seen_pdf:
                seen_pdf.add(key)
                unique_pdfs.append(p)
        pdf_paths = unique_pdfs

        if image_paths:
            unique, seen = [], set()
            for path in image_paths:
                key = os.path.normcase(os.path.abspath(path))
                if key not in seen:
                    seen.add(key)
                    unique.append(path)
            self.add_images(unique)
        elif not pdf_paths:
            if folder_count:
                messagebox.showinfo(
                    "提示",
                    "拖入的文件夹中没有找到支持的图片。\n\n"
                    "支持：JPG / JPEG / PNG / BMP / GIF / TIFF / WEBP，以及 PDF")
            else:
                messagebox.showinfo("提示", "没有找到支持的图片文件。")

        if pdf_paths:
            self.import_pdf(pdf_paths)

    def _is_image_file(self, path):
        return os.path.splitext(path)[1].lower() in IMAGE_EXTENSIONS

    def _scan_folder_for_images(self, folder):
        result = []
        try:
            for current_root, dirs, files in os.walk(folder):
                dirs.sort()
                files.sort()
                for filename in files:
                    path = os.path.join(current_root, filename)
                    ext = os.path.splitext(path)[1].lower()
                    if ext in IMAGE_EXTENSIONS or ext in PDF_EXTENSIONS:
                        result.append(path)
        except Exception as e:
            self.status.config(text="扫描失败：%s - %s" % (folder, e))
        return result

    # ==========================================================
    # 鼠标：右侧图片排序
    # ==========================================================
    def on_press(self, event):
        self._cancel_press_timer()
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        idx = self._get_image_index_at(x, y)

        self.press_idx = idx
        self.press_x = x
        self.press_y = y
        self.is_dragging = False

        if idx is not None:
            self.press_timer = self.root.after(
                LONG_PRESS_TIME, self._start_drag, x, y, idx)
        else:
            self.selected_preview_idx = None
            self.listbox.selection_clear(0, END)
            self.update_preview()
            self.status.config(text="已取消选中")

    def on_move(self, event):
        self._cancel_press_timer()
        if self.is_dragging and self.drag_follow_id is not None:
            x = self.canvas.canvasx(event.x)
            y = self.canvas.canvasy(event.y)
            self.canvas.coords(self.drag_follow_id, x, y)
            self._update_drop_indicator(x, y)

    def on_release(self, event):
        self._cancel_press_timer()
        if self.is_dragging:
            self._finish_drag(event)
        elif self.press_idx is not None:
            self._select_index(self.press_idx)
            self.status.config(
                text="选中图片 %d：%s" % (self.press_idx + 1, self.images[self.press_idx][0]))

    def _cancel_press_timer(self):
        if self.press_timer:
            try:
                self.root.after_cancel(self.press_timer)
            except Exception:
                pass
            self.press_timer = None

    def _select_index(self, idx):
        if idx is None or not (0 <= idx < len(self.images)):
            return
        self.selected_preview_idx = idx
        self.listbox.selection_clear(0, END)
        self.listbox.selection_set(idx)
        self.listbox.see(idx)
        self.current_page = idx // self.max_per_page
        self.update_preview()

    def _start_drag(self, x, y, idx):
        self.press_timer = None
        self.is_dragging = True
        self.drag_start_idx = idx
        self._create_follow_image(x, y, idx)
        self.status.config(text="拖拽图片 %d，松开鼠标调整位置" % (idx + 1))

    def _finish_drag(self, event):
        if self.drop_indicator_id:
            self.canvas.delete(self.drop_indicator_id)
            self.drop_indicator_id = None

        if self.drag_start_idx is not None and self.drag_follow_id is not None:
            x = self.canvas.canvasx(event.x)
            y = self.canvas.canvasy(event.y)
            target_idx = self._get_drop_target(x, y)
            original_idx = self.drag_start_idx

            if target_idx is not None and target_idx != original_idx:
                item = self.images.pop(original_idx)
                if target_idx > original_idx:
                    target_idx -= 1
                target_idx = max(0, min(target_idx, len(self.images)))
                self.images.insert(target_idx, item)
                self.selected_preview_idx = target_idx
                self._refresh_listbox()
                self.listbox.selection_set(target_idx)
                self.listbox.see(target_idx)
                self.current_page = target_idx // self.max_per_page
                self.update_preview()
                self.status.config(text="已移动到位置 %d" % (target_idx + 1))
            else:
                self.selected_preview_idx = original_idx
                self.update_preview()
                self.status.config(text="取消拖拽")

            self.canvas.delete(self.drag_follow_id)
            self.drag_follow_id = None
            self.drag_start_idx = None
            self.is_dragging = False

    # ==========================================================
    # 图片增删改
    # ==========================================================
    def add_images(self, file_paths=None):
        from_dialog = file_paths is None
        if from_dialog:
            file_paths = filedialog.askopenfilenames(
                title="选择图片或 PDF",
                filetypes=[
                    ("图片和 PDF",
                     "*.jpg *.jpeg *.png *.bmp *.gif *.tif *.tiff *.webp *.pdf"),
                    ("图片文件", "*.jpg *.jpeg *.png *.bmp *.gif *.tif *.tiff *.webp"),
                    ("PDF 文件", "*.pdf"),
                    ("所有文件", "*.*"),
                ])
        if not file_paths:
            return

        pdf_paths = [p for p in file_paths
                     if os.path.splitext(p)[1].lower() in PDF_EXTENSIONS]
        image_paths = [p for p in file_paths if p not in pdf_paths]

        if pdf_paths:
            self.import_pdf(pdf_paths)

        if not image_paths:
            return

        existing = {os.path.normcase(os.path.abspath(item[0])) for item in self.images}
        added = 0
        skipped = 0

        for path in image_paths:
            path = os.path.normpath(path)
            if not os.path.isfile(path) or not self._is_image_file(path):
                continue
            key = os.path.normcase(os.path.abspath(path))
            if key in existing:
                skipped += 1
                continue
            try:
                # 宽高按 EXIF 修正后的方向记录，避免竖拍照片被拉伸
                w, h = image_size_after_exif(path)
                self.images.append([path, w, h, 0])
                self._insert_listbox_entry(len(self.images) - 1)
                existing.add(key)
                added += 1
            except Exception as e:
                messagebox.showerror("错误", "无法加载图片：\n%s\n\n%s"
                                     % (os.path.basename(path), e))

        if added:
            self.thumb_cache.clear()
            self.status.config(text="已添加 %d 张图片（跳过重复 %d 张），共 %d 张"
                                    % (added, skipped, len(self.images)))
            self.current_page = 0
            self.selected_preview_idx = None
            self.update_preview()
            self.root.after(50, lambda: self._scroll_to_page(0))
        elif skipped:
            self.status.config(text="全部都是已存在图片，跳过 %d 张" % skipped)

    def _insert_listbox_entry(self, idx):
        self.listbox.insert(END, "%d. %s" % (idx + 1, os.path.basename(self.images[idx][0])))

    def _refresh_listbox(self):
        self.listbox.delete(0, END)
        for i, item in enumerate(self.images):
            self.listbox.insert(END, "%d. %s" % (i + 1, os.path.basename(item[0])))
        if self.selected_preview_idx is not None and self.selected_preview_idx < len(self.images):
            self.listbox.selection_set(self.selected_preview_idx)
            self.listbox.see(self.selected_preview_idx)

    def clear_all(self):
        if self.images and not messagebox.askyesno("确认", "清空所有图片？"):
            return
        self.images.clear()
        self.listbox.delete(0, END)
        self.thumb_cache.clear()
        self.current_page = 0
        self.selected_preview_idx = None
        self.update_preview()
        self._scroll_to_page(0)
        self.status.config(text="已清空")

    def remove_selected(self):
        idx = self.selected_preview_idx
        if idx is None:
            list_idx = self.listbox.curselection()
            if list_idx:
                idx = list_idx[0]
        if idx is None:
            messagebox.showinfo("提示", "请先选中一张图片")
            return
        if idx >= len(self.images):
            return

        del self.images[idx]
        self.thumb_cache.clear()
        self.selected_preview_idx = None
        self._refresh_listbox()

        if self.current_page >= self.total_pages():
            self.current_page = max(0, self.total_pages() - 1)

        self.update_preview()
        self._scroll_to_page(self.current_page)
        self.status.config(text="已删除，剩余 %d 张" % len(self.images))

    def rotate_selected(self, angle):
        idx = self.selected_preview_idx
        if idx is None:
            list_idx = self.listbox.curselection()
            if list_idx:
                idx = list_idx[0]
        if idx is None:
            messagebox.showinfo("提示", "请先选中一张图片")
            return
        if idx >= len(self.images):
            return

        self.images[idx][3] = (self.images[idx][3] + angle) % 360
        self.thumb_cache.clear()
        self.update_preview()
        self.status.config(text="旋转 %d°：%s"
                                % (angle, os.path.basename(self.images[idx][0])))

    # ==========================================================
    # 缩略图
    # ==========================================================
    def _get_thumbnail(self, img_data, box):
        path, _w, _h, rotation = img_data[0], img_data[1], img_data[2], img_data[3]
        bw = max(1, int(box[0]))
        bh = max(1, int(box[1]))
        key = (path, rotation, bw, bh)
        if key in self.thumb_cache:
            return self.thumb_cache[key]
        try:
            img = load_photo_rgb(path, rotation)
            img = fit_image(img, bw, bh)
            photo = ImageTk.PhotoImage(img)
            img.close()
        except Exception:
            return None
        if len(self.thumb_cache) > 600:
            self.thumb_cache.clear()
        self.thumb_cache[key] = photo
        return photo

    # ==========================================================
    # 版面计算
    # ==========================================================
    def _get_layout_values(self):
        scale = PAGE_W / A4_W_MM
        margin_px = self.margin_mm * scale
        pad_px = self.padding_mm * scale
        cell_w = (A4_W_MM - 2 * self.margin_mm) / self.cols * scale
        cell_h = (A4_H_MM - 2 * self.margin_mm) / self.rows * scale
        return scale, margin_px, pad_px, cell_w, cell_h

    def _page_origin(self, page_idx):
        return page_idx * (PAGE_W + PAGE_GAP) + 10, 10

    def _cell_center(self, page_idx, rel_idx):
        _scale, margin_px, _pad, cell_w, cell_h = self._get_layout_values()
        page_x, page_y = self._page_origin(page_idx)
        row, col = divmod(rel_idx, self.cols)
        cx = page_x + margin_px + col * cell_w + cell_w / 2.0
        cy = page_y + margin_px + row * cell_h + cell_h / 2.0
        return cx, cy

    def _drawn_size(self, item, avail_w, avail_h):
        """按 fit_image 的规则算出画面上的宽高（与实际渲染一致）。"""
        _path, w, h, rotation = item[0], item[1], item[2], item[3]
        if rotation % 180:
            w, h = h, w
        w = max(1, int(w))
        h = max(1, int(h))
        factor = min(avail_w / w, avail_h / h)
        return w * factor, h * factor

    def _get_image_index_at(self, x, y):
        if not self.images:
            return None
        _scale, margin_px, pad_px, cell_w, cell_h = self._get_layout_values()
        avail_w = cell_w - 2 * pad_px
        avail_h = cell_h - 2 * pad_px

        for page_idx in range(self.total_pages()):
            page_x, page_y = self._page_origin(page_idx)
            if x < page_x or x > page_x + PAGE_W:
                continue
            if y < page_y + margin_px or y > page_y + PAGE_H - margin_px:
                continue

            start = page_idx * self.max_per_page
            end = min(start + self.max_per_page, len(self.images))
            for idx in range(start, end):
                cx, cy = self._cell_center(page_idx, idx - start)
                draw_w, draw_h = self._drawn_size(self.images[idx], avail_w, avail_h)
                if (cx - draw_w / 2 <= x <= cx + draw_w / 2
                        and cy - draw_h / 2 <= y <= cy + draw_h / 2):
                    return idx
        return None

    def _get_drop_target(self, x, y):
        if not self.images:
            return 0
        _scale, margin_px, _pad, cell_w, cell_h = self._get_layout_values()

        for page_idx in range(self.total_pages()):
            page_x, page_y = self._page_origin(page_idx)
            if x < page_x or x > page_x + PAGE_W:
                continue
            if y < page_y + margin_px or y > page_y + PAGE_H - margin_px:
                continue

            col = int((x - page_x - margin_px) / cell_w)
            row = int((y - page_y - margin_px) / cell_h)
            col = max(0, min(self.cols - 1, col))
            row = max(0, min(self.rows - 1, row))

            idx = page_idx * self.max_per_page + row * self.cols + col
            if idx >= len(self.images):
                return len(self.images)

            cell_center_x = page_x + margin_px + col * cell_w + cell_w / 2.0
            return idx if x < cell_center_x else idx + 1
        return len(self.images)

    def _create_follow_image(self, x, y, global_idx):
        item = self.images[global_idx]
        _scale, _margin, pad_px, cell_w, cell_h = self._get_layout_values()
        try:
            photo = self._get_thumbnail(item, ((cell_w - 2 * pad_px) * 0.6,
                                               (cell_h - 2 * pad_px) * 0.6))
            if photo is None:
                raise RuntimeError
            self._follow_images.append(photo)
            self.drag_follow_id = self.canvas.create_image(x, y, image=photo, anchor=CENTER)
        except Exception:
            self.drag_follow_id = self.canvas.create_rectangle(
                x - 30, y - 30, x + 30, y + 30, fill="gray", outline="black",
                stipple="gray50")

    def _update_drop_indicator(self, x, y):
        if self.drop_indicator_id:
            self.canvas.delete(self.drop_indicator_id)
            self.drop_indicator_id = None

        target = self._get_drop_target(x, y)
        if target is None:
            return

        _scale, margin_px, _pad, cell_w, cell_h = self._get_layout_values()
        if target >= len(self.images):
            if not self.images:
                return
            last = len(self.images) - 1
            page_idx, rel = divmod(last, self.max_per_page)
            row, col = divmod(rel, self.cols)
            cx, _cy = self._cell_center(page_idx, rel)
            line_x = cx + cell_w / 2.0
        else:
            page_idx, rel = divmod(target, self.max_per_page)
            row, col = divmod(rel, self.cols)
            cx, _cy = self._cell_center(page_idx, rel)
            line_x = cx - cell_w / 2.0

        page_x, page_y = self._page_origin(page_idx)
        y0 = page_y + margin_px + row * cell_h
        y1 = y0 + cell_h
        self.drop_indicator_id = self.canvas.create_line(
            line_x, y0, line_x, y1, fill="#00CC00", width=5, capstyle=ROUND)

    # ==========================================================
    # 分页与预览
    # ==========================================================
    def total_pages(self):
        return max(1, (len(self.images) + self.max_per_page - 1) // self.max_per_page)

    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self.update_preview()
            self._scroll_to_page(self.current_page)

    def next_page(self):
        if self.current_page < self.total_pages() - 1:
            self.current_page += 1
            self.update_preview()
            self._scroll_to_page(self.current_page)

    def _scroll_to_page(self, page_idx):
        canvas_width = self.canvas.winfo_width()
        if canvas_width <= 0:
            return
        bbox = self.canvas.bbox("all")
        if not bbox:
            return
        total_width = bbox[2] - bbox[0]
        if total_width <= 0:
            return
        page_x, _page_y = self._page_origin(page_idx)
        target_x = max(0, page_x - (canvas_width - PAGE_W) / 2.0)
        self.canvas.xview_moveto(target_x / total_width)

    def on_select(self, event):
        idx = self.listbox.curselection()
        if idx:
            self.selected_preview_idx = idx[0]
            page = self.selected_preview_idx // self.max_per_page
            self.current_page = page
            self.update_preview()
            self.root.after(20, lambda: self._scroll_to_page(page))

    def _on_canvas_configure(self, event):
        self.update_preview()

    def update_preview(self):
        self.canvas.delete("all")
        self._preview_images.clear()
        self._follow_images.clear()
        self.drop_indicator_id = None

        total = self.total_pages()
        self.page_label.config(text="页: %d/%d   共 %d 张   排版 %d×%d"
                                    % (self.current_page + 1, total, len(self.images),
                                       self.rows, self.cols))

        if not self.images:
            self.canvas.create_text(
                160, 120,
                text="请添加图片\n\n也可以把照片、文件夹，\n或本工具导出的 PDF 拖到左侧列表",
                font=("Microsoft YaHei UI", 14), fill="gray", justify=CENTER)
            self.canvas.config(scrollregion=(0, 0, 460, 320))
            return

        _scale, margin_px, pad_px, cell_w, cell_h = self._get_layout_values()
        avail_w = max(1, cell_w - 2 * pad_px)
        avail_h = max(1, cell_h - 2 * pad_px)

        total_width = total * (PAGE_W + PAGE_GAP) + 20
        total_height = PAGE_H + 20
        self.canvas.config(scrollregion=(0, 0, total_width, total_height))

        for page_idx in range(total):
            x_offset, y_offset = self._page_origin(page_idx)

            self.canvas.create_rectangle(x_offset, y_offset,
                                         x_offset + PAGE_W, y_offset + PAGE_H,
                                         fill="white", outline="black", width=1)

            for r in range(self.rows + 1):
                y = y_offset + margin_px + r * cell_h
                self.canvas.create_line(x_offset + margin_px, y,
                                        x_offset + PAGE_W - margin_px, y,
                                        fill="lightgray", dash=(2, 2))
            for c in range(self.cols + 1):
                x = x_offset + margin_px + c * cell_w
                self.canvas.create_line(x, y_offset + margin_px,
                                        x, y_offset + PAGE_H - margin_px,
                                        fill="lightgray", dash=(2, 2))

            start = page_idx * self.max_per_page
            end = min(start + self.max_per_page, len(self.images))

            if (self.selected_preview_idx is not None
                    and start <= self.selected_preview_idx < end):
                sel_rel = self.selected_preview_idx - start
                sel_row, sel_col = divmod(sel_rel, self.cols)
                gx0 = x_offset + margin_px + sel_col * cell_w
                gy0 = y_offset + margin_px + sel_row * cell_h
                self.canvas.create_rectangle(gx0, gy0, gx0 + cell_w, gy0 + cell_h,
                                             fill="gray", stipple="gray50", outline="")

            for img_idx in range(start, end):
                item = self.images[img_idx]
                cx, cy = self._cell_center(page_idx, img_idx - start)
                photo = self._get_thumbnail(item, (avail_w, avail_h))
                if photo is not None:
                    self._preview_images.append(photo)
                    self.canvas.create_image(cx, cy, image=photo)
                else:
                    draw_w, draw_h = self._drawn_size(item, avail_w, avail_h)
                    self.canvas.create_rectangle(cx - draw_w / 2, cy - draw_h / 2,
                                                 cx + draw_w / 2, cy + draw_h / 2,
                                                 fill="red", outline="black")
                    self.canvas.create_text(cx, cy, text="无法读取\n%s"
                                            % os.path.basename(item[0]),
                                            fill="white", width=max(40, draw_w))

        if self.selected_preview_idx is not None and self.selected_preview_idx < len(self.images):
            self.listbox.selection_clear(0, END)
            self.listbox.selection_set(self.selected_preview_idx)
            self.listbox.see(self.selected_preview_idx)

    # ==========================================================
    # 进度窗口
    # ==========================================================
    def _progress_begin(self, title, total, cancellable=True):
        self._progress_cancelled = False
        self._progress_cancellable = cancellable
        win = Toplevel(self.root)
        win.title(title)
        win.geometry("440x140")
        win.resizable(False, False)
        win.transient(self.root)
        win.protocol("WM_DELETE_WINDOW", self._progress_cancel)
        if cancellable:
            ttk.Button(win, text="取消", command=self._progress_cancel).pack(pady=6)

        self._progress_label = ttk.Label(win, text="准备中…", anchor=W)
        self._progress_label.pack(fill=X, padx=15, pady=(15, 4))
        self._progress_bar = ttk.Progressbar(win, mode="determinate",
                                             maximum=max(1, total), length=400)
        self._progress_bar.pack(padx=15, pady=6)
        self._progress_win = win
        try:
            win.grab_set()
        except Exception:
            pass
        self.root.update()

    def _progress_step(self, done, text=None):
        if self._progress_cancelled:
            raise _Cancelled()
        if self._progress_bar is not None:
            self._progress_bar["value"] = done
        if text and self._progress_label is not None:
            self._progress_label.config(text=text)
        self.root.update()

    def _progress_cancel(self):
        if self._progress_cancellable:
            self._progress_cancelled = True

    def _progress_end(self):
        self._progress_cancelled = False
        self._progress_cancellable = False
        self._progress_bar = None
        self._progress_label = None
        if self._progress_win is not None:
            try:
                self._progress_win.grab_release()
            except Exception:
                pass
            try:
                self._progress_win.destroy()
            except Exception:
                pass
            self._progress_win = None
        try:
            self.root.update()
        except Exception:
            pass

    # ==========================================================
    # 导出 PDF
    # ==========================================================
    def export_pdf(self):
        if not self.images:
            messagebox.showinfo("提示", "没有图片可导出")
            return

        missing = [item[0] for item in self.images if not os.path.isfile(item[0])]
        if missing:
            preview = "\n".join(os.path.basename(p) for p in missing[:8])
            if len(missing) > 8:
                preview += "\n…"
            if not messagebox.askyesno(
                    "有文件找不到",
                    "有 %d 张图片的文件已不存在：\n\n%s\n\n这些位置会画成红色占位框。\n仍要导出吗？"
                    % (len(missing), preview)):
                return

        try:
            dpi = int(self.dpi_var.get())
        except ValueError:
            dpi = DEFAULT_DPI
        try:
            quality = int(self.quality_var.get())
        except ValueError:
            quality = DEFAULT_QUALITY

        file_path = filedialog.asksaveasfilename(
            title="导出 A4 PDF", defaultextension=".pdf",
            filetypes=[("PDF 文件", "*.pdf")])
        if not file_path:
            return

        total = self.total_pages()
        embed = bool(self.embed_var.get())
        state_bytes = None
        if embed:
            state = make_state(self.images, self.rows, self.cols,
                               self.margin_mm, self.padding_mm, dpi)
            state_bytes = state_to_bytes(state)

        self._progress_begin("正在导出 PDF", total)
        try:
            def render_page(idx):
                self._progress_step(idx + 1, "正在导出第 %d / %d 页…" % (idx + 1, total))
                page = render_page_raster(self.images, idx, dpi, self.rows, self.cols,
                                          self.margin_mm, self.padding_mm)
                buf = io.BytesIO()
                page.save(buf, "JPEG", quality=quality,
                          subsampling=0 if quality >= 90 else 2)
                size = page.size
                page.close()
                return buf.getvalue(), size[0], size[1]

            write_pdf(file_path, total, render_page,
                      info={
                          "title": os.path.splitext(os.path.basename(file_path))[0],
                          "creator": APP_NAME,
                          "producer": APP_NAME,
                          "keywords": "A4PhotoLayout 可再编辑 PDF",
                      },
                      state_bytes=state_bytes)
            self._progress_end()
        except _Cancelled:
            self._progress_end()
            try:
                if os.path.exists(file_path):
                    os.remove(file_path)
            except Exception:
                pass
            self.status.config(text="已取消导出")
            return
        except Exception as e:
            self._progress_end()
            self.status.config(text="PDF 导出失败")
            messagebox.showerror("导出失败", "%s\n\n%s" % (e, traceback.format_exc(limit=3)))
            return

        size_mb = os.path.getsize(file_path) / 1048576.0
        self.status.config(text="PDF 已导出：%s（%d 页，%.1f MB，%d DPI）"
                                % (os.path.basename(file_path), total, size_mb, dpi))
        messagebox.showinfo(
            "导出成功",
            "已保存到：\n%s\n\n页数：%d\n分辨率：%d DPI\nJPEG 质量：%d\n文件大小：%.1f MB\n%s"
            % (file_path, total, dpi, quality, size_mb,
               "已写入可再编辑信息：以后可以把这个 PDF 直接拖回本工具继续编辑。"
               if embed else "（未写入可再编辑信息）"))

    # ==========================================================
    # 导入 PDF
    # ==========================================================
    def import_pdf(self, paths=None):
        if paths is None:
            paths = filedialog.askopenfilenames(
                title="导入 PDF（本工具导出的 PDF 可直接继续编辑）",
                filetypes=[("PDF 文件", "*.pdf"), ("所有文件", "*.*")])
        paths = [p for p in (paths or []) if os.path.isfile(p)]
        if not paths:
            return

        self._progress_begin("正在读取 PDF", 1, cancellable=False)
        try:
            self._progress_step(0, "正在分析 PDF…")
            infos = [describe_pdf(p) for p in paths]
        finally:
            self._progress_end()

        opts = self._ask_import_options(infos)
        if opts is None:
            return

        temp_dir = self._ensure_temp_dir()
        collected = []
        warnings = []
        state_layout = None
        failed = []
        used_modes = []

        total_pages_hint = sum(max(1, i["pages"]) for i in infos)
        self._progress_begin("正在导入 PDF", total_pages_hint)
        try:
            for info in infos:
                path = info["path"]
                if info["error"]:
                    failed.append("%s：%s" % (info["name"], info["error"]))
                    continue

                counter = {"done": 0}

                def progress(done, total, _name=info["name"], _c=counter):
                    _c["done"] = done
                    self._progress_step(done, "正在导入 %s：%d / %d"
                                        % (_name, done, max(1, total)))

                try:
                    res = import_pdf_file(path, opts["mode"],
                                          opts.get("rows", self.rows),
                                          opts.get("cols", self.cols),
                                          self.margin_mm, self.padding_mm,
                                          temp_dir, progress=progress)
                except _Cancelled:
                    raise
                except Exception as e:
                    failed.append("%s：%s" % (info["name"], e))
                    continue

                collected.extend(res["images"])
                used_modes.append(res["mode"])
                warnings.extend("%s：%s" % (info["name"], w) for w in res["warnings"])
                if res["mode"] == "state" and res["grid"]:
                    state_layout = (res["grid"], res["margin_mm"], res["padding_mm"])
        except _Cancelled:
            self._progress_end()
            self.status.config(text="已取消导入")
            return
        finally:
            self._progress_end()

        if not collected:
            messagebox.showwarning(
                "导入失败",
                "没有从 PDF 里导入任何图片。\n\n" +
                ("\n".join(failed[:6]) if failed else
                 "\n".join(warnings[:6]) if warnings else
                 "可能这个 PDF 里没有位图（纯文字/矢量页面）。"))
            return

        # 空列表时才采纳 PDF 里带的排版参数，避免打乱当前排版
        if state_layout and (opts["replace"] or not self.images):
            (s_rows, s_cols), s_margin, s_padding = state_layout
            if (s_rows, s_cols) != (self.rows, self.cols) or s_margin != self.margin_mm:
                self.rows, self.cols = s_rows, s_cols
                self.margin_mm = s_margin
                self.padding_mm = s_padding
                self.max_per_page = self.rows * self.cols
                self._update_grid_label()
                warnings.insert(0, "已按 PDF 里的编辑信息切换到排版 %d×%d" % (s_rows, s_cols))

        if opts["replace"] or not self.images:
            self.images = list(collected)
        else:
            self.images.extend(collected)

        self.thumb_cache.clear()
        self.listbox.delete(0, END)
        self._refresh_listbox()
        self.current_page = 0
        self.selected_preview_idx = None
        self.update_preview()
        self.root.after(50, lambda: self._scroll_to_page(0))

        self.status.config(text="已从 PDF 导入 %d 张，当前共 %d 张"
                                % (len(collected), len(self.images)))

        # 说明文字按"实际用的方式"写，而不是按对话框里选的选项写
        mode_labels = {"state": "根据 PDF 里的编辑信息无损恢复",
                       "grid": "按 %d×%d 网格拆分每页" % (self.rows, self.cols),
                       "gaps": "按空白间隔自动拆分每页",
                       "page": "每页作为一张整页图片",
                       "images": "每页里的每张位图分别导入"}
        mode_text = "、".join(
            dict.fromkeys(mode_labels.get(m, m) for m in used_modes)) or opts["mode_label"]

        msg = ["已导入 %d 张图片（%s）。" % (len(collected), mode_text)]
        if failed:
            msg.append("\n失败：")
            msg.extend(failed[:5])
        if warnings:
            msg.append("\n提示：")
            msg.extend(warnings[:6])
            if len(warnings) > 6:
                msg.append("…另有 %d 条提示" % (len(warnings) - 6))
        messagebox.showinfo("导入完成", "\n".join(msg))

    def _ask_import_options(self, infos):
        """导入前的确认窗口：显示检测结果，必要时让用户选导入方式。"""
        need_mode = any(not i["has_state"] for i in infos)

        dlg = Toplevel(self.root)
        dlg.title("导入 PDF")
        dlg.transient(self.root)
        dlg.resizable(False, False)

        frame = ttk.Frame(dlg)
        frame.pack(fill=BOTH, expand=True, padx=15, pady=12)

        lines = []
        for info in infos:
            if info["error"]:
                lines.append("• %s —— 读取失败：%s" % (info["name"], info["error"]))
                continue
            desc = "• %s —— %d 页" % (info["name"], info["pages"])
            if info["encrypted"]:
                desc += "（已加密，无法导入）"
            elif info["has_state"]:
                desc += "，含编辑信息：可恢复 %d 张照片" % info["state_images"]
                if info["missing"]:
                    desc += "（其中 %d 张原图已不在，将从 PDF 里抠图替代）" % info["missing"]
            else:
                desc += "，未检测到编辑信息"
                n_img = info.get("first_page_images") or 0
                if n_img == 1:
                    desc += "（每页 1 张位图）"
                elif n_img > 1:
                    desc += "（第 1 页就有 %d 张位图%s）" % (
                        n_img, "，可自动合成整页" if info.get("composable") else "")
            lines.append(desc)

        ttk.Label(frame, text="\n".join(lines), justify=LEFT,
                  font=("Microsoft YaHei UI", 9)).pack(anchor=W)

        mode_var = StringVar(value="auto")
        grid_rows_var = IntVar(value=self.rows)
        grid_cols_var = IntVar(value=self.cols)
        if need_mode:
            ttk.Separator(frame, orient=HORIZONTAL).pack(fill=X, pady=10)
            ttk.Label(frame,
                      text="这个 PDF 里没有本工具的编辑信息，请选择导入方式：",
                      justify=LEFT).pack(anchor=W, pady=(0, 4))
            ttk.Radiobutton(frame, value="auto", variable=mode_var,
                            text="自动判断（推荐）").pack(anchor=W)
            ttk.Radiobutton(
                frame, value="gaps", variable=mode_var,
                text="按空白间隔自动拆分每页（照片之间有白边的表格/水印相机照片表）"
            ).pack(anchor=W)
            ttk.Radiobutton(frame, value="page", variable=mode_var,
                            text="每页作为一张整页图片（忠实还原整个页面）").pack(anchor=W)
            grid_row = ttk.Frame(frame)
            grid_row.pack(anchor=W, fill=X)
            ttk.Radiobutton(grid_row, value="grid", variable=mode_var,
                            text="按网格等分拆分每页：").pack(side=LEFT)
            ttk.Spinbox(grid_row, from_=1, to=8, width=3,
                        textvariable=grid_rows_var).pack(side=LEFT, padx=(4, 0))
            ttk.Label(grid_row, text="行 ×").pack(side=LEFT, padx=2)
            ttk.Spinbox(grid_row, from_=1, to=8, width=3,
                        textvariable=grid_cols_var).pack(side=LEFT)
            ttk.Label(grid_row, text="列").pack(side=LEFT, padx=2)
            ttk.Radiobutton(frame, value="images", variable=mode_var,
                            text="把每页里的每一张位图分别导入（照片被切成条的情况）"
                            ).pack(anchor=W)

        ttk.Separator(frame, orient=HORIZONTAL).pack(fill=X, pady=10)
        replace_var = BooleanVar(value=not self.images)
        if self.images:
            ttk.Radiobutton(frame, value=True, variable=replace_var,
                            text="替换当前列表（清空后再导入）").pack(anchor=W)
            ttk.Radiobutton(frame, value=False, variable=replace_var,
                            text="追加到当前列表末尾（当前 %d 张）" % len(self.images)
                            ).pack(anchor=W)
        else:
            ttk.Label(frame, text="当前列表为空，导入的图片会直接加入列表。").pack(anchor=W)

        result = {}

        def ok():
            result["mode"] = mode_var.get()
            result["replace"] = bool(replace_var.get()) if self.images else True
            try:
                result["rows"] = max(1, min(8, int(grid_rows_var.get())))
                result["cols"] = max(1, min(8, int(grid_cols_var.get())))
            except Exception:
                result["rows"], result["cols"] = self.rows, self.cols
            labels = {"state": "根据 PDF 里的编辑信息无损恢复",
                      "grid": "按 %d×%d 网格拆分" % (result["rows"], result["cols"]),
                      "gaps": "按空白间隔自动拆分",
                      "page": "每页一张整页图片",
                      "images": "每页里的每张位图分别导入",
                      "auto": "自动判断"}
            result["mode_label"] = labels.get(result["mode"], result["mode"])
            dlg.destroy()

        buttons = ttk.Frame(frame)
        buttons.pack(fill=X, pady=(12, 0))
        ttk.Button(buttons, text="取消", command=dlg.destroy).pack(side=RIGHT, padx=5)
        ttk.Button(buttons, text="开始导入", command=ok).pack(side=RIGHT, padx=5)

        dlg.bind("<Return>", lambda e: ok())
        dlg.bind("<Escape>", lambda e: dlg.destroy())

        dlg.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_height()) // 3
        dlg.geometry("+%d+%d" % (max(0, x), max(0, y)))
        dlg.grab_set()
        dlg.wait_window()
        return result or None

    # ==========================================================
    # 临时目录
    # ==========================================================
    def _ensure_temp_dir(self):
        if self._temp_dir is None:
            base = os.path.join(tempfile.gettempdir(),
                                "A4PhotoLayout_import_%d" % os.getpid())
            os.makedirs(base, exist_ok=True)
            self._temp_dir = base
        return self._temp_dir

    def _cleanup_temp(self):
        if self._temp_dir and os.path.isdir(self._temp_dir):
            shutil.rmtree(self._temp_dir, ignore_errors=True)
        self._temp_dir = None

    def on_close(self):
        self._cleanup_temp()
        try:
            self.root.destroy()
        except Exception:
            pass

    # ==========================================================
    # 打印
    # ==========================================================
    def print_with_dialog(self):
        if not PRINT_AVAILABLE:
            messagebox.showerror(
                "打印不可用",
                "打印功能需要安装 pywin32。\n\n请执行：\npy -m pip install pywin32")
            return
        if not self.images:
            messagebox.showinfo("提示", "没有图片可打印")
            return

        printers = self._get_installed_printers()
        if not printers:
            messagebox.showerror("没有打印机", "Windows 没有检测到已安装的打印机。")
            return
        self._show_printer_dialog(printers)

    def _get_installed_printers(self):
        result = []
        try:
            flags = win32print.PRINTER_ENUM_LOCAL | win32print.PRINTER_ENUM_CONNECTIONS
            for item in win32print.EnumPrinters(flags, None, 2):
                name = item.get("pPrinterName")
                if name and name not in result:
                    result.append(name)
        except Exception as e:
            messagebox.showerror("读取打印机失败", str(e))
        return result

    def _show_printer_dialog(self, printers):
        dialog = Toplevel(self.root)
        dialog.title("选择打印机")
        dialog.geometry("520x290")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        frame = ttk.Frame(dialog)
        frame.pack(fill=BOTH, expand=True, padx=15, pady=15)

        ttk.Label(frame, text="请选择要使用的打印机：",
                  font=("Microsoft YaHei UI", 10)).pack(anchor=W, pady=(0, 8))

        combo_var = StringVar()
        try:
            default_printer = win32print.GetDefaultPrinter()
        except Exception:
            default_printer = printers[0]
        combo_var.set(default_printer if default_printer in printers else printers[0])

        combo = ttk.Combobox(frame, textvariable=combo_var, values=printers,
                             state="readonly", width=58)
        combo.pack(fill=X, pady=5)

        ttk.Label(frame, text=(
            "纸张：A4（210 × 297 mm）\n"
            "排版：%d × %d\n"
            "打印内容：当前所有排版页面（等比缩放并居中，不会变形）"
            % (self.rows, self.cols)), justify=LEFT).pack(anchor=W, pady=15)

        button_frame = ttk.Frame(frame)
        button_frame.pack(side=BOTTOM, fill=X, pady=(10, 0))

        def do_print():
            printer_name = combo_var.get().strip()
            if not printer_name:
                messagebox.showwarning("提示", "请选择打印机。", parent=dialog)
                return
            dialog.destroy()
            self._print_to_printer(printer_name)

        ttk.Button(button_frame, text="取消",
                   command=dialog.destroy).pack(side=RIGHT, padx=5)
        ttk.Button(button_frame, text="开始打印",
                   command=do_print).pack(side=RIGHT, padx=5)

        combo.focus_set()
        dialog.bind("<Return>", lambda e: do_print())
        dialog.bind("<Escape>", lambda e: dialog.destroy())

    @staticmethod
    def _start_doc(hdc, doc_name):
        """
        有些"文件打印机"（Microsoft Print to PDF / XPS）不接受不带输出文件的
        StartDoc，会直接报 StartDoc failed。这里先按常规方式试一次，失败再用
        空的输出文件名重试（驱动自己会弹出"保存打印输出为"对话框）。
        """
        try:
            hdc.StartDoc(doc_name)
            return True
        except Exception:
            pass
        try:
            hdc.StartDoc(doc_name, "")
            return True
        except Exception:
            return False

    @staticmethod
    def _blit_via_memory_dc(printer_dc, img, dst_rect):
        """
        先画进内存 DC，再用 StretchBlt 缩放到目标矩形，最后送给打印机 DC。

        StretchBlt 是唯一能同时做到"正确缩放"和"被 Microsoft Print to PDF
        接受"的画法（实测打印出来的页面与原图平均色差 0.09，几乎一模一样）。
        """
        screen_dc = src_dc = mem_dc = bmp = None
        try:
            screen_dc = win32gui.GetDC(0)
            src_dc = win32ui.CreateDCFromHandle(screen_dc)
            mem_dc = src_dc.CreateCompatibleDC()
            bmp = win32ui.CreateBitmap()
            bmp.CreateCompatibleBitmap(src_dc, img.width, img.height)
            mem_dc.SelectObject(bmp)
            ImageWin.Dib(img).draw(mem_dc.GetSafeHdc(), (0, 0, img.width, img.height))
            set_stretch_halftone(printer_dc)
            x0, y0, x1, y1 = dst_rect
            printer_dc.StretchBlt((x0, y0), (max(1, x1 - x0), max(1, y1 - y0)),
                                  mem_dc, (0, 0), (img.width, img.height),
                                  win32con.SRCCOPY)
            return True
        finally:
            if bmp is not None:
                try:
                    win32gui.DeleteObject(bmp.GetHandle())
                except Exception:
                    pass
            for dc in (mem_dc, src_dc):
                if dc is not None:
                    try:
                        dc.DeleteDC()
                    except Exception:
                        pass

    @classmethod
    def _draw_page_on_dc(cls, printer_dc, img, dst_rect):
        """
        把整页位图送到打印机 DC。两种画法按顺序尝试：

        1) 内存 DC + StretchBlt —— 缩放正确，且 Microsoft Print to PDF / XPS
           这类驱动也接受（换成 StretchDIBits 画完 EndPage 会失败 -1）；
           但个别驱动（例如 Canon UFRII）不支持 StretchBlt。
        2) ImageWin.Dib.draw（StretchDIBits）—— 兼容性最广的老办法。

        两种画法都会等比缩放到 dst_rect，所以版面不会变形。
        """
        if win32gui is not None and win32con is not None:
            try:
                if cls._blit_via_memory_dc(printer_dc, img, dst_rect):
                    return True
            except Exception:
                pass
        ImageWin.Dib(img).draw(printer_dc.GetSafeHdc(), dst_rect)
        return True

    def _print_to_printer(self, printer_name):
        """
        V3 修正：
          * 用打印机自身的分辨率渲染（不再跟随"导出质量"，2400 DPI 不会再把内存打爆）
          * 按可打印区域等比缩放并居中（A4 版面打到 Letter 等纸张上不再变形）
          * 每页只 StartPage / EndPage 一次，不会出现空白页
        """
        hdc = None
        total = self.total_pages()
        self._progress_begin("正在打印", total, cancellable=False)
        try:
            self._progress_step(0, "正在连接打印机：%s" % printer_name)

            hdc = win32ui.CreateDC()
            hdc.CreatePrinterDC(printer_name)

            def caps(index, fallback):
                try:
                    value = hdc.GetDeviceCaps(index)
                    return int(value) if value else fallback
                except Exception:
                    return fallback

            dpi_x = caps(CAP_LOGPIXELSX, 300)
            dpi_y = caps(CAP_LOGPIXELSY, 300)
            dpi_x = max(72, min(PRINT_MAX_DPI, dpi_x))
            dpi_y = max(72, min(PRINT_MAX_DPI, dpi_y))
            area_w = caps(CAP_HORZRES, int(A4_W_MM / 25.4 * dpi_x))
            area_h = caps(CAP_VERTRES, int(A4_H_MM / 25.4 * dpi_y))

            if not self._start_doc(hdc, "A4 Photo Layout"):
                # Microsoft Print to PDF / XPS 这类"文件打印机"必须给出输出文件，
                # 否则 StartDoc 直接失败。这里问一下用户存到哪里，再重试。
                self._progress_end()
                out_file = filedialog.asksaveasfilename(
                    parent=self.root,
                    title="“%s”需要指定输出文件" % printer_name,
                    defaultextension=".pdf",
                    filetypes=[("PDF 文件", "*.pdf"), ("所有文件", "*.*")])
                self._progress_begin("正在打印", total, cancellable=False)
                if not out_file:
                    self.status.config(text="已取消打印")
                    return
                hdc.StartDoc("A4 Photo Layout", out_file)
                target_note = "（已输出到：%s）" % out_file
            else:
                target_note = ""
            try:
                for page_idx in range(total):
                    self._progress_step(page_idx + 1, "正在打印第 %d / %d 页…" % (page_idx + 1, total))

                    page_img = render_page_raster(
                        self.images, page_idx, dpi_x, self.rows, self.cols,
                        self.margin_mm, self.padding_mm)

                    # 等比缩放，居中放进可打印区域
                    factor = min(area_w / float(page_img.width),
                                 area_h / float(page_img.height))
                    draw_w = max(1, int(page_img.width * factor))
                    draw_h = max(1, int(page_img.height * factor))
                    x0 = max(0, (area_w - draw_w) // 2)
                    y0 = max(0, (area_h - draw_h) // 2)

                    hdc.StartPage()
                    try:
                        self._draw_page_on_dc(hdc, page_img,
                                              (x0, y0, x0 + draw_w, y0 + draw_h))
                    finally:
                        hdc.EndPage()
                    page_img.close()
            finally:
                hdc.EndDoc()

            self._progress_end()
            self.status.config(text="打印任务已发送：%d 页 → %s" % (total, printer_name))
            messagebox.showinfo("打印完成",
                                "已将 %d 页发送到打印机：\n%s\n%s"
                                % (total, printer_name, target_note))
        except Exception as e:
            self._progress_end()
            self.status.config(text="打印失败")
            messagebox.showerror("打印失败",
                                 "无法打印到：\n%s\n\n%s" % (printer_name, e))
        finally:
            if hdc is not None:
                try:
                    hdc.DeleteDC()
                except Exception:
                    pass


# ==============================================================
# 启动
# ==============================================================
def main():
    try:
        root = TkinterDnD.Tk() if DND_AVAILABLE else Tk()
        PhotoLayoutApp(root)
        root.mainloop()
    except Exception as e:
        traceback.print_exc()
        try:
            messagebox.showerror("致命错误",
                                 "程序启动失败：\n%s\n\n请从命令行运行以查看详细错误。" % e)
        except Exception:
            pass
        sys.exit(1)


if __name__ == "__main__":
    main()
