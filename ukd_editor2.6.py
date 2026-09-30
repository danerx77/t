import sys
import os
import json
import glob
import re
import difflib
import struct

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListWidget, QTableWidget, QTableWidgetItem, QDialog, QLabel,
    QTextEdit, QPushButton, QGroupBox, QHeaderView, QFileDialog,
    QSplitter, QStatusBar, QLineEdit, QSpinBox, QMessageBox,
    QListWidgetItem, QAbstractItemView, QCheckBox, QMenu
)
from PySide6.QtCore import Qt
from PySide6.QtGui import (
    QColor, QFont, QDragEnterEvent, QDropEvent, QSyntaxHighlighter,
    QTextCharFormat, QAction, QShortcut, QKeySequence
)

# --- STYLIZACJE ---
DARK_STYLE = """
QWidget { background-color: #1e1f22; color: #d0d0d0; font-family: 'Segoe UI', Arial, sans-serif; font-size: 14px; }
QPushButton { background-color: #3574f0; color: white; border: none; border-radius: 6px; padding: 6px 12px; font-weight: bold; }
QPushButton:hover { background-color: #4b85f2; }
QPushButton#danger { background-color: #d9534f; }
QPushButton#danger:hover { background-color: #e86a66; }
QPushButton#secondary { background-color: #4a4d52; }
QPushButton#secondary:hover { background-color: #5b5f66; }
QPushButton#success { background-color: #43a047; }
QPushButton#success:hover { background-color: #4caf50; }
QPushButton#token { background-color: #2b2d30; border: 1px solid #3a3d42; color: #8fb1ff; font-weight: bold; }
QPushButton#token:hover { background-color: #3574f0; color: white; }
QLineEdit, QTextEdit, QSpinBox { background-color: #2b2d30; border: 1px solid #3a3d42; border-radius: 6px; padding: 6px; color: #e0e0e0; }
QTextEdit#mainEditor { font-size: 15px; line-height: 1.5; font-family: 'Consolas', monospace; }
QListWidget, QTableWidget { background-color: #2b2d30; border: 1px solid #3a3d42; border-radius: 6px; alternate-background-color: #31343a; }
QListWidget::item { padding: 7px; border-bottom: 1px solid #393b40; }
QListWidget::item:selected, QTableWidget::item:selected { background-color: #2f65ca; color: white; }
QHeaderView::section { background-color: #1b1c1f; color: #8fb1ff; padding: 7px; border: none; border-right: 1px solid #3a3d42; border-bottom: 1px solid #3a3d42; font-weight: bold; }
QGroupBox { border: 1px solid #3a3d42; border-radius: 6px; margin-top: 14px; color: #8fb1ff; font-weight: bold; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 4px 0 4px; }
QStatusBar { background-color: #1b1c1f; color: #9bb0c9; font-weight: bold; }
QMenuBar { background-color: #1b1c1f; color: #d0d0d0; }
QMenuBar::item:selected { background-color: #3574f0; }
QMenu { background-color: #2b2d30; color: #d0d0d0; border: 1px solid #3a3d42; }
QMenu::item:selected { background-color: #3574f0; }
"""

LIGHT_STYLE = """
QWidget { background-color: #f3f4f6; color: #1f2937; font-family: 'Segoe UI', Arial, sans-serif; font-size: 14px; }
QPushButton { background-color: #3b82f6; color: white; border: none; border-radius: 6px; padding: 6px 12px; font-weight: bold; }
QPushButton:hover { background-color: #2563eb; }
QPushButton#danger { background-color: #ef4444; }
QPushButton#danger:hover { background-color: #dc2626; }
QPushButton#secondary { background-color: #9ca3af; }
QPushButton#secondary:hover { background-color: #6b7280; }
QPushButton#success { background-color: #10b981; }
QPushButton#success:hover { background-color: #059669; }
QPushButton#token { background-color: #e5e7eb; border: 1px solid #d1d5db; color: #2563eb; font-weight: bold; }
QPushButton#token:hover { background-color: #3b82f6; color: white; }
QLineEdit, QTextEdit, QSpinBox { background-color: #ffffff; border: 1px solid #d1d5db; border-radius: 6px; padding: 6px; color: #111827; }
QTextEdit#mainEditor { font-size: 15px; line-height: 1.5; font-family: 'Consolas', monospace; }
QListWidget, QTableWidget { background-color: #ffffff; border: 1px solid #d1d5db; border-radius: 6px; alternate-background-color: #f9fafb; }
QListWidget::item { padding: 7px; border-bottom: 1px solid #e5e7eb; }
QListWidget::item:selected, QTableWidget::item:selected { background-color: #3b82f6; color: white; }
QHeaderView::section { background-color: #e5e7eb; color: #1f2937; padding: 7px; border: none; border-right: 1px solid #d1d5db; border-bottom: 1px solid #d1d5db; font-weight: bold; }
QGroupBox { border: 1px solid #d1d5db; border-radius: 6px; margin-top: 14px; color: #2563eb; font-weight: bold; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 4px 0 4px; }
QStatusBar { background-color: #e5e7eb; color: #374151; font-weight: bold; }
QMenuBar { background-color: #e5e7eb; color: #1f2937; }
QMenuBar::item:selected { background-color: #3b82f6; color: white;}
QMenu { background-color: #ffffff; color: #1f2937; border: 1px solid #d1d5db; }
QMenu::item:selected { background-color: #3b82f6; color: white;}
"""


# ==============================================================================
# UKDPARSER (LOGIKA NIEZMIENIONA)
# ==============================================================================
class UKDParser:
    POINTER_UNIT_U16 = 2

    DISPLAY_MAP = {
        0x002B: ',', 0x002D: '.', 0x002C: '-', 0x0026: "'",
        0x0022: '"', 0x0027: '(', 0x0028: ')', 0x005C: "'",
    }
    # Odwrotna mapa: przy duplikatach (apostrof ma 2 kody: 0x0026 i 0x005C)
    # wygrywa PIERWSZY z DISPLAY_MAP (0x0026) - ten faktycznie używany przez grę.
    REVERSE_DISPLAY = {}
    for _k, _v in DISPLAY_MAP.items():
        REVERSE_DISPLAY.setdefault(_v, _k)
    del _k, _v

    SPECIAL_CHARS = {
        0x016D: '…', 0x01A9: 'é', 0x0181: 'Á', 0x0180: 'À', 0x0182: 'Â', 0x0184: 'Ä',
        0x0187: 'Ç', 0x0189: 'É', 0x0188: 'È', 0x018A: 'Ê', 0x018B: 'Ë',
        0x018D: 'Í', 0x018C: 'Ì', 0x018E: 'Î', 0x018F: 'Ï',
        0x0191: 'Ñ', 0x0193: 'Ó', 0x0192: 'Ò', 0x0194: 'Ô', 0x0196: 'Ö',
        0x017C: 'Ø', 0x019A: 'Ú', 0x0199: 'Ù', 0x019B: 'Û', 0x019C: 'Ü',
        0x019F: 'ß', 0x01A1: 'á', 0x01A0: 'à', 0x01A2: 'â', 0x01A4: 'ä',
        0x01A7: 'ç', 0x01A8: 'è', 0x01AA: 'ê', 0x01AB: 'ë',
        0x01AD: 'í', 0x01AC: 'ì', 0x01AE: 'î', 0x01AF: 'ï',
        0x01B1: 'ñ', 0x01B3: 'ó', 0x01B2: 'ò', 0x01B4: 'ô', 0x01B6: 'ö',
        0x017D: 'ø', 0x01BA: 'ú', 0x01B9: 'ù', 0x01BB: 'û', 0x01BC: 'ü',
        0x0161: '¡', 0x017F: '¿', 0x0149: '♂', 0x0148: '♀',
        0x017B: '°', 0x0152: '♪', 0x016B: '×', 0x0156: '÷',
    }
    REVERSE_SPECIAL = {v: k for k, v in SPECIAL_CHARS.items()}

    def __init__(self):
        self.filepath = None
        self.entries = []
        self.original_entries = []
        self.original_data = b''
        self.header_size = 0
        self.header_flags = b''
        self.pointer_table = []
        self.original_pointer_table = []
        self.pointer_count = 0
        self.data_section_start = 0
        self.text_data_buffer = []
        self.entry_positions = []
        self.raw_entries = []
        self.entry_count = 0
        self.buffer_segments = []
        self.pointer_to_entry = {}
        self.original_slack = {}

    def parse_file(self, filepath):
        self.filepath = filepath
        with open(filepath, 'rb') as f: self.original_data = f.read()
        return self.parse_data(self.original_data)

    def parse_data(self, data, preserve_limits=False):
        if not preserve_limits: self.original_slack = {}
        self.entries = []; self.original_entries = []
        self.pointer_table = []; self.original_pointer_table = []
        self.raw_entries = []; self.entry_positions = []
        self.buffer_segments = []; self.pointer_to_entry = {}
        if len(data) < 8: raise ValueError("File too short")
        self.header_size = struct.unpack_from('<I', data, 0)[0]
        self.header_flags = data[4:8]
        self.data_section_start = 4 + self.header_size
        if self.header_size < 4: raise ValueError(f"Invalid header size: {self.header_size}")
        self.pointer_count = (self.header_size - 4) // 2
        for i in range(self.pointer_count):
            pos = 8 + i * 2
            if pos + 2 > len(data): break
            ptr_val = struct.unpack_from('<H', data, pos)[0]
            self.pointer_table.append(ptr_val)
            self.original_pointer_table.append(ptr_val)
        self.text_data_buffer = []
        pos = self.data_section_start
        while pos + 1 < len(data):
            self.text_data_buffer.append(struct.unpack_from('<H', data, pos)[0])
            pos += 2
        self._split_by_null()
        self._map_pointers_to_entries()
        if not preserve_limits: self._calc_hard_limits()
        return self.entries

    def _calc_hard_limits(self):
        self.original_slack = {}
        for idx in range(len(self.entries)):
            orig_len = 0
            if idx < len(self.entry_positions):
                s, e = self.entry_positions[idx]
                orig_len = e - s
            na = self._null_after_entry(idx)
            self.original_slack[idx] = (orig_len, na)

    def _null_after_entry(self, idx):
        for si, (stype, sval) in enumerate(self.buffer_segments):
            if stype == 'entry' and sval == idx:
                if si + 1 < len(self.buffer_segments) and self.buffer_segments[si + 1][0] == 'null':
                    return self.buffer_segments[si + 1][1]
                return 0
        return 0

    def _safe_max_len_no_shift(self, idx):
        if idx < 0 or idx >= len(self.entries): return 0
        orig_len = 0
        if idx < len(self.entry_positions):
            s, e = self.entry_positions[idx]
            orig_len = e - s
        null_after = self._null_after_entry(idx)
        min_null = 0
        for si, (stype, sval) in enumerate(self.buffer_segments):
            if stype == 'entry' and sval == idx:
                null_si = si + 1 if (si + 1 < len(self.buffer_segments) and self.buffer_segments[si + 1][0] == 'null') else None
                if null_si is not None and null_si + 1 < len(self.buffer_segments) and self.buffer_segments[null_si + 1][0] == 'entry':
                    min_null = 1
                break
        return orig_len + max(0, null_after - min_null)

    def _split_by_null(self):
        self.entries = []; self.original_entries = []; self.raw_entries = []
        self.entry_positions = []; self.buffer_segments = []
        buf = self.text_data_buffer
        i = 0
        while i < len(buf):
            null_count = 0
            while i < len(buf) and buf[i] == 0x0000:
                null_count += 1; i += 1
            if null_count > 0: self.buffer_segments.append(('null', null_count))
            if i >= len(buf): break
            start = i
            while i < len(buf) and buf[i] != 0x0000: i += 1
            if i > start:
                entry_idx = len(self.raw_entries)
                raw_data = list(buf[start:i])
                self.raw_entries.append(raw_data)
                self.entry_positions.append((start, i))
                decoded = self._decode(raw_data)
                self.entries.append(decoded)
                self.original_entries.append(decoded)
                self.buffer_segments.append(('entry', entry_idx))
        self.entry_count = len(self.entries)

    def _ptr_to_bufpos(self, ptr_val): return int(ptr_val) * self.POINTER_UNIT_U16

    def _bufpos_to_ptr(self, buf_pos):
        buf_pos = int(buf_pos)
        if buf_pos % self.POINTER_UNIT_U16 != 0: buf_pos -= 1
        ptr = buf_pos // self.POINTER_UNIT_U16
        if not (0 <= ptr <= 0xFFFF): raise ValueError(f"Pointer {ptr} poza zakresem 0..65535")
        return ptr

    def _align_pointer_target(self, pos, buf=None):
        pos = int(pos)
        if pos % self.POINTER_UNIT_U16 == 0: return pos
        ctrl = {0x0000, 0x0002, 0x0003, 0x0004, 0x0005, 0x000A, 0x000C, 0x000D, 0x0018}
        candidates = [pos - 1, pos + 1]
        if buf is not None:
            for c in candidates:
                if 0 <= c < len(buf) and buf[c] not in ctrl: return c
        return max(0, pos - 1)

    def _map_pointers_to_entries(self):
        self.pointer_to_entry = {}
        for pi, ptr_val in enumerate(self.pointer_table):
            ptr_pos = self._ptr_to_bufpos(ptr_val)
            found = False
            for ei, (start, end) in enumerate(self.entry_positions):
                if start <= ptr_pos < end:
                    self.pointer_to_entry[pi] = (ei, ptr_pos - start)
                    found = True; break
            if not found:
                for ei, (start, _end) in enumerate(self.entry_positions):
                    if ptr_pos == start:
                        self.pointer_to_entry[pi] = (ei, 0)
                        found = True; break
            if not found: self.pointer_to_entry[pi] = None

    def _decode(self, a):
        r = []; i = 0
        while i < len(a):
            v = a[i]
            if v == 0x000A: r.append('\n')
            elif v == 0x000D:
                if i + 1 < len(a) and a[i + 1] == 0x000C:
                    r.append('[PAGE]'); i += 1
                else: r.append('\r')
            elif v == 0x000C: r.append('[0C]')
            elif v == 0x0018: r.append('[BOX]')
            elif v == 0xFF10:
                if i + 1 < len(a) and a[i + 1] == 0x0010:
                    r.append('[SYS]'); i += 1
                else: r.append(f'[{v:04X}]')
            elif v == 0x0002:
                p = []; i += 1
                while i < len(a) and a[i] != 0x0003:
                    p.append(a[i]); i += 1
                if len(p) >= 1:
                    if p[0] == 0x0101: r.append('[PLAYER]')
                    elif p[0] == 0x0207 and len(p) >= 2: r.append(f'[POKEMON:{p[1]:04X}]')
                    else: r.append(f'[VAR:{"*".join(f"{x:04X}" for x in p)}]')
                else: r.append('[VAR]')
            elif v == 0x0004:
                nc = []; i += 1
                while i < len(a) and a[i] != 0x0005:
                    x = a[i]
                    if x in self.SPECIAL_CHARS: nc.append(self.SPECIAL_CHARS[x])
                    elif x in self.DISPLAY_MAP: nc.append(self.DISPLAY_MAP[x])
                    elif 0x20 <= x <= 0x7E: nc.append(chr(x))
                    else: nc.append(f'[{x:04X}]')
                    i += 1
                r.append(f'[SPEAKER:{"".join(nc)}]')
            elif v in (0x0005, 0x0003): pass
            elif v in self.SPECIAL_CHARS: r.append(self.SPECIAL_CHARS[v])
            elif v in self.DISPLAY_MAP: r.append(self.DISPLAY_MAP[v])
            elif 0x20 <= v <= 0x7E: r.append(chr(v))
            else: r.append(f'[{v:04X}]')
            i += 1
        return ''.join(r)

    def _encode(self, text):
        r = []; i = 0
        while i < len(text):
            c = text[i]
            if c == '[':
                e = text.find(']', i)
                if e == -1:
                    r.append(self._ec(c)); i += 1; continue
                tag = text[i + 1:e]
                if tag == 'SYS': r.extend([0xFF10, 0x0010])
                elif tag == 'PAGE': r.extend([0x000D, 0x000C])
                elif tag == 'BOX': r.append(0x0018)
                elif tag == 'PLAYER': r.extend([0x0002, 0x0101, 0x0003])
                elif tag.startswith('POKEMON:'): r.extend([0x0002, 0x0207, int(tag.split(':', 1)[1], 16), 0x0003])
                elif tag.startswith('VAR:'):
                    r.append(0x0002)
                    body = tag.split(':', 1)[1]
                    if body:
                        for p in body.split('*'):
                            if p: r.append(int(p, 16))
                    r.append(0x0003)
                elif tag == 'VAR': r.extend([0x0002, 0x0003])
                elif tag.startswith('SPEAKER:'):
                    n = tag.split(':', 1)[1]
                    r.append(0x0004)
                    for ch in n: r.append(self._ec(ch))
                    r.append(0x0005)
                elif tag == '0C': r.append(0x000C)
                else:
                    try: r.append(int(tag, 16))
                    except ValueError:
                        for ch in f'[{tag}]': r.append(self._ec(ch))
                i = e + 1
            elif c == '\n': r.append(0x000A); i += 1
            elif c == '\r': r.append(0x000D); i += 1
            else: r.append(self._ec(c)); i += 1
        return r

    def _ec(self, c):
        if c in self.REVERSE_SPECIAL: return self.REVERSE_SPECIAL[c]
        if c in self.REVERSE_DISPLAY: return self.REVERSE_DISPLAY[c]
        return ord(c)

    def set_pointer(self, ptr_index, new_value):
        if 0 <= ptr_index < len(self.pointer_table):
            if not (0 <= int(new_value) <= 0xFFFF): raise ValueError("Pointer poza zakresem 0..65535")
            self.pointer_table[ptr_index] = int(new_value)
            self._map_pointers_to_entries()

    def get_entry_start(self, entry_idx):
        if 0 <= entry_idx < len(self.entry_positions): return self._bufpos_to_ptr(self.entry_positions[entry_idx][0])
        return None

    def _remap_ptr(self, old_off, old_raw, new_raw):
        if old_off <= 0: return 0
        if not new_raw: return 0
        if not old_raw: return min(old_off, len(new_raw) - 1)
        old_off = min(old_off, len(old_raw) - 1)
        sm = difflib.SequenceMatcher(a=old_raw, b=new_raw, autojunk=False)
        last_old = 0; last_new = 0
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if old_off < i1:
                delta = old_off - last_old
                return max(0, min(last_new + delta, len(new_raw) - 1))
            if i1 <= old_off < i2:
                if tag == 'equal': return max(0, min(j1 + (old_off - i1), len(new_raw) - 1))
                if tag == 'replace':
                    rel = old_off - i1
                    if i2 > i1 and j2 > j1: mapped = j1 + int(rel * (j2 - j1) / max(1, i2 - i1))
                    else: mapped = j1
                    return max(0, min(mapped, len(new_raw) - 1))
                if tag == 'delete': return max(0, min(j1, len(new_raw) - 1))
            last_old = i2; last_new = j2
        for length in range(min(24, len(old_raw) - old_off), 3, -1):
            pattern = old_raw[old_off:old_off + length]
            if not pattern: continue
            old_rank = 0
            for k in range(0, max(0, old_off - length + 1)):
                if old_raw[k:k + length] == pattern: old_rank += 1
            seen = 0
            for j in range(len(new_raw) - length + 1):
                if new_raw[j:j + length] == pattern:
                    if seen == old_rank: return j
                    seen += 1
        ratio = old_off / max(1, len(old_raw))
        return min(int(ratio * len(new_raw)), max(0, len(new_raw) - 1))

    def _remap_null_pointer(self, old_ptr, new_entry_starts, new_entry_ends):
        best_entry = -1; best_old_end = -1
        for ei, (_start, end) in enumerate(self.entry_positions):
            if end <= old_ptr and end > best_old_end:
                best_entry = ei; best_old_end = end
        if best_entry >= 0 and best_entry in new_entry_ends:
            delta = old_ptr - best_old_end
            return new_entry_ends[best_entry] + delta
        return old_ptr

    def save_file(self, filepath):
        changed = set()
        for i in range(len(self.entries)):
            if i >= len(self.original_entries) or self.entries[i] != self.original_entries[i]: changed.add(i)
        pointer_changed = self.pointer_table != self.original_pointer_table
        if not changed and not pointer_changed:
            with open(filepath, 'wb') as f: f.write(self.original_data)
            return
        # KLUCZOWE: koduj od nowa TYLKO zmienione wpisy.
        # Niezmienione wpisy zachowują oryginalne bajty 1:1 (żadnego rekodowania,
        # które mogłoby podmienić np. 0x0026 na 0x005C dla apostrofu).
        all_enc = {}
        for i in range(len(self.entries)):
            if i in changed:
                all_enc[i] = self._encode(self.entries[i])
            elif i < len(self.raw_entries):
                all_enc[i] = list(self.raw_entries[i])
            else:
                all_enc[i] = self._encode(self.entries[i])
        null_adj = {}
        seg = self.buffer_segments
        for si, (stype, sval) in enumerate(seg):
            if stype != 'entry': continue
            ei = sval
            orig_len = (self.entry_positions[ei][1] - self.entry_positions[ei][0] if ei < len(self.entry_positions) else 0)
            raw = all_enc.get(ei, list(self.raw_entries[ei]) if ei < len(self.raw_entries) else [])
            new_len = len(raw)
            null_si = si + 1 if (si + 1 < len(seg) and seg[si + 1][0] == 'null') else None
            delta = new_len - orig_len
            if null_si is not None:
                if delta > 0:
                    orig_null = seg[null_si][1]
                    min_null = 1 if (null_si + 1 < len(seg) and seg[null_si + 1][0] == 'entry') else 0
                    absorbed = min(delta, max(0, orig_null - min_null))
                    if absorbed > 0: null_adj[null_si] = null_adj.get(null_si, 0) - absorbed
                elif delta < 0: null_adj[null_si] = null_adj.get(null_si, 0) + (-delta)
        new_buf = []; new_starts = {}; new_ends = {}
        for si, (stype, sval) in enumerate(seg):
            if stype == 'null':
                count = sval + null_adj.get(si, 0)
                if count > 0: new_buf.extend([0] * count)
            else:
                ei = sval
                if len(new_buf) % self.POINTER_UNIT_U16 != 0: new_buf.append(0)
                raw = all_enc.get(ei, list(self.raw_entries[ei]) if ei < len(self.raw_entries) else [])
                new_starts[ei] = len(new_buf)
                new_buf.extend(raw)
                new_ends[ei] = len(new_buf)
        new_ptrs = []
        for pi in range(len(self.pointer_table)):
            old_ptr = self.pointer_table[pi]
            mapping = self.pointer_to_entry.get(pi)
            if mapping is not None:
                ei, old_off = mapping
                if ei not in new_starts: new_ptr = old_ptr
                else:
                    ns = new_starts[ei]
                    if ei in changed:
                        old_raw = self.raw_entries[ei] if ei < len(self.raw_entries) else []
                        new_raw = all_enc[ei]
                        new_off = self._remap_ptr(old_off, old_raw, new_raw)
                    else: new_off = old_off
                    nl = new_ends[ei] - ns
                    new_off = min(new_off, nl - 1) if nl > 0 else 0
                    new_ptr = ns + new_off
            else: new_ptr = self._remap_null_pointer(self._ptr_to_bufpos(old_ptr), new_starts, new_ends)
            new_ptr = self._align_pointer_target(new_ptr, new_buf)
            stored_ptr = self._bufpos_to_ptr(new_ptr)
            new_ptrs.append(stored_ptr)
        out = bytearray()
        out.extend(struct.pack('<I', self.header_size))
        out.extend(self.header_flags)
        for ptr in new_ptrs: out.extend(struct.pack('<H', ptr))
        written = 4 + 4 + len(new_ptrs) * 2
        expected = 4 + self.header_size
        if written < expected: out.extend(b'\x00' * (expected - written))
        elif written > expected: raise ValueError("Header/pointer table większy niż header_size")
        for val in new_buf:
            if not (0 <= val <= 0xFFFF): raise ValueError(f"Token poza zakresem u16: {val}")
            out.extend(struct.pack('<H', val))
        with open(filepath, 'wb') as f: f.write(out)
        self.filepath = filepath
        self.original_data = bytes(out)
        self.parse_data(self.original_data, preserve_limits=True)

    def get_entry_slack(self, idx):
        if idx < 0 or idx >= len(self.entries): return 0, 0, 0, 0
        if self.original_slack and idx in self.original_slack: orig_len, na = self.original_slack[idx]
        else:
            orig_len = 0
            if idx < len(self.entry_positions):
                s, e = self.entry_positions[idx]
                orig_len = e - s
            na = self._null_after_entry(idx)
        new_len = len(self._encode(self.entries[idx]))
        safe_max = self._safe_max_len_no_shift(idx)
        can_grow = max(0, safe_max - new_len)
        return orig_len, new_len, na, can_grow

    def get_length_info(self, idx):
        if idx < 0 or idx >= len(self.entries): return 0, 0
        orig = 0
        if idx < len(self.entry_positions):
            s, e = self.entry_positions[idx]
            orig = e - s
        return orig, len(self._encode(self.entries[idx]))

    def export_to_txt(self, fp):
        with open(fp, 'w', encoding='utf-8') as f:
            for i, e in enumerate(self.entries): f.write(f'=== Entry {i} ===\n{e}\n\n')

    def export_to_json(self, fp):
        with open(fp, 'w', encoding='utf-8') as f:
            json.dump({'format': 'UKD', 'entry_count': len(self.entries),
                       'entries': [{'index': i, 'text': e} for i, e in enumerate(self.entries)]},
                      f, ensure_ascii=False, indent=2)

    def import_from_txt(self, fp):
        with open(fp, 'r', encoding='utf-8') as f: c = f.read()
        new_entries = []
        for p in c.split('=== Entry ')[1:]:
            ls = p.split('\n', 1)
            if len(ls) > 1:
                text = ls[1]
                if text.endswith('\n\n'): text = text[:-2]
                new_entries.append(text.strip())
        self.entries = new_entries
        self.entry_count = len(self.entries)

    def import_from_json(self, fp):
        with open(fp, 'r', encoding='utf-8') as f: d = json.load(f)
        if isinstance(d, dict) and 'entries' in d:
            items = d['entries']
        elif isinstance(d, list):
            items = d
        else:
            raise ValueError("Nieznany format JSON (oczekiwano klucza 'entries' lub listy)")
        new_entries = []
        for e in items:
            if isinstance(e, dict): new_entries.append(str(e.get('text', '')))
            else: new_entries.append(str(e))
        self.entries = new_entries
        self.entry_count = len(self.entries)

    def _char_for_val(self, v):
        if v in self.SPECIAL_CHARS: return self.SPECIAL_CHARS[v]
        if v in self.DISPLAY_MAP: return self.DISPLAY_MAP[v]
        if 0x20 <= v <= 0x7E: return chr(v)
        if v == 0x0A: return '↵'
        if v == 0x18: return '□'
        return '·'

    def get_raw_hex(self, idx):
        if idx < 0 or idx >= len(self.raw_entries): return "No data"
        raw = self.raw_entries[idx]
        ls = []
        if idx < len(self.entry_positions):
            s, e = self.entry_positions[idx]
            ls.extend([
                f"Entry #{idx}", f"Buf[{s}..{e}] ({e - s} u16)", f"File: 0x{self.data_section_start + s * 2:04X}",
                "", "Pointers to this entry:"
            ])
            for pi, mapping in self.pointer_to_entry.items():
                if mapping and mapping[0] == idx:
                    _ei, off = mapping
                    ls.append(f"  ptr[{pi}] -> offset {off} {'(START)' if off == 0 else ''}")
            ls.append("")
        for j in range(0, len(raw), 8):
            ch = raw[j:j + 8]
            hx = ' '.join(f'{v:04X}' for v in ch)
            cs = ''.join(self._char_for_val(v) for v in ch)
            ls.append(f'{j * 2:04X}: {hx:<40s} │ {cs}')
        return '\n'.join(ls)

    def debug_entry(self, idx):
        if idx < 0 or idx >= len(self.raw_entries): return f"Invalid index {idx}"
        raw = self.raw_entries[idx]
        start, end = self.entry_positions[idx]
        lines = [
            f"=== DEBUG Entry {idx} ===", f"Buffer position: [{start}..{end}]",
            f"Raw length: {len(raw)} u16", f"First 10 values: {[f'{v:04X}' for v in raw[:10]]}",
            f"Decoded text: {self.entries[idx][:120]}...", "", "=== Buffer context around start ===",
        ]
        buf = self.text_data_buffer
        ctx_start = max(0, start - 5); ctx_end = min(len(buf), end + 5)
        for j in range(ctx_start, ctx_end):
            marker = ">>>" if j == start else ("<<<" if j == end else "   ")
            v = buf[j]
            lines.append(f"{marker} buf[{j:4d}] = 0x{v:04X} = {self._char_for_val(v)}")
        lines.append(""); lines.append("=== Pointers to this entry ===")
        for pi, mapping in self.pointer_to_entry.items():
            if mapping and mapping[0] == idx:
                _ei, off = mapping
                ptr_val = self.pointer_table[pi]
                status = "✓ START" if off == 0 else f"offset {off}"
                lines.append(f"  ptr[{pi}] = {ptr_val} -> {status}")
        return '\n'.join(lines)

    def debug_all_pointers(self):
        lines = [
            "=== ALL POINTERS DEBUG ===", f"Total pointers: {len(self.pointer_table)}",
            f"Total entries: {len(self.entries)}", f"Data section start: 0x{self.data_section_start:04X}", "",
        ]
        for pi, ptr_val in enumerate(self.pointer_table):
            mapping = self.pointer_to_entry.get(pi)
            if mapping:
                ei, off = mapping
                if ei < len(self.entry_positions):
                    start, _end = self.entry_positions[ei]
                    abs_pos = start + off
                    if abs_pos < len(self.text_data_buffer):
                        v = self.text_data_buffer[abs_pos]; c = self._char_for_val(v)
                        status = "START" if off == 0 else f"+{off}"
                        lines.append(f"ptr[{pi:3d}] = {ptr_val:5d} -> entry[{ei:2d}] {status:>6} -> '{c}'")
                    else: lines.append(f"ptr[{pi:3d}] = {ptr_val:5d} -> entry[{ei:2d}]+{off} (out)")
            else: lines.append(f"ptr[{pi:3d}] = {ptr_val:5d} -> NULL AREA")
        return '\n'.join(lines)


# ==============================================================================
# TEXTPARSER - samodzielne pliki TXT / JSON (bez pliku binarnego)
# ==============================================================================
class TextParser:
    """Pozwala otwierać i edytować pliki .txt / .json bezpośrednio,
    bez powiązanego pliku UKD/DED. Zapis wraca do tego samego formatu."""
    IS_TEXT = True

    def __init__(self):
        self.filepath = None
        self.fmt = 'txt'
        self.entries = []
        self.original_entries = []
        self.entry_count = 0
        # Atrybuty-zaślepki, żeby UI (struktura, wskaźniki) nie crashowało:
        self.original_data = b''
        self.header_size = 0
        self.pointer_count = 0
        self.pointer_table = []
        self.pointer_to_entry = {}
        self.entry_positions = []
        self.raw_entries = []

    # --- Wczytywanie ---
    def parse_file(self, filepath):
        self.filepath = filepath
        ext = os.path.splitext(filepath)[1].lower()
        self.fmt = 'json' if ext == '.json' else 'txt'
        with open(filepath, 'rb') as f: self.original_data = f.read()
        if self.fmt == 'json': self.import_from_json(filepath)
        else: self.import_from_txt(filepath)
        self.original_entries = list(self.entries)
        return self.entries

    def import_from_txt(self, fp):
        with open(fp, 'r', encoding='utf-8') as f: c = f.read()
        new_entries = []
        if '=== Entry ' in c:
            for p in c.split('=== Entry ')[1:]:
                ls = p.split('\n', 1)
                if len(ls) > 1:
                    text = ls[1]
                    if text.endswith('\n\n'): text = text[:-2]
                    new_entries.append(text.strip())
        else:
            # Zwykły plik tekstowy bez nagłówków - każda linia to wpis
            new_entries = [ln for ln in c.splitlines()]
        self.entries = new_entries
        self.entry_count = len(self.entries)

    def import_from_json(self, fp):
        with open(fp, 'r', encoding='utf-8') as f: d = json.load(f)
        if isinstance(d, dict) and 'entries' in d:
            items = d['entries']
        elif isinstance(d, list):
            items = d
        elif isinstance(d, dict):
            # Słownik klucz->tekst
            items = [str(v) for v in d.values()]
        else:
            raise ValueError("Nieznany format JSON (oczekiwano klucza 'entries' lub listy)")
        new_entries = []
        for e in items:
            if isinstance(e, dict): new_entries.append(str(e.get('text', '')))
            else: new_entries.append(str(e))
        self.entries = new_entries
        self.entry_count = len(self.entries)

    # --- Zapis ---
    def export_to_txt(self, fp):
        with open(fp, 'w', encoding='utf-8') as f:
            for i, e in enumerate(self.entries): f.write(f'=== Entry {i} ===\n{e}\n\n')

    def export_to_json(self, fp):
        with open(fp, 'w', encoding='utf-8') as f:
            json.dump({'format': 'UKD', 'entry_count': len(self.entries),
                       'entries': [{'index': i, 'text': e} for i, e in enumerate(self.entries)]},
                      f, ensure_ascii=False, indent=2)

    def save_file(self, filepath):
        ext = os.path.splitext(filepath)[1].lower()
        fmt = 'json' if ext == '.json' else self.fmt if ext == '' else 'txt'
        if ext == '.json' or (ext == '' and self.fmt == 'json'):
            self.export_to_json(filepath)
        else:
            self.export_to_txt(filepath)
        self.filepath = filepath
        self.original_entries = list(self.entries)
        with open(filepath, 'rb') as f: self.original_data = f.read()

    # --- Metody wymagane przez UI (limity nie obowiązują) ---
    def _encode(self, text): return list(text)

    def _safe_max_len_no_shift(self, idx): return 10 ** 9

    def get_length_info(self, idx):
        if idx < 0 or idx >= len(self.entries): return 0, 0
        orig = len(self.original_entries[idx]) if idx < len(self.original_entries) else 0
        return orig, len(self.entries[idx])

    def get_entry_slack(self, idx):
        o, n = self.get_length_info(idx)
        return o, n, 0, 10 ** 9

    def get_raw_hex(self, idx):
        if idx < 0 or idx >= len(self.entries): return "No data"
        t = self.entries[idx]
        ls = [f"Entry #{idx} (plik tekstowy - brak danych binarnych)",
              f"Length: {len(t)} chars", ""]
        enc = t.encode('utf-8')
        for j in range(0, len(enc), 16):
            ch = enc[j:j + 16]
            hx = ' '.join(f'{b:02X}' for b in ch)
            cs = ''.join(chr(b) if 0x20 <= b <= 0x7E else '·' for b in ch)
            ls.append(f'{j:04X}: {hx:<48s} │ {cs}')
        return '\n'.join(ls)


# ==============================================================================
# OKNO USTAWIEŃ
# ==============================================================================
class SettingsDialog(QDialog):
    def __init__(self, main_window, parent=None):
        super().__init__(parent)
        self.main_window = main_window
        self.setWindowTitle(self.main_window.tr("set_title"))
        self.resize(800, 750)
        layout = QVBoxLayout(self)

        group1 = QGroupBox(self.main_window.tr("set_g1"))
        g1 = QVBoxLayout(group1)

        lbl_var = QLabel(self.main_window.tr("set_lbl_var"))
        lbl_var.setWordWrap(True)
        g1.addWidget(lbl_var)
        self.var_edit = QTextEdit(", ".join(f"[{k}]={v}" for k, v in sorted(main_window.visual_tag_texts.items())))
        self.var_edit.setMaximumHeight(80)
        g1.addWidget(self.var_edit)

        lbl_ign = QLabel(self.main_window.tr("set_lbl_ign"))
        lbl_ign.setWordWrap(True)
        g1.addWidget(lbl_ign)
        self.ignored_edit = QTextEdit(", ".join(f"[{x}]" for x in sorted(main_window.visual_ignore_tags)))
        self.ignored_edit.setMaximumHeight(60)
        g1.addWidget(self.ignored_edit)
        layout.addWidget(group1)

        group2 = QGroupBox(self.main_window.tr("set_g2"))
        g2 = QVBoxLayout(group2)

        self.chk_font = QCheckBox(self.main_window.tr("set_chk_font"))
        self.chk_font.setChecked(main_window.use_font_width_table)
        g2.addWidget(self.chk_font)

        self.chk_pixel = QCheckBox(self.main_window.tr("set_chk_pixel"))
        self.chk_pixel.setChecked(main_window.pixel_mode_enabled)
        g2.addWidget(self.chk_pixel)
        lbl_pixel = QLabel(self.main_window.tr("set_lbl_pixel"))
        lbl_pixel.setWordWrap(True)
        g2.addWidget(lbl_pixel)

        lbl_char = QLabel(self.main_window.tr("set_lbl_char"))
        lbl_char.setWordWrap(True)
        g2.addWidget(lbl_char)

        overrides = main_window._char_width_overrides()
        out_chars = [f"{'SPACE' if k == ' ' else k}={v}" for k, v in sorted(overrides.items())]
        self.char_edit = QTextEdit(", ".join(out_chars))
        self.char_edit.setMaximumHeight(80)
        g2.addWidget(self.char_edit)

        lbl_tag = QLabel(self.main_window.tr("set_lbl_tag"))
        lbl_tag.setWordWrap(True)
        g2.addWidget(lbl_tag)
        self.tag_edit = QTextEdit(", ".join(f"[{k}]={v}" for k, v in sorted(main_window.visual_tag_widths.items())))
        self.tag_edit.setMaximumHeight(80)
        g2.addWidget(self.tag_edit)
        layout.addWidget(group2)

        group3 = QGroupBox(self.main_window.tr("set_g3"))
        g3 = QVBoxLayout(group3)
        self.chk_polish = QCheckBox(self.main_window.tr("set_chk_polish"))
        self.chk_polish.setChecked(main_window.polish_conversion)
        g3.addWidget(self.chk_polish)
        lbl_polish = QLabel(self.main_window.tr("set_lbl_polish"))
        lbl_polish.setWordWrap(True)
        g3.addWidget(lbl_polish)

        lbl_polish_map = QLabel(self.main_window.tr("set_lbl_polish_map"))
        lbl_polish_map.setWordWrap(True)
        g3.addWidget(lbl_polish_map)
        self.polish_map_edit = QTextEdit(
            ", ".join(f"{k}={v}" for k, v in main_window.polish_map.items()))
        self.polish_map_edit.setMaximumHeight(70)
        g3.addWidget(self.polish_map_edit)

        btn_polish_reset = QPushButton(self.main_window.tr("btn_polish_reset"))
        btn_polish_reset.setObjectName("secondary")
        btn_polish_reset.clicked.connect(self._reset_polish_map)
        g3.addWidget(btn_polish_reset)
        layout.addWidget(group3)

        btns = QHBoxLayout()
        btns.addStretch()
        cancel = QPushButton(self.main_window.tr("btn_cancel"))
        cancel.setObjectName("secondary")
        cancel.clicked.connect(self.reject)
        save = QPushButton(self.main_window.tr("btn_save_set"))
        save.setObjectName("success")
        save.clicked.connect(self.save_and_accept)
        btns.addWidget(cancel)
        btns.addWidget(save)
        layout.addLayout(btns)

    def save_and_accept(self):
        # 1. Tagi ignorowane
        ignore = set()
        raw_ign = self.ignored_edit.toPlainText().replace('\n', ',')
        for part in raw_ign.split(','):
            part = part.strip().strip("[]").upper()
            if part: ignore.add(part)
        self.main_window.visual_ignore_tags = ignore

        # PANCERNY PARSER dla [TAG]=WARTOŚĆ
        def robust_parse(text, is_int=False):
            result = {}
            clean_text = text.replace(',', ' ').replace('\n', ' ')
            for match in re.finditer(r'(?:\[)?([^\]=\s]+)(?:\])?\s*=\s*([^\s]+)', clean_text):
                k = match.group(1).strip().upper()
                v = match.group(2).strip()
                if not k: continue
                if is_int:
                    try: result[k] = max(0, int(v))
                    except ValueError: continue
                else:
                    result[k] = v
            return result

        # 2. Zamiana na tekst
        self.main_window.visual_tag_texts = robust_parse(self.var_edit.toPlainText(), is_int=False)
        # 3. Stała szerokość tagów
        self.main_window.visual_tag_widths = robust_parse(self.tag_edit.toPlainText(), is_int=True)
        # 4. Szerokość poszczególnych liter
        self.main_window.use_font_width_table = self.chk_font.isChecked()
        char_weights = self.main_window._default_font_widths() if self.main_window.use_font_width_table else {}

        parsed_chars = robust_parse(self.char_edit.toPlainText(), is_int=True)
        for k, v in parsed_chars.items():
            if k == 'SPACE': k = ' '
            if k: char_weights[k[0]] = v

        self.main_window.visual_char_widths = char_weights

        # 5. Tryb pikselowy i zamiana polskich znaków
        self.main_window.pixel_mode_enabled = self.chk_pixel.isChecked()

        old_polish_on = self.main_window.polish_conversion
        old_map = dict(self.main_window.polish_map)

        # 6. Edytowalna tablica zamiany polskich znaków (format: Ą=À, ć=ç ...)
        new_map = {}
        raw_map = self.polish_map_edit.toPlainText().replace('\n', ',')
        for part in raw_map.split(','):
            if '=' not in part: continue
            k, v = part.split('=', 1)
            k = k.strip(); v = v.strip()
            if len(k) == 1 and len(v) == 1:
                new_map[k] = v
        if new_map:
            self.main_window.polish_map = new_map

        new_polish_on = self.chk_polish.isChecked()

        # Przełącz wyświetlanie w już wczytanych plikach:
        # - włączono -> pokaż zastępcze jako polskie
        # - wyłączono -> wróć do znaków zastępczych
        if old_polish_on != new_polish_on:
            if not new_polish_on:
                # przy wyłączaniu użyj STAREJ mapy (bo nią konwertowano)
                cur = dict(self.main_window.polish_map)
                self.main_window.polish_map = old_map
                self.main_window.polish_conversion = old_polish_on
                self.main_window._toggle_polish_display_all(False)
                self.main_window.polish_map = cur
            self.main_window.polish_conversion = new_polish_on
            if new_polish_on:
                self.main_window._toggle_polish_display_all(True)
        else:
            self.main_window.polish_conversion = new_polish_on

        self.accept()

    def _reset_polish_map(self):
        self.polish_map_edit.setPlainText(
            ", ".join(f"{k}={v}" for k, v in self.main_window.POLISH_TO_SUB.items()))


# ==============================================================================
# HIGHLIGHTER
# ==============================================================================
class UKDHighlighter(QSyntaxHighlighter):
    def __init__(self, document, app_window):
        super().__init__(document)
        self.app_window = app_window
        self.tag_format = QTextCharFormat()
        self.tag_format.setFontWeight(QFont.Bold)
        self.error_format = QTextCharFormat()
        self.error_tag_format = QTextCharFormat()
        self.error_tag_format.setFontWeight(QFont.Bold)
        self.set_theme("dark")

    def set_theme(self, theme):
        if theme == "light":
            tag_color = "#2563eb"
            err_bg = "#ef4444"
            err_fg = "#ffffff"
        else:
            tag_color = "#e5c07b"
            err_bg = "#991b1b"
            err_fg = "#ffffff"
        self.tag_format.setForeground(QColor(tag_color))
        self.error_format.setForeground(QColor(err_fg))
        self.error_format.setBackground(QColor(err_bg))
        self.error_tag_format.setForeground(QColor(tag_color))
        self.error_tag_format.setBackground(QColor(err_bg))
        self.rehighlight()

    def highlightBlock(self, text):
        limit = self.app_window._visual_limit_width()
        current_width = 0
        idx = 0
        while idx < len(text):
            if text[idx] == '[':
                match = re.match(r'^\[.*?\]', text[idx:])
                if match:
                    full_tag = match.group(0)
                    tag_len = len(full_tag)
                    tag_core = full_tag[1:-1]
                    w = self.app_window._tag_visual_width(tag_core)
                    current_width += w
                    if current_width > limit: self.setFormat(idx, tag_len, self.error_tag_format)
                    else: self.setFormat(idx, tag_len, self.tag_format)
                    idx += tag_len
                    continue
            w = self.app_window._char_width(text[idx])
            current_width += w
            if current_width > limit: self.setFormat(idx, 1, self.error_format)
            idx += 1


# ==============================================================================
# GUI MAIN WINDOW
# ==============================================================================
class UKDEditorMainWindow(QMainWindow):
    FTYPES_ALL = ("Obsługiwane (*.ukd *.ded *.frd *.esd *.itd *.bin *.dat *.txt *.json);;"
                  "UKD/DED (*.ukd *.ded *.frd *.esd *.itd *.bin *.dat);;"
                  "TXT/JSON (*.txt *.json);;All (*.*)")
    EXTS_ALL = ['.ukd', '.ded', '.frd', '.esd', '.itd', '.bin', '.dat']
    EXTS_IMPORT = ['.txt', '.json']
    DEFAULT_VISUAL_IGNORE_TAGS = ['SYS', '0C', 'BOX', 'PAGE']
    DEFAULT_VISUAL_TAG_WIDTHS = {'VAR:0702*': 10}
    DEFAULT_VISUAL_VAR0702_CODES = [
        '0001', '0004', '0006', '0007', '000A', '000C', '000E', '000F',
        '0011', '0012', '0013', '001D', '0020', '0021', '0022', '0027',
        '0029', '002B', '002C', '002F', '0031', '0032', '0033', '0035',
        '0036', '0037', '0038', '003E', '0041', '0042', '0044', '0046',
        '0047', '0048', '004C', '0051', '0052', '0053', '0059', '005A',
        '005B', '005C', '0068', '0069', '006D', '0070', '0071', '0072',
        '0077', '0078', '007C', '007D', '007E', '007F', '0081', '0082',
        '0083', '0086', '0087', '008B', '008E', '0091', '0093', '0098',
        '0099', '009A', '009B', '009C', '009D', '009F', '00A1', '00A2',
        '00A5', '00AC', '00AD', '00AE', '00B3', '00B4', '00B6', '00B8',
        '00BA', '00BF', '00D2', '00D3', '00D4', '00D5'
    ]
    DEFAULT_VISUAL_TAG_TEXTS = {'VAR:0702*0053': 'Lapras', 'VAR:0702*00D5': 'Deoxys'}
    # Zamiana polskich znaków na "znaki zastępcze" obsługiwane przez font gry
    # ĄĆĘŁŃÓŚŹŻ -> ÀÇÈÊÑÓÙÚÛ (i małe litery analogicznie)
    POLISH_TO_SUB = {
        'Ą': 'À', 'Ć': 'Ç', 'Ę': 'È', 'Ł': 'Ê', 'Ń': 'Ñ',
        'Ó': 'Ó', 'Ś': 'Ù', 'Ź': 'Ú', 'Ż': 'Û',
        'ą': 'à', 'ć': 'ç', 'ę': 'è', 'ł': 'ê', 'ń': 'ñ',
        'ó': 'ó', 'ś': 'ù', 'ź': 'ú', 'ż': 'û',
    }
    SUB_TO_POLISH = {
        'À': 'Ą', 'Ç': 'Ć', 'È': 'Ę', 'Ê': 'Ł', 'Ñ': 'Ń',
        'Ù': 'Ś', 'Ú': 'Ź', 'Û': 'Ż',
        'à': 'ą', 'ç': 'ć', 'è': 'ę', 'ê': 'ł', 'ñ': 'ń',
        'ù': 'ś', 'ú': 'ź', 'û': 'ż',
    }
    FONT_WIDTH_BASE = 0x20
    FONT_WIDTH_STANDARD = 6
    # Brak wbudowanej czcionki - tabelę szerokości wczytuje się z zewnątrz (🔤 Załaduj czcionkę)

    def __init__(self):
        super().__init__()
        self.menu_actions = {}
        self.ui_elements = {}

        self._init_i18n()
        self._load_config()
        self.resize(1400, 900)
        self.setAcceptDrops(True)
        self.file_parsers = {}
        self.current_file = None
        self.current_entry_index = -1
        self.is_updating_ui = False
        self.modified = False
        self.init_ui()
        self.apply_theme()
        self._update_ui_texts()
        self._update_font_status()

    def tr(self, key):
        return self.translations.get(self.current_lang, {}).get(key, key)

    def _init_i18n(self):
        self.translations = {}
        lang_file = "lang.json"

        default_langs = {
            "pl": {
                "title": "UKD & DED Editor - Nowoczesny",
                "menu_file": "Plik",
                "menu_open": "Otwórz pliki...",
                "menu_open_folder": "Otwórz folder...",
                "menu_save": "Zapisz",
                "menu_save_as": "Zapisz jako...",
                "menu_save_all": "Zapisz folder (wszystkie pliki)",
                "menu_imp_exp": "Import / Eksport",
                "menu_exp_txt": "Eksportuj aktualny (TXT)",
                "menu_exp_json": "Eksportuj aktualny (JSON)",
                "menu_b_exp_txt": "Masowy/Zbiorczy Eksport (TXT)",
                "menu_b_exp_json": "Masowy/Zbiorczy Eksport (JSON)",
                "menu_imp_txt": "Importuj do aktualnego (TXT)",
                "menu_imp_json": "Importuj do aktualnego (JSON)",
                "menu_b_imp_txt": "Masowy/Zbiorczy Import (TXT)",
                "menu_b_imp_json": "Masowy/Zbiorczy Import (JSON)",
                "menu_b_imp_dir_txt": "Masowy/Zbiorczy Import folder (TXT)",
                "menu_b_imp_dir_json": "Masowy/Zbiorczy Import folder (JSON)",
                "fd_imp_dir": "Wybierz folder z plikami do importu",
                "msg_imp_dir_nofiles": "Najpierw wczytaj pliki gry (.ukd itd.), do których ma trafić import.",
                "msg_imp_dir_empty": "W wybranym folderze nie znaleziono plików {ext}.",
                "msg_imp_dir_done": "Zaimportowano: {imported} z {found} znalezionych\nPominięto (brak pasującego pliku): {skipped}\nBłędy: {errors}",
                "msg_imp_dir_skipped": "Pominięte (nie znaleziono wczytanego pliku o tej nazwie):",
                "menu_transfer": "Przenieś wpis do innego pliku językowego...",
                "menu_b_transfer": "Masowy transfer przenoszenie folderu (UKD → FRD)...",
                "menu_exit": "Zakończ program",
                "menu_edit": "Edycja",
                "menu_undo": "↩ Cofnij (Ctrl+Z)",
                "menu_redo": "↪ Ponów (Ctrl+Y)",
                "menu_remove_file": "🗑 Usuń zaznaczone pliki z listy (Delete)",
                "ctx_remove_file": "🗑 Usuń z listy ({count})",
                "msg_remove_unsaved": "Te pliki mają niezapisane zmiany:\n{names}\n\nUsunąć z listy mimo to? (zmiany przepadną, plik na dysku zostaje)",
                "msg_files_removed": "Usunięto z listy: {count} (pliki na dysku nietknięte)",
                "menu_mass_search": "Masowe wyszukiwanie",
                "menu_edit_pointers": "Edytor wskaźników (Pointers)",
                "menu_view": "Widok",
                "menu_hex": "Podgląd Hex",
                "menu_struct": "Struktura pliku",
                "menu_lang": "Język (Language)",
                "btn_files": "📄 Pliki",
                "btn_folder": "📁 Folder",
                "btn_save": "💾 Zapisz",
                "btn_save_all": "💾📁 Zapisz folder",
                "btn_settings": "⚙️ Ustawienia",
                "btn_pointers": "📍 Wskaźniki",
                "btn_clear": "🗑 Wyczyść",
                "lbl_limit": "Limit MAX znaków:",
                "lbl_limit_px": "Limit szerokości (piksele):",
                "search_file": "🔍 Szukaj pliku...",
                "search_text": "🌐 Szukaj w tekstach...",
                "col_id": "ID",
                "col_size": "Rozmiar",
                "col_widest": "Najdłuższa",
                "col_lines": "Linii",
                "col_slack": "Zapas",
                "col_preview": "Podgląd",
                "lbl_editor": "Wybierz wpis z tabeli powyżej, aby edytować.",
                "msg_discard": "Porzucić niezapisane zmiany?",
                "msg_err": "Błąd",
                "msg_ok": "OK",
                "msg_imported_file": "Zaimportowano '{src}' do '{dst}'. Pamiętaj o zapisie (💾).",
                "msg_opened_text": "Otwarto plik tekstowy: {name}",
                "btn_font_load": "🔤 Załaduj czcionkę",
                "btn_font_del": "🔤✖ Usuń czcionkę",
                "fd_font": "Wybierz plik tabeli szerokości czcionki (.dat)",
                "msg_font_loaded": "Załadowano czcionkę '{name}' ({count} znaków).\nSzerokości liter są teraz brane z tego pliku.",
                "msg_font_removed": "Usunięto czcionkę '{name}'.\nZnaki będą liczone jako standardowa szerokość.",
                "msg_font_none": "Nie ma załadowanej czcionki (każdy znak liczony jako standardowa szerokość).",
                "msg_font_active": "Aktywna czcionka: {name}",
                "msg_polish_conv": "🔁 Zamieniono znaki w {count} wpisach",
                "lbl_font_loaded": "✅ Czcionka: {name}",
                "lbl_font_none": "Czcionka: brak (wczytaj plik)",
                "set_title": "⚙️ Ustawienia Znaków i Tagów",
                "set_g1": "Zmienne i ignorowanie (Liczenie znaków)",
                "set_lbl_var": "🔄 Zamiana tagów na tekst (np. [VAR:0702*0053]=Lapras, [SPEAKER:Kid]=Kid):\nPodmienia tag w locie na podane słowo, aby program poprawnie policzył jego szerokość na ekranie.",
                "set_lbl_ign": "🚫 Tagi ignorowane w liczeniu (np. [SYS], [0C], [BOX], [PAGE]):\nProgram potraktuje je jako 0 szerokości.",
                "set_g2": "Zaawansowane wagi i rozmiary",
                "set_chk_font": "Używaj tabeli szerokości z wczytanej czcionki (Zalecane)",
                "set_chk_pixel": "📐 Tryb pikselowy (limit w pikselach zamiast znaków)",
                "set_lbl_pixel": "Po włączeniu limit podajesz w pikselach (np. 222 px) i szerokość tekstu liczona jest z tabeli szerokości czcionki. Po wyłączeniu wraca zwykły limit znaków (np. 37). Ustawienie jest zapamiętywane po restarcie.",
                "set_g3": "Zamiana znaków",
                "set_chk_polish": "🔁 Zamieniaj znaki wg tablicy przy zapisie (.ukd, .ded itd.)",
                "set_lbl_polish": "Przy zapisie do plików gry znaki z lewej kolumny tablicy są podmieniane na znaki z prawej (np. Ą → À). W edytorze piszesz i widzisz znaki z lewej kolumny - także gdy plik gry ma już w środku znaki zastępcze, program wyświetli je wg tablicy. Zamiana działa tylko przy 💾 Zapisz do .ukd/.ded itd. Nie dotyczy .txt/.json, masowego importu ani transferów.",
                "set_lbl_polish_map": "🔧 Tablica zamiany (możesz edytować, format: ZNAK=ZAMIENNIK, np. Ą=À, ć=ç):",
                "btn_polish_reset": "Przywróć domyślną tablicę",
                "set_lbl_char": "📝 Szerokość POSZCZEGÓLNYCH LITER z klawiatury (np. i=1, SPACE=0):\nOkreśla ile pikseli zajmuje litera (dodaj tu wyjątki).",
                "set_lbl_tag": "🏷️ Tagi wstawiające tekst - SZTYWNA SZEROKOŚĆ (np. [PLAYER]=8, [VAR:0702*]=10):",
                "btn_cancel": "Anuluj",
                "btn_save_set": "Zapisz",
                "fd_open": "Wybierz pliki",
                "fd_dir": "Wybierz folder",
                "fd_save_as": "Zapisz jako...",
                "msg_saved_as": "Zapisano jako: {name}",
                "msg_saved_all": "Zapisano plików: {ok}, błędów: {err}",
                "btn_ignore_error": "🔕 Ignoruj błąd",
                "btn_unignore_error": "🔔 Przywróć błąd",
                "lbl_error_ignored": "BŁĄD IGNOROWANY",
                "search_find": "Szukaj...",
                "search_replace": "Zamień na...",
                "search_btn_find": "Szukaj",
                "search_btn_replace": "Zamień wszystko",
                "search_found": "Znaleziono: ",
                "search_replaced": "Zamieniono.",
                "col_text": "Tekst",
                "col_path": "Ścieżka",
                "d_trans_1": "1. Wybierz folder Z TŁUMACZENIEM",
                "d_trans_2": "2. Wybierz folder Z BAZĄ (Oryginalne gry)",
                "d_trans_3": "3. Wybierz PUSTY folder na ZAPIS",
                "d_trans_err": "Nie znaleziono pasujących plików.",
                "d_trans_title": "Zbiorcze przenoszenie w toku..."
            },
            "en": {
                "title": "UKD & DED Editor - Modern",
                "menu_file": "File",
                "menu_open": "Open files...",
                "menu_open_folder": "Open folder...",
                "menu_save": "Save",
                "menu_save_as": "Save as...",
                "menu_save_all": "Save folder (all files)",
                "menu_imp_exp": "Import / Export",
                "menu_exp_txt": "Export current (TXT)",
                "menu_exp_json": "Export current (JSON)",
                "menu_b_exp_txt": "Mass/Batch Export (TXT)",
                "menu_b_exp_json": "Mass/Batch Export (JSON)",
                "menu_imp_txt": "Import to current (TXT)",
                "menu_imp_json": "Import to current (JSON)",
                "menu_b_imp_txt": "Mass/Batch Import (TXT)",
                "menu_b_imp_json": "Mass/Batch Import (JSON)",
                "menu_b_imp_dir_txt": "Mass/Batch Import folder (TXT)",
                "menu_b_imp_dir_json": "Mass/Batch Import folder (JSON)",
                "fd_imp_dir": "Select folder with files to import",
                "msg_imp_dir_nofiles": "First load the game files (.ukd etc.) the import should go into.",
                "msg_imp_dir_empty": "No {ext} files found in the selected folder.",
                "msg_imp_dir_done": "Imported: {imported} of {found} found\nSkipped (no matching file): {skipped}\nErrors: {errors}",
                "msg_imp_dir_skipped": "Skipped (no loaded file with this name):",
                "menu_transfer": "Transfer entry to another language file...",
                "menu_b_transfer": "Mass folder transfer (UKD → FRD)...",
                "menu_exit": "Exit",
                "menu_edit": "Edit",
                "menu_undo": "↩ Undo (Ctrl+Z)",
                "menu_redo": "↪ Redo (Ctrl+Y)",
                "menu_remove_file": "🗑 Remove selected files from list (Delete)",
                "ctx_remove_file": "🗑 Remove from list ({count})",
                "msg_remove_unsaved": "These files have unsaved changes:\n{names}\n\nRemove from list anyway? (changes will be lost, file on disk stays)",
                "msg_files_removed": "Removed from list: {count} (files on disk untouched)",
                "menu_mass_search": "Mass Search",
                "menu_edit_pointers": "Pointer Editor",
                "menu_view": "View",
                "menu_hex": "Hex View",
                "menu_struct": "File Structure",
                "menu_lang": "Language",
                "btn_files": "📄 Files",
                "btn_folder": "📁 Folder",
                "btn_save": "💾 Save",
                "btn_save_all": "💾📁 Save folder",
                "btn_settings": "⚙️ Settings",
                "btn_pointers": "📍 Pointers",
                "btn_clear": "🗑 Clear",
                "lbl_limit": "MAX char limit:",
                "lbl_limit_px": "Width limit (pixels):",
                "search_file": "🔍 Search file...",
                "search_text": "🌐 Search text...",
                "col_id": "ID",
                "col_size": "Size",
                "col_widest": "Widest",
                "col_lines": "Lines",
                "col_slack": "Slack",
                "col_preview": "Preview",
                "lbl_editor": "Select an entry from the table above to edit.",
                "msg_discard": "Discard unsaved changes?",
                "msg_err": "Error",
                "msg_ok": "OK",
                "msg_imported_file": "Imported '{src}' into '{dst}'. Remember to save (💾).",
                "msg_opened_text": "Opened text file: {name}",
                "btn_font_load": "🔤 Load font",
                "btn_font_del": "🔤✖ Remove font",
                "fd_font": "Select font width table file (.dat)",
                "msg_font_loaded": "Loaded font '{name}' ({count} characters).\nLetter widths are now taken from this file.",
                "msg_font_removed": "Removed font '{name}'.\nCharacters will be counted as standard width.",
                "msg_font_none": "No font loaded (every character counted as standard width).",
                "msg_font_active": "Active font: {name}",
                "msg_polish_conv": "🔁 Characters converted in {count} entries",
                "lbl_font_loaded": "✅ Font: {name}",
                "lbl_font_none": "Font: none (load a file)",
                "set_title": "⚙️ Character and Tag Settings",
                "set_g1": "Variables and Ignoring (Character Counting)",
                "set_lbl_var": "🔄 Replace tags with text (e.g. [VAR:0702*0053]=Lapras, [SPEAKER:Kid]=Kid):\nReplaces the tag on the fly with a specific word so the program can calculate screen width correctly.",
                "set_lbl_ign": "🚫 Ignored tags (e.g. [SYS], [0C], [BOX], [PAGE]):\nTreated as having 0 width.",
                "set_g2": "Advanced Weights and Sizes",
                "set_chk_font": "Use width table from loaded font (Recommended)",
                "set_chk_pixel": "📐 Pixel mode (limit in pixels instead of characters)",
                "set_lbl_pixel": "When enabled, the limit is set in pixels (e.g. 222 px) and text width is calculated from the font width table. When disabled, the regular character limit returns (e.g. 37). Remembered after restart.",
                "set_g3": "Character replacement",
                "set_chk_polish": "🔁 Replace characters using the table on save (.ukd, .ded etc.)",
                "set_lbl_polish": "When saving to game files, characters from the left column of the table are replaced with those from the right (e.g. Ą → À). In the editor you type and see the left-column characters - if the game file already contains substitutes, they are displayed according to the table. Conversion happens only on 💾 Save to .ukd/.ded etc. Does not apply to .txt/.json, batch import or transfers.",
                "set_lbl_polish_map": "🔧 Replacement table (editable, format: CHAR=SUBSTITUTE, e.g. Ą=À, ć=ç):",
                "btn_polish_reset": "Restore default table",
                "set_lbl_char": "📝 Width of INDIVIDUAL LETTERS (e.g. i=1, SPACE=0):\nOverrides specific pixel widths.",
                "set_lbl_tag": "🏷️ Text-inserting tags - FIXED WIDTH (e.g. [PLAYER]=8, [VAR:0702*]=10):",
                "btn_cancel": "Cancel",
                "btn_save_set": "Save",
                "fd_open": "Select files",
                "fd_dir": "Select folder",
                "fd_save_as": "Save as...",
                "msg_saved_as": "Saved as: {name}",
                "msg_saved_all": "Files saved: {ok}, errors: {err}",
                "btn_ignore_error": "🔕 Ignore error",
                "btn_unignore_error": "🔔 Restore error",
                "lbl_error_ignored": "ERROR IGNORED",
                "search_find": "Find...",
                "search_replace": "Replace with...",
                "search_btn_find": "Find",
                "search_btn_replace": "Replace All",
                "search_found": "Found: ",
                "search_replaced": "Replaced.",
                "col_text": "Text",
                "col_path": "Path",
                "d_trans_1": "1. Select folder WITH TRANSLATION",
                "d_trans_2": "2. Select BASE folder (Original game files)",
                "d_trans_3": "3. Select EMPTY folder for OUTPUT",
                "d_trans_err": "No matching files found.",
                "d_trans_title": "Batch transfer in progress..."
            }
        }

        # Zapisz/Odczytaj i połącz, by dodać ewentualne brakujące klucze do istniejącego lang.json
        if os.path.exists(lang_file):
            try:
                with open(lang_file, "r", encoding="utf-8") as f:
                    self.translations = json.load(f)
            except: self.translations = {}

        # Klucze, których treść została zmieniona - nadpisz nawet jeśli istnieją w lang.json
        force_update = {
            "set_g3", "set_chk_polish", "set_lbl_polish", "set_lbl_polish_map",
            "set_chk_font", "msg_font_none", "msg_font_removed", "msg_polish_conv",
            "lbl_font_none",
        }
        changed = False
        for lang, keys in default_langs.items():
            if lang not in self.translations:
                self.translations[lang] = keys
                changed = True
            else:
                for k, v in keys.items():
                    if k not in self.translations[lang] or (k in force_update and self.translations[lang][k] != v):
                        self.translations[lang][k] = v
                        changed = True
        if changed:
            try:
                with open(lang_file, "w", encoding="utf-8") as f:
                    json.dump(self.translations, f, ensure_ascii=False, indent=4)
            except: pass

    def _load_config(self):
        self.current_lang = "pl"
        self.theme = "dark"
        self.chars_per_line = 37
        self.pixel_limit = 37 * self.FONT_WIDTH_STANDARD  # limit w pikselach (tryb czcionki)
        self.pixel_mode_enabled = False   # tryb pikselowy - włączany/wyłączany w Ustawieniach
        self.polish_conversion = False    # zamiana ĄĆĘŁ... na ÀÇÈÊ... przy zapisie do .ukd
        self.polish_map = dict(self.POLISH_TO_SUB)  # edytowalna tablica zamiany (Ustawienia)
        self.error_ignores = {}  # {ścieżka_pliku: set(indeksów wpisów z ignorowanym błędem)}
        self.visual_ignore_tags = set(self.DEFAULT_VISUAL_IGNORE_TAGS)
        self.visual_tag_widths = self._default_tag_widths()
        self.visual_tag_texts = {str(k).upper(): str(v) for k, v in self.DEFAULT_VISUAL_TAG_TEXTS.items()}
        self.use_font_width_table = True
        self.custom_font_hex = None
        self.custom_font_name = None
        self.visual_char_widths = self._default_font_widths()

        try:
            if os.path.exists("config.json"):
                with open("config.json", "r", encoding="utf-8") as f:
                    cfg = json.load(f)
                # Własny font (tabela szerokości) - wczytaj PRZED liczeniem widths
                cf_hex = cfg.get("custom_font_hex")
                if cf_hex:
                    self.custom_font_hex = str(cf_hex)
                    self.custom_font_name = cfg.get("custom_font_name")
                    self.visual_char_widths = self._default_font_widths()
                self.current_lang = cfg.get("lang", "pl")
                self.theme = cfg.get("theme", "dark")
                self.chars_per_line = int(cfg.get("chars_per_line", 37))
                self.pixel_limit = int(cfg.get("pixel_limit", self.chars_per_line * self.FONT_WIDTH_STANDARD))
                self.pixel_mode_enabled = bool(cfg.get("pixel_mode_enabled", False))
                self.polish_conversion = bool(cfg.get("polish_conversion", False))
                pm = cfg.get("polish_map")
                if isinstance(pm, dict) and pm:
                    self.polish_map = {str(k)[:1]: str(v)[:1] for k, v in pm.items() if k and v}
                ei = cfg.get("error_ignores")
                if isinstance(ei, dict):
                    self.error_ignores = {str(k): set(int(x) for x in v) for k, v in ei.items() if isinstance(v, list)}
                self.visual_ignore_tags = set(str(x).upper() for x in cfg.get("visual_ignore_tags", self.DEFAULT_VISUAL_IGNORE_TAGS))
                self.visual_tag_widths.update({str(k).upper(): int(v) for k, v in cfg.get("visual_tag_widths", {}).items()})
                self.visual_tag_texts.update({str(k).upper(): str(v) for k, v in cfg.get("visual_tag_texts", {}).items()})
                self.use_font_width_table = bool(cfg.get("use_font_width_table", True))
                if self.use_font_width_table and "visual_char_widths" in cfg:
                    self.visual_char_widths.update({str(k): int(v) for k, v in cfg.get("visual_char_widths", {}).items()})
                elif not self.use_font_width_table and "visual_char_widths" in cfg:
                    self.visual_char_widths = {str(k): int(v) for k, v in cfg.get("visual_char_widths", {}).items()}
        except: pass

    def _save_config(self):
        try:
            with open("config.json", "w", encoding="utf-8") as f:
                json.dump({
                    "lang": self.current_lang,
                    "theme": self.theme,
                    "chars_per_line": int(self.chars_per_line),
                    "pixel_limit": int(self.pixel_limit),
                    "pixel_mode_enabled": bool(self.pixel_mode_enabled),
                    "polish_conversion": bool(self.polish_conversion),
                    "polish_map": self.polish_map,
                    "error_ignores": {k: sorted(v) for k, v in self.error_ignores.items() if v},
                    "visual_ignore_tags": sorted(str(x).upper() for x in self.visual_ignore_tags),
                    "visual_tag_widths": {str(k).upper(): int(v) for k, v in self.visual_tag_widths.items()},
                    "visual_tag_texts": {str(k).upper(): str(v) for k, v in self.visual_tag_texts.items()},
                    "use_font_width_table": self.use_font_width_table,
                    "visual_char_widths": self._char_width_overrides(),
                    "custom_font_hex": self.custom_font_hex,
                    "custom_font_name": self.custom_font_name,
                }, f, ensure_ascii=False, indent=2)
        except: pass

    def _change_lang(self, lang):
        self.current_lang = lang
        self._save_config()
        self._update_ui_texts()

    def _update_ui_texts(self):
        self.setWindowTitle(self.tr("title"))

        # Menu updates
        for key, action in self.menu_actions.items():
            if isinstance(action, QMenu): action.setTitle(self.tr(key))
            else: action.setText(self.tr(key))

        # UI elements updates
        for key, widget in self.ui_elements.items():
            if isinstance(widget, QPushButton) or isinstance(widget, QLabel):
                widget.setText(self.tr(key))
            elif isinstance(widget, QLineEdit):
                widget.setPlaceholderText(self.tr(key))

        # Table headers
        self.table.setHorizontalHeaderLabels([
            self.tr("col_id"), self.tr("col_size"), self.tr("col_widest"),
            self.tr("col_lines"), self.tr("col_slack"), self.tr("col_preview")])

        # Napis o czcionce i etykieta limitu (zależne od języka i trybu)
        self._update_font_status()
        self._sync_limit_spin()

    def _default_tag_widths(self):
        d = dict(self.DEFAULT_VISUAL_TAG_WIDTHS)
        for code in self.DEFAULT_VISUAL_VAR0702_CODES: d.setdefault(f'VAR:0702*{code}', 10)
        return d

    def _default_font_widths(self):
        """Zwraca tabelę szerokości z załadowanej czcionki.
        Bez czcionki - pusta tabela (każdy znak liczy się jako FONT_WIDTH_STANDARD)."""
        if not getattr(self, 'custom_font_hex', None): return {}
        try: data = [int(x, 16) for x in self.custom_font_hex.split()]
        except: data = []
        out = {}
        for i, w in enumerate(data):
            code = self.FONT_WIDTH_BASE + i
            if 0 <= code <= 0x10FFFF: out[chr(code)] = int(w)
        return out

    # --- ŁADOWANIE / USUWANIE WŁASNEGO FONTU ---
    def _load_font_file(self):
        fp, _ = QFileDialog.getOpenFileName(
            self, self.tr("fd_font"), "",
            "Font width table (*.dat *.bin *.txt);;All (*.*)")
        if not fp: return
        try:
            widths = self._parse_font_width_file(fp)
        except Exception as e:
            QMessageBox.critical(self, self.tr("msg_err"), f"{os.path.basename(fp)}:\n{e}")
            return
        self.custom_font_hex = ' '.join(f'{w:02X}' for w in widths)
        self.custom_font_name = os.path.basename(fp)
        self.use_font_width_table = True
        self.visual_char_widths = self._default_font_widths()
        self._save_config()
        self._after_font_change()
        QMessageBox.information(self, self.tr("msg_ok"),
                                self.tr("msg_font_loaded").format(
                                    name=self.custom_font_name, count=len(widths)))

    def _remove_font_file(self):
        if not self.custom_font_hex:
            QMessageBox.information(self, self.tr("msg_ok"), self.tr("msg_font_none"))
            return
        name = self.custom_font_name or "?"
        self.custom_font_hex = None
        self.custom_font_name = None
        self.visual_char_widths = self._default_font_widths()
        self._save_config()
        self._after_font_change()
        QMessageBox.information(self, self.tr("msg_ok"),
                                self.tr("msg_font_removed").format(name=name))

    def _after_font_change(self):
        self._sync_limit_spin()
        self.highlighter.rehighlight()
        self._refresh_table()
        self._refresh_file_list()
        self._refresh_editor_info()
        self._update_font_status()

    def _update_font_status(self):
        if not hasattr(self, 'font_status_label'): return
        if self.custom_font_name:
            self.font_status_label.setText(
                self.tr("lbl_font_loaded").format(name=self.custom_font_name))
            self.font_status_label.setStyleSheet(
                f"color: {self.get_color('success')}; font-weight: bold; padding: 0 8px;")
            self.status.showMessage(self.tr("msg_font_active").format(name=self.custom_font_name))
        else:
            self.font_status_label.setText(self.tr("lbl_font_none"))
            self.font_status_label.setStyleSheet(
                "color: #8a8f98; font-weight: normal; padding: 0 8px;")

    def _parse_font_width_file(self, fp):
        """Wczytuje tabelę szerokości fontu.
        Obsługuje: tekst hex ('00 02 06 ...') oraz surowy plik binarny
        (1 bajt = szerokość jednego znaku, począwszy od 0x20)."""
        with open(fp, 'rb') as f: raw = f.read()
        if not raw: raise ValueError("Pusty plik")

        # Próba 1: plik tekstowy z hexami oddzielonymi spacjami/nowymi liniami
        try:
            text = raw.decode('utf-8')
            tokens = text.split()
            if tokens and all(re.fullmatch(r'[0-9A-Fa-f]{1,2}', t) for t in tokens):
                widths = [int(t, 16) for t in tokens]
                if len(widths) < 32: raise ValueError("Za mało wartości w tabeli")
                return widths
        except (UnicodeDecodeError, ValueError):
            pass

        # Próba 2: surowe bajty (każdy bajt = szerokość znaku)
        widths = list(raw)
        # Sensowna tabela szerokości: wartości małe (piksele), zwykle <= 0x20
        if len(widths) > 4096:
            raise ValueError(
                "Plik za duży na tabelę szerokości.\n"
                "To wygląda na plik bitmap glifów (grafika czcionki) - "
                "on nie zawiera szerokości i nie jest tu potrzebny.\n"
                "Załaduj mały plik z tabelą szerokości (1 bajt na znak).")
        if max(widths) > 0x3F:
            raise ValueError(
                "Wartości za duże jak na szerokości znaków (max 63 px).\n"
                "To prawdopodobnie nie jest tabela szerokości fontu.")
        return widths

    def _char_width_overrides(self):
        if not self.use_font_width_table: return {str(k): int(v) for k, v in self.visual_char_widths.items()}
        default = self._default_font_widths()
        return {str(k): int(v) for k, v in self.visual_char_widths.items() if default.get(k) != int(v)}

    def get_color(self, name):
        is_light = self.theme == "light"
        if name == "text": return "#1f2937" if is_light else "#d0d0d0"
        if name == "error": return "#dc2626" if is_light else "#ff6b6b"
        if name == "success": return "#059669" if is_light else "#66bb6a"
        if name == "warning": return "#2563eb" if is_light else "#ffeb3b"
        return "#ffffff"

    def apply_theme(self):
        if self.theme == "light":
            self.setStyleSheet(LIGHT_STYLE)
            self.btn_theme.setText("🌙")
            self.btn_theme.setObjectName("secondary")
        else:
            self.setStyleSheet(DARK_STYLE)
            self.btn_theme.setText("☀️")
            self.btn_theme.setObjectName("")

        self.btn_theme.style().unpolish(self.btn_theme)
        self.btn_theme.style().polish(self.btn_theme)

        if hasattr(self, 'highlighter'): self.highlighter.set_theme(self.theme)
        self._refresh_table()
        self._refresh_file_list()
        self._update_font_status()

    def toggle_theme(self):
        self.theme = "light" if self.theme == "dark" else "dark"
        self._save_config()
        self.apply_theme()

    def set_modified(self, m=True):
        self.modified = m
        title = self.tr("title")
        if self.current_file: title += f" — {os.path.basename(self.current_file)}"
        if m: title += " *"
        self.setWindowTitle(title)

    def init_ui(self):
        self.create_menu()

        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)
        main_layout.setContentsMargins(10, 10, 10, 10)

        top = QHBoxLayout()
        btn_open = QPushButton(); btn_open.clicked.connect(self._open_files)
        btn_dir = QPushButton(); btn_dir.clicked.connect(self._open_dir)
        btn_save = QPushButton(); btn_save.setObjectName("success"); btn_save.clicked.connect(self._save_file)
        btn_save_all = QPushButton(); btn_save_all.setObjectName("success"); btn_save_all.clicked.connect(self._save_all)
        btn_settings = QPushButton(); btn_settings.setObjectName("secondary"); btn_settings.clicked.connect(self._open_settings)
        btn_pointers = QPushButton(); btn_pointers.clicked.connect(self._edit_pointers)
        btn_clear = QPushButton(); btn_clear.setObjectName("danger"); btn_clear.clicked.connect(self._clear_all)
        btn_font_load = QPushButton(); btn_font_load.setObjectName("secondary"); btn_font_load.clicked.connect(self._load_font_file)
        btn_font_del = QPushButton(); btn_font_del.setObjectName("secondary"); btn_font_del.clicked.connect(self._remove_font_file)

        self.ui_elements["btn_files"] = btn_open
        self.ui_elements["btn_folder"] = btn_dir
        self.ui_elements["btn_save"] = btn_save
        self.ui_elements["btn_save_all"] = btn_save_all
        self.ui_elements["btn_settings"] = btn_settings
        self.ui_elements["btn_pointers"] = btn_pointers
        self.ui_elements["btn_clear"] = btn_clear
        self.ui_elements["btn_font_load"] = btn_font_load
        self.ui_elements["btn_font_del"] = btn_font_del

        self.btn_theme = QPushButton("☀️")
        self.btn_theme.clicked.connect(self.toggle_theme)

        top.addWidget(btn_open)
        top.addWidget(btn_dir)
        top.addWidget(btn_save)
        top.addWidget(btn_save_all)
        top.addWidget(btn_settings)
        top.addWidget(btn_pointers)
        top.addWidget(btn_font_load)
        top.addWidget(btn_font_del)

        self.font_status_label = QLabel("")
        self.font_status_label.setTextFormat(Qt.PlainText)
        top.addWidget(self.font_status_label)

        top.addWidget(btn_clear)
        top.addStretch()

        lbl_limit = QLabel()
        self.ui_elements["lbl_limit"] = lbl_limit
        top.addWidget(lbl_limit)

        self.limit_spin = QSpinBox()
        self.limit_spin.setRange(10, 999)
        self.limit_spin.setValue(self.chars_per_line)
        self.limit_spin.setFixedWidth(110)
        self.limit_spin.valueChanged.connect(self._on_limit_changed)
        self._sync_limit_spin()
        top.addWidget(self.limit_spin)
        top.addWidget(self.btn_theme)
        main_layout.addLayout(top)

        splitter = QSplitter(Qt.Horizontal)
        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(0, 0, 0, 0)

        self.search_file = QLineEdit()
        self.search_file.textChanged.connect(self._refresh_file_list)
        self.ui_elements["search_file"] = self.search_file
        left_layout.addWidget(self.search_file)

        self.search_content = QLineEdit()
        self.search_content.textChanged.connect(self._refresh_file_list)
        self.ui_elements["search_text"] = self.search_content
        left_layout.addWidget(self.search_content)

        self.file_list = QListWidget()
        self.file_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.file_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.file_list.customContextMenuRequested.connect(self._file_list_context_menu)
        # Delete usuwa zaznaczone pliki TYLKO gdy fokus jest na liście
        del_sc = QShortcut(QKeySequence(Qt.Key_Delete), self.file_list)
        del_sc.setContext(Qt.WidgetShortcut)
        del_sc.activated.connect(self._remove_selected_files)
        self.file_list.itemClicked.connect(self._on_file_selected)
        left_layout.addWidget(self.file_list)
        splitter.addWidget(left)

        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)
        right_splitter = QSplitter(Qt.Vertical)

        self.table = QTableWidget()
        self.table.setColumnCount(6)
        self.table.setAlternatingRowColors(True)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.verticalHeader().setVisible(False)
        self.table.itemSelectionChanged.connect(self._on_entry_selected)
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(4, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(5, QHeaderView.Stretch)
        right_splitter.addWidget(self.table)

        editor_box = QWidget()
        editor_layout = QVBoxLayout(editor_box)
        editor_layout.setContentsMargins(0, 0, 0, 0)

        tokens_layout = QHBoxLayout()
        tokens = [('[PLAYER]', '[PLAYER]'), ('[PAGE]', '[PAGE]'), ('[BOX]', '[BOX]'),
                  ('[SYS]', '[SYS]'), ('[0C]', '[0C]'), ('\\n (Nowa linia)', '\n'),
                  ('é', 'é'), ('…', '…'), ('♂', '♂'), ('♀', '♀'), ('♪', '♪')]
        for lbl, tok in tokens:
            b = QPushButton(lbl)
            b.setObjectName("token")
            b.clicked.connect(lambda _, t=tok: self.editor.insertPlainText(t))
            tokens_layout.addWidget(b)
        tokens_layout.addStretch()
        editor_layout.addLayout(tokens_layout)

        info_row = QHBoxLayout()
        self.editor_info = QLabel()
        self.ui_elements["lbl_editor"] = self.editor_info
        info_row.addWidget(self.editor_info)
        info_row.addStretch()
        self.btn_ignore_error = QPushButton()
        self.btn_ignore_error.setObjectName("secondary")
        self.btn_ignore_error.clicked.connect(self._toggle_error_ignore)
        self.btn_ignore_error.setVisible(False)
        info_row.addWidget(self.btn_ignore_error)
        editor_layout.addLayout(info_row)

        self.editor = QTextEdit()
        self.editor.setObjectName("mainEditor")
        self.editor.setEnabled(False)
        self.editor.setUndoRedoEnabled(True)
        self.highlighter = UKDHighlighter(self.editor.document(), self)
        self.editor.textChanged.connect(self._on_editor_changed)
        editor_layout.addWidget(self.editor)

        right_splitter.addWidget(editor_box)
        right_splitter.setSizes([400, 400])
        right_layout.addWidget(right_splitter)

        splitter.addWidget(right)
        splitter.setSizes([300, 1000])
        main_layout.addWidget(splitter)

        self.status = QStatusBar()
        self.setStatusBar(self.status)

    def create_menu(self):
        menubar = self.menuBar()
        self.menu_actions["menu_file"] = menubar.addMenu("")

        self.menu_actions["menu_open"] = self.menu_actions["menu_file"].addAction("", self._open_files)
        self.menu_actions["menu_open_folder"] = self.menu_actions["menu_file"].addAction("", self._open_dir)
        self.menu_actions["menu_file"].addSeparator()
        self.menu_actions["menu_save"] = self.menu_actions["menu_file"].addAction("", self._save_file)
        self.menu_actions["menu_save_as"] = self.menu_actions["menu_file"].addAction("", self._save_file_as)
        self.menu_actions["menu_save_all"] = self.menu_actions["menu_file"].addAction("", self._save_all)
        self.menu_actions["menu_file"].addSeparator()

        self.menu_actions["menu_imp_exp"] = self.menu_actions["menu_file"].addMenu("")
        self.menu_actions["menu_exp_txt"] = self.menu_actions["menu_imp_exp"].addAction("", self._export_txt)
        self.menu_actions["menu_exp_json"] = self.menu_actions["menu_imp_exp"].addAction("", self._export_json)
        self.menu_actions["menu_imp_exp"].addSeparator()
        self.menu_actions["menu_b_exp_txt"] = self.menu_actions["menu_imp_exp"].addAction("", self._batch_export_txt)
        self.menu_actions["menu_b_exp_json"] = self.menu_actions["menu_imp_exp"].addAction("", self._batch_export_json)
        self.menu_actions["menu_imp_exp"].addSeparator()
        self.menu_actions["menu_imp_txt"] = self.menu_actions["menu_imp_exp"].addAction("", self._import_txt)
        self.menu_actions["menu_imp_json"] = self.menu_actions["menu_imp_exp"].addAction("", self._import_json)
        self.menu_actions["menu_imp_exp"].addSeparator()
        self.menu_actions["menu_b_imp_txt"] = self.menu_actions["menu_imp_exp"].addAction("", self._batch_import_txt)
        self.menu_actions["menu_b_imp_json"] = self.menu_actions["menu_imp_exp"].addAction("", self._batch_import_json)
        self.menu_actions["menu_b_imp_dir_txt"] = self.menu_actions["menu_imp_exp"].addAction("", lambda: self._batch_import_folder('.txt'))
        self.menu_actions["menu_b_imp_dir_json"] = self.menu_actions["menu_imp_exp"].addAction("", lambda: self._batch_import_folder('.json'))

        self.menu_actions["menu_file"].addSeparator()
        self.menu_actions["menu_transfer"] = self.menu_actions["menu_file"].addAction("", self._transfer_lang)
        self.menu_actions["menu_b_transfer"] = self.menu_actions["menu_file"].addAction("", self._batch_transfer_folders)
        self.menu_actions["menu_file"].addSeparator()
        self.menu_actions["menu_exit"] = self.menu_actions["menu_file"].addAction("", self.close)

        self.menu_actions["menu_edit"] = menubar.addMenu("")
        self.menu_actions["menu_undo"] = self.menu_actions["menu_edit"].addAction("", self._editor_undo)
        self.menu_actions["menu_undo"].setShortcut("Ctrl+Z")
        self.menu_actions["menu_redo"] = self.menu_actions["menu_edit"].addAction("", self._editor_redo)
        self.menu_actions["menu_redo"].setShortcut("Ctrl+Y")
        self.menu_actions["menu_edit"].addSeparator()
        self.menu_actions["menu_remove_file"] = self.menu_actions["menu_edit"].addAction("", self._remove_selected_files)
        self.menu_actions["menu_edit"].addSeparator()
        self.menu_actions["menu_mass_search"] = self.menu_actions["menu_edit"].addAction("", self._mass_search_dialog)
        self.menu_actions["menu_edit_pointers"] = self.menu_actions["menu_edit"].addAction("", self._edit_pointers)

        self.menu_actions["menu_view"] = menubar.addMenu("")
        self.menu_actions["menu_hex"] = self.menu_actions["menu_view"].addAction("", self._hex_view)
        self.menu_actions["menu_struct"] = self.menu_actions["menu_view"].addAction("", self._struct_view)

        self.menu_actions["menu_lang"] = menubar.addMenu("")
        self.menu_actions["menu_lang"].addAction("Polski", lambda: self._change_lang("pl"))
        self.menu_actions["menu_lang"].addAction("English", lambda: self._change_lang("en"))

    # --- DRAG & DROP ---
    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls(): event.accept()
        else: event.ignore()

    def dropEvent(self, event: QDropEvent):
        paths = [os.path.abspath(u.toLocalFile()) for u in event.mimeData().urls()]
        self._process_paths(paths)
        event.accept()

    def _open_files(self):
        files, _ = QFileDialog.getOpenFileNames(self, self.tr("fd_open"), "", self.FTYPES_ALL)
        if files: self._process_paths(files)

    def _open_dir(self):
        folder = QFileDialog.getExistingDirectory(self, self.tr("fd_dir"))
        if folder: self._process_paths([folder])

    def _process_paths(self, paths):
        added = 0
        pending_imports = []
        for path in paths:
            if os.path.isdir(path):
                for root, _, files in os.walk(path):
                    for name in files:
                        full = os.path.abspath(os.path.join(root, name))
                        ext = os.path.splitext(name)[1].lower()
                        if ext in self.EXTS_ALL and full not in self.file_parsers:
                            if self._load_parser(full): added += 1
                        elif ext in self.EXTS_IMPORT:
                            pending_imports.append(full)
            else:
                ext = os.path.splitext(path)[1].lower()
                if ext in self.EXTS_ALL:
                    if path not in self.file_parsers and self._load_parser(path): added += 1
                elif ext in self.EXTS_IMPORT:
                    pending_imports.append(path)

        # Najpierw ładujemy pliki binarne, potem importujemy TXT/JSON
        # (dzięki temu drop "plik.ukd + plik.txt" naraz działa poprawnie)
        imported = 0
        for path in pending_imports:
            if self._import_side_file(path): imported += 1

        if added > 0 or imported > 0:
            self._refresh_file_list()
            if self.current_file: self._refresh_table()
            msgs = []
            if added > 0: msgs.append(f"Loaded {added} files.")
            if imported > 0: msgs.append(f"Imported {imported} TXT/JSON.")
            self.status.showMessage(" ".join(msgs))

    def _import_side_file(self, path):
        """Plik .txt/.json:
        1) jeśli jest wczytany plik binarny o tej samej nazwie -> import do niego,
        2) w przeciwnym razie -> otwórz TXT/JSON samodzielnie jako edytowalny plik."""
        ext = os.path.splitext(path)[1].lower()
        base = os.path.splitext(os.path.basename(path))[0].lower()

        target_fp = None
        for fp, pr in self.file_parsers.items():
            if getattr(pr, 'IS_TEXT', False): continue
            if os.path.splitext(os.path.basename(fp))[0].lower() == base:
                target_fp = fp
                break

        if target_fp is None:
            # Otwórz samodzielnie jako plik tekstowy
            if path in self.file_parsers: return False
            try:
                parser = TextParser()
                parser.parse_file(path)
            except Exception as e:
                QMessageBox.critical(self, self.tr("msg_err"), f"{os.path.basename(path)}:\n{e}")
                return False
            self.file_parsers[path] = parser
            self.status.showMessage(self.tr("msg_opened_text").format(name=os.path.basename(path)))
            return True

        parser = self.file_parsers[target_fp]
        try:
            if ext == '.txt': parser.import_from_txt(path)
            elif ext == '.json': parser.import_from_json(path)
            else: return False
        except Exception as e:
            QMessageBox.critical(self, self.tr("msg_err"), f"{os.path.basename(path)}:\n{e}")
            return False

        self.set_modified(True)
        if target_fp == self.current_file:
            if self.current_entry_index >= len(parser.entries):
                self.current_entry_index = -1
                self.editor.blockSignals(True)
                self.editor.clear()
                self.editor.blockSignals(False)
                self.editor.setEnabled(False)
            self._refresh_table()
            self._refresh_editor_info()
        self.status.showMessage(self.tr("msg_imported_file").format(
            src=os.path.basename(path), dst=os.path.basename(target_fp)))
        return True

    def _load_parser(self, fp):
        try:
            parser = UKDParser()
            parser.parse_file(fp)
            self._apply_polish_display(parser)
            self.file_parsers[fp] = parser
            return True
        except Exception: return False

    # --- COFNIJ / PONÓW W EDYTORZE ---
    def _editor_undo(self):
        if self.editor.isEnabled(): self.editor.undo()

    def _editor_redo(self):
        if self.editor.isEnabled(): self.editor.redo()

    # --- USUWANIE PLIKÓW Z LISTY ---
    def _file_list_context_menu(self, pos):
        item = self.file_list.itemAt(pos)
        if item is None: return
        selected = self.file_list.selectedItems()
        count = len(selected) if selected else 1
        menu = QMenu(self.file_list)
        act_remove = menu.addAction(self.tr("ctx_remove_file").format(count=count))
        action = menu.exec(self.file_list.mapToGlobal(pos))
        if action == act_remove:
            self._remove_selected_files()

    def _remove_selected_files(self):
        """Usuwa z listy zaznaczone pliki (można zaznaczyć wiele:
        Ctrl+klik, Shift+klik). Pliki na dysku zostają nietknięte."""
        selected = self.file_list.selectedItems()
        if not selected: return
        paths = [it.data(Qt.UserRole) for it in selected]
        # Ostrzeż o niezapisanych zmianach w usuwanych plikach
        unsaved = []
        for fp in paths:
            p = self.file_parsers.get(fp)
            if p is not None and p.entries != p.original_entries:
                unsaved.append(os.path.basename(fp))
        if unsaved:
            if QMessageBox.question(
                self, "?",
                self.tr("msg_remove_unsaved").format(names="\n".join(unsaved[:10]))
            ) != QMessageBox.Yes:
                return
        removed = 0
        for fp in paths:
            if fp in self.file_parsers:
                del self.file_parsers[fp]
                removed += 1
            if fp == self.current_file:
                self.current_file = None
                self.current_entry_index = -1
                self.table.setRowCount(0)
                self.editor.blockSignals(True)
                self.editor.clear()
                self.editor.blockSignals(False)
                self.editor.setEnabled(False)
                self.editor_info.setText(self.tr("lbl_editor"))
                self.editor_info.setStyleSheet("")
                self.btn_ignore_error.setVisible(False)
        self._refresh_file_list()
        self.status.showMessage(self.tr("msg_files_removed").format(count=removed))

    def _clear_all(self):
        if self.modified and QMessageBox.question(self, "?", self.tr("msg_discard")) != QMessageBox.Yes:
            return
        self.file_parsers.clear()
        self.current_file = None
        self.current_entry_index = -1
        self.file_list.clear()
        self.table.setRowCount(0)
        self.editor.clear()
        self.editor.setEnabled(False)
        self.editor_info.setText(self.tr("lbl_editor"))
        self.set_modified(False)

    def _open_settings(self):
        dlg = SettingsDialog(self, self)
        if dlg.exec() == QDialog.Accepted:
            self._save_config()
            self._sync_limit_spin()
            self.highlighter.rehighlight()
            self._refresh_table()
            self._refresh_file_list()
            self._refresh_editor_info()

    # --- LIMITS & MATH ---
    def _pixel_mode(self):
        """Tryb pikselowy - włączany wyłącznikiem w Ustawieniach.
        Zapamiętywany w config.json niezależnie od czcionki."""
        return bool(self.pixel_mode_enabled)

    def _on_limit_changed(self):
        if self._pixel_mode():
            self.pixel_limit = self.limit_spin.value()
        else:
            self.chars_per_line = self.limit_spin.value()
        self._save_config()
        self.highlighter.rehighlight()
        self._refresh_table()
        self._refresh_file_list()
        self._refresh_editor_info()

    def _px_units(self):
        """Czy szerokości liczone są w pikselach (załadowana czcionka lub tryb px)."""
        return self._pixel_mode() or (self.use_font_width_table and bool(self.custom_font_hex))

    def _char_width(self, ch):
        """Szerokość pojedynczego znaku: z czcionki/nadpisań, inaczej wartość domyślna."""
        w = self.visual_char_widths.get(ch)
        if w is not None: return int(w)
        return int(self.FONT_WIDTH_STANDARD) if self._px_units() else 1

    def _sync_limit_spin(self):
        """Przełącza spinner między trybem znaki/piksele."""
        if not hasattr(self, 'limit_spin'): return
        self.limit_spin.blockSignals(True)
        if self._pixel_mode():
            self.limit_spin.setRange(10, 4000)
            self.limit_spin.setValue(int(self.pixel_limit))
            self.limit_spin.setSuffix(" px")
        else:
            self.limit_spin.setRange(10, 999)
            self.limit_spin.setValue(int(self.chars_per_line))
            self.limit_spin.setSuffix("")
        self.limit_spin.blockSignals(False)
        if "lbl_limit" in self.ui_elements:
            key = "lbl_limit_px" if self._pixel_mode() else "lbl_limit"
            self.ui_elements["lbl_limit"].setText(self.tr(key))

    def _visual_limit_width(self):
        if self._pixel_mode(): return int(self.pixel_limit)
        if self._px_units(): return int(self.chars_per_line) * int(self.FONT_WIDTH_STANDARD)
        return int(self.chars_per_line)

    def _line_widths(self, text):
        """Zwraca listę (nr_linii, szerokość_w_jednostkach) dla wszystkich linii
        we wszystkich boxach ([BOX]/[PAGE] dzielą tekst)."""
        result = []
        n = 1
        for part in re.split(r'\[(?:BOX|PAGE)\]', text):
            for line in part.split('\n'):
                total = 0; i = 0
                while i < len(line):
                    if line[i] == '[':
                        e = line.find(']', i)
                        if e != -1:
                            total += self._tag_visual_width(line[i + 1:e])
                            i = e + 1; continue
                    total += self._char_width(line[i])
                    i += 1
                result.append((n, total))
                n += 1
        return result

    def _tag_width_units(self, value):
        v = int(value)
        if self._px_units(): return v * int(self.FONT_WIDTH_STANDARD)
        return v

    def _plain_visual_len(self, text):
        total = 0
        for ch in text: total += self._char_width(ch)
        return total

    def _tag_visual_width(self, tag):
        raw = tag.strip()
        base = raw.split(':', 1)[0].upper()
        if base in ('BOX', 'PAGE', '0C', 'SYS'): return 0
        if base in self.visual_ignore_tags or raw.upper() in self.visual_ignore_tags: return 0

        if raw.upper() in self.visual_tag_texts:
            return self._plain_visual_len(str(self.visual_tag_texts[raw.upper()]))
        for k, v in self.visual_tag_texts.items():
            if k.endswith('*') and raw.upper().startswith(k[:-1]):
                return self._plain_visual_len(str(v))

        if raw.upper() in self.visual_tag_widths:
            return self._tag_width_units(self.visual_tag_widths[raw.upper()])
        if base in self.visual_tag_widths:
            return self._tag_width_units(self.visual_tag_widths[base])
        for k, v in self.visual_tag_widths.items():
            if k.endswith('*') and raw.upper().startswith(k[:-1]):
                return self._tag_width_units(v)
        return 0

    def _pv(self, text):
        p = text.replace('[PAGE]', ' ¶ ').replace('[BOX]', ' □ ').replace('[PLAYER]', '★').replace('[SYS]', '⚙').replace('\n', ' ↵ ')
        p = re.sub(r'\[SPEAKER:([^\]]+)\]', r'【\1】', p)
        p = re.sub(r'\[(?:POKEMON|VAR):[^\]]+\]', '◇', p)
        p = re.sub(r'\[[0-9A-Fa-f]{2,4}\]', '·', p)
        p = re.sub(r'\s+', ' ', p).strip()
        return p[:80] + '…' if len(p) > 80 else p

    # --- UI UPDATES ---
    def _refresh_file_list(self):
        nf = self.search_file.text().lower()
        cf = self.search_content.text().lower()
        self.file_list.clear()

        for fp, parser in self.file_parsers.items():
            name = os.path.basename(fp)
            if nf and nf not in name.lower(): continue
            if cf:
                found = False
                for e in parser.entries:
                    if cf in e.lower():
                        found = True; break
                if not found: continue
            err = sum(1 for i in range(len(parser.entries)) if self._entry_has_error(parser, i, fp))
            if getattr(parser, 'IS_TEXT', False): name = f"📝 {name}"
            item = QListWidgetItem(f"⚠️ {name}" if err > 0 else name)
            item.setData(Qt.UserRole, fp)
            if err > 0: item.setForeground(QColor(self.get_color("error")))
            else: item.setForeground(QColor(self.get_color("text")))
            self.file_list.addItem(item)

    def _on_file_selected(self, item):
        self.current_file = item.data(Qt.UserRole)
        self.current_entry_index = -1
        self.editor.setEnabled(False)
        self.editor.clear()
        self._refresh_table()

    def _fill_table_row(self, row, parser, text):
        """Wypełnia jeden wiersz tabeli: ID, Rozmiar, Najdłuższa, Linii, Zapas, Podgląd."""
        limit = self._visual_limit_width()
        unit = " px" if self._pixel_mode() else ""

        o, n = parser.get_length_info(row)
        lstr = f"{n}/{o}" if n != o else str(o)

        lines = self._line_widths(text)
        max_w = max((w for _, w in lines), default=0)
        # liczba linii w najdłuższym boxie
        max_lines = 0
        for part in re.split(r'\[(?:BOX|PAGE)\]', text):
            max_lines = max(max_lines, len(part.split('\n')))
        line_errors = [f"L{ln}: {limit - w}" for ln, w in lines if w > limit]

        ignored = self._is_error_ignored(self.current_file, row) if self.current_file else False
        if ignored: line_errors = []

        has_err = self._entry_has_error(parser, row, self.current_file)
        err_c = QColor(self.get_color("error"))
        txt_c = QColor(self.get_color("text"))
        ok_c = QColor(self.get_color("success"))

        bold = QFont(); bold.setBold(True)

        id_it = QTableWidgetItem(str(row)); id_it.setTextAlignment(Qt.AlignCenter)
        len_it = QTableWidgetItem(lstr); len_it.setTextAlignment(Qt.AlignCenter)
        wid_it = QTableWidgetItem(f"{max_w}{unit}"); wid_it.setTextAlignment(Qt.AlignCenter); wid_it.setFont(bold)
        lin_it = QTableWidgetItem(str(max_lines)); lin_it.setTextAlignment(Qt.AlignCenter); lin_it.setFont(bold)
        rem_it = QTableWidgetItem(); rem_it.setTextAlignment(Qt.AlignCenter); rem_it.setFont(bold)
        pv_it = QTableWidgetItem(self._pv(text))

        if line_errors:
            rem_it.setText(", ".join(line_errors) + " ⚠️")
            rem_it.setForeground(err_c)
            wid_it.setForeground(err_c)
        elif ignored and self._entry_has_error_raw(parser, row):
            rem_it.setText("🔕")
            rem_it.setForeground(txt_c)
            wid_it.setForeground(txt_c)
        else:
            rem_it.setText(f"+{limit - max_w}{unit}")
            rem_it.setForeground(ok_c)
            wid_it.setForeground(err_c if has_err else txt_c)

        base_c = err_c if has_err else txt_c
        id_it.setForeground(base_c)
        len_it.setForeground(base_c)
        lin_it.setForeground(err_c if (max_lines > 3 and not ignored) else txt_c)
        pv_it.setForeground(base_c)

        self.table.setItem(row, 0, id_it)
        self.table.setItem(row, 1, len_it)
        self.table.setItem(row, 2, wid_it)
        self.table.setItem(row, 3, lin_it)
        self.table.setItem(row, 4, rem_it)
        self.table.setItem(row, 5, pv_it)

    def _refresh_table(self):
        self.is_updating_ui = True
        self.table.setRowCount(0)
        if not self.current_file or self.current_file not in self.file_parsers:
            self.is_updating_ui = False; return

        parser = self.file_parsers[self.current_file]
        for i, text in enumerate(parser.entries):
            self.table.insertRow(i)
            self._fill_table_row(i, parser, text)
        self.is_updating_ui = False

    def _on_entry_selected(self):
        if self.is_updating_ui or not self.current_file: return
        items = self.table.selectedItems()
        if not items: return

        idx = items[0].row()
        self.current_entry_index = idx
        parser = self.file_parsers[self.current_file]

        self.editor.blockSignals(True)
        self.editor.setPlainText(parser.entries[idx])
        self.editor.blockSignals(False)
        self.editor.setEnabled(True)
        self._refresh_editor_info()

    def _on_editor_changed(self):
        if self.is_updating_ui or self.current_entry_index < 0: return
        new_text = self.editor.toPlainText()
        parser = self.file_parsers[self.current_file]

        if parser.entries[self.current_entry_index] != new_text:
            parser.entries[self.current_entry_index] = new_text
            self.set_modified(True)
            self._refresh_editor_info()
            self._refresh_file_list()

            self.is_updating_ui = True
            self._fill_table_row(self.current_entry_index, parser, new_text)
            self.is_updating_ui = False

    def _is_error_ignored(self, fp, idx):
        return idx in self.error_ignores.get(fp, set())

    def _toggle_error_ignore(self):
        """Przełącza ignorowanie błędu dla aktualnie edytowanego wpisu."""
        if not self.current_file or self.current_entry_index < 0: return
        fp, idx = self.current_file, self.current_entry_index
        ig = self.error_ignores.setdefault(fp, set())
        if idx in ig:
            ig.discard(idx)
        else:
            ig.add(idx)
        if not ig: self.error_ignores.pop(fp, None)
        self._save_config()
        parser = self.file_parsers[fp]
        self.is_updating_ui = True
        self._fill_table_row(idx, parser, parser.entries[idx])
        self.is_updating_ui = False
        self._refresh_editor_info()
        self._refresh_file_list()

    def _entry_has_error(self, parser, idx, fp=None):
        # Wpis z ręcznie ignorowanym błędem nigdy nie jest liczony jako błędny
        if fp is None:
            for pfp, p in self.file_parsers.items():
                if p is parser:
                    fp = pfp; break
        if fp is not None and self._is_error_ignored(fp, idx): return False
        return self._entry_has_error_raw(parser, idx)

    def _entry_has_error_raw(self, parser, idx):
        """Faktyczny stan błędu, bez uwzględniania ignorowania.
        UWAGA: przekroczenie 'wolnego miejsca' bajtów NIE jest błędem -
        zapis potrafi przesunąć kolejne wpisy i zaktualizować wskaźniki.
        Błędem bajtowym jest tylko przekroczenie zakresu wskaźników u16."""
        try:
            if not getattr(parser, 'IS_TEXT', False):
                # Czy po zmianach całość zmieści się w zakresie wskaźników u16?
                # (cache - przeliczaj tylko gdy teksty się zmieniły)
                key = tuple(len(e) for e in parser.entries)
                cached = getattr(parser, '_total_size_cache', None)
                if cached is None or cached[0] != key:
                    total = 0
                    for e in parser.entries:
                        total += len(parser._encode(e)) + 1
                    parser._total_size_cache = (key, total)
                else:
                    total = cached[1]
                if total > 0xFFFF: return True
            text = parser.entries[idx]
            limit = self._visual_limit_width()
            for part in re.split(r'\[(?:BOX|PAGE)\]', text):
                if len(part.split('\n')) > 3: return True
            for _ln, w in self._line_widths(text):
                if w > limit: return True
            return False
        except: return False

    def _refresh_editor_info(self):
        if self.current_entry_index < 0: return
        parser = self.file_parsers[self.current_file]
        n = len(parser._encode(parser.entries[self.current_entry_index]))

        if getattr(parser, 'IS_TEXT', False):
            info = f"ID: {self.current_entry_index} | Znaki: {n} (plik tekstowy - bez limitu bajtów)"
        else:
            safe_max = parser._safe_max_len_no_shift(self.current_entry_index)
            info = f"ID: {self.current_entry_index} | Bajty: {n}/{safe_max}"
            if n > safe_max:
                # To NIE błąd: zapis przesunie kolejne wpisy i poprawi wskaźniki
                info += " (↔ przesunie kolejne wpisy)"

        # Informacja o szerokości w pikselach (tryb czcionki)
        limit = self._visual_limit_width()
        lines = self._line_widths(parser.entries[self.current_entry_index])
        if lines:
            max_w = max(w for _, w in lines)
            bad = [str(ln) for ln, w in lines if w > limit]
            unit = "px" if self._pixel_mode() else ""
            if bad:
                info += f" | 📏 {max_w}/{limit}{unit} ❌ linia: {', '.join(bad)}"
            else:
                info += f" | 📏 {max_w}/{limit}{unit} (zapas: +{limit - max_w}{unit})"
        raw_error = self._entry_has_error_raw(parser, self.current_entry_index)
        ignored = self._is_error_ignored(self.current_file, self.current_entry_index)
        if raw_error and ignored:
            self.editor_info.setStyleSheet(f"color: {self.get_color('warning')}; font-weight: bold;")
            info += " | 🔕 " + self.tr("lbl_error_ignored")
        elif raw_error:
            self.editor_info.setStyleSheet(f"color: {self.get_color('error')}; font-weight: bold;")
            info += " | ❌ BŁĄD LIMITU"
        else:
            self.editor_info.setStyleSheet(f"color: {self.get_color('success')}; font-weight: bold;")
            info += " | ✅ OK"
        self.editor_info.setText(info)

        # Przycisk ignorowania: widoczny gdy jest błąd albo gdy już ignorujemy
        self.btn_ignore_error.setVisible(raw_error or ignored)
        self.btn_ignore_error.setText(
            self.tr("btn_unignore_error") if ignored else self.tr("btn_ignore_error"))

    def _polish_to_sub(self, text):
        """ĄĆĘŁŃÓŚŹŻ ąćęłńóśźż -> ÀÇÈÊÑÓÙÚÛ àçèêñóùúû (wg edytowalnej tablicy)"""
        for pl, sub in self.polish_map.items():
            if pl != sub and pl in text: text = text.replace(pl, sub)
        return text

    def _sub_to_polish(self, text):
        """Odwrotnie: znaki zastępcze z pliku gry -> polskie znaki (do wyświetlania)"""
        for pl, sub in self.polish_map.items():
            if pl != sub and sub in text: text = text.replace(sub, pl)
        return text

    def _apply_polish_display(self, parser):
        """Po wczytaniu pliku gry: pokaż znaki zastępcze jako polskie litery.
        Konwertuje też original_entries, żeby plik nie był oznaczony jako zmieniony."""
        if not self.polish_conversion: return
        if getattr(parser, 'IS_TEXT', False): return
        for i in range(len(parser.entries)):
            parser.entries[i] = self._sub_to_polish(parser.entries[i])
        for i in range(len(parser.original_entries)):
            parser.original_entries[i] = self._sub_to_polish(parser.original_entries[i])

    def _toggle_polish_display_all(self, enable):
        """Przełącza wyświetlanie we wszystkich wczytanych plikach binarnych
        (wywoływane przy zmianie wyłącznika w Ustawieniach)."""
        conv = self._sub_to_polish if enable else self._polish_to_sub
        for parser in self.file_parsers.values():
            if getattr(parser, 'IS_TEXT', False): continue
            for i in range(len(parser.entries)):
                parser.entries[i] = conv(parser.entries[i])
            for i in range(len(parser.original_entries)):
                parser.original_entries[i] = conv(parser.original_entries[i])

    def _apply_polish_conversion(self, parser):
        """Podmienia polskie znaki na zastępcze we wpisach parsera binarnego.
        Działa tylko gdy włączone w Ustawieniach i tylko dla plików UKD/DED
        (pliki .txt/.json - TextParser - zostają bez zmian)."""
        if not self.polish_conversion: return 0
        if getattr(parser, 'IS_TEXT', False): return 0
        changed = 0
        for i, e in enumerate(parser.entries):
            new = self._polish_to_sub(e)
            if new != e:
                parser.entries[i] = new
                changed += 1
        return changed

    def _save_parser_to(self, parser, filepath):
        """Wspólny zapis: zamiana znaków wg tablicy (tylko pliki binarne,
        nie .txt/.json), zapis na dysk, powrót do wyświetlania wg tablicy.
        Zwraca liczbę wpisów, w których zamieniono znaki."""
        conv = self._apply_polish_conversion(parser)
        try:
            parser.save_file(filepath)
        finally:
            # nawet przy błędzie zapisu przywróć wyświetlanie
            self._apply_polish_display(parser)
        return conv

    def _save_file(self):
        if not self.current_file: return
        parser = self.file_parsers[self.current_file]
        try:
            conv = self._save_parser_to(parser, self.current_file)
            if conv > 0:
                self._refresh_table()
                if self.current_entry_index >= 0:
                    self.editor.blockSignals(True)
                    self.editor.setPlainText(parser.entries[self.current_entry_index])
                    self.editor.blockSignals(False)
            self.set_modified(False)
            if conv > 0:
                self.status.showMessage(
                    f"Saved: {os.path.basename(self.current_file)} | "
                    + self.tr("msg_polish_conv").format(count=conv))
            else:
                self.status.showMessage(f"Saved: {os.path.basename(self.current_file)}")
            self._refresh_file_list()
        except Exception as e:
            QMessageBox.critical(self, self.tr("msg_err"), str(e))

    def _save_file_as(self):
        """Zapisz jako... - zapisuje aktualny plik pod nową nazwą/ścieżką."""
        if not self.current_file: return
        parser = self.file_parsers[self.current_file]
        is_text = getattr(parser, 'IS_TEXT', False)
        if is_text:
            filt = "TXT (*.txt);;JSON (*.json);;All (*.*)"
        else:
            filt = self.FTYPES_ALL
        fp, _ = QFileDialog.getSaveFileName(
            self, self.tr("fd_save_as"), os.path.basename(self.current_file), filt)
        if not fp: return
        try:
            conv = self._save_parser_to(parser, fp)
            # parser wskazuje teraz nowy plik - przenieś go pod nowy klucz
            if fp != self.current_file:
                del self.file_parsers[self.current_file]
                self.file_parsers[fp] = parser
                if self.current_file in self.error_ignores:
                    self.error_ignores[fp] = self.error_ignores.pop(self.current_file)
                    self._save_config()
                self.current_file = fp
            self.set_modified(False)
            msg = self.tr("msg_saved_as").format(name=os.path.basename(fp))
            if conv > 0:
                msg += " | " + self.tr("msg_polish_conv").format(count=conv)
            self.status.showMessage(msg)
            self._refresh_file_list()
            self._refresh_table()
        except Exception as e:
            QMessageBox.critical(self, self.tr("msg_err"), str(e))

    def _save_all(self):
        """Zapisz folder/wszystko - zapisuje zmiany we WSZYSTKICH wczytanych
        plikach. Zamiana znaków wg tablicy działa tylko dla plików gry
        (.ukd, .ded itd.), a pliki .txt/.json zapisywane są bez zamiany."""
        if not self.file_parsers: return
        ok, err, conv_total = 0, 0, 0
        errors = []
        for fp, parser in self.file_parsers.items():
            try:
                conv_total += self._save_parser_to(parser, fp)
                ok += 1
            except Exception as e:
                err += 1
                errors.append(f"{os.path.basename(fp)}: {e}")
        self.set_modified(False)
        self._refresh_file_list()
        self._refresh_table()
        if self.current_entry_index >= 0 and self.current_file in self.file_parsers:
            p = self.file_parsers[self.current_file]
            if self.current_entry_index < len(p.entries):
                self.editor.blockSignals(True)
                self.editor.setPlainText(p.entries[self.current_entry_index])
                self.editor.blockSignals(False)
        msg = self.tr("msg_saved_all").format(ok=ok, err=err)
        if conv_total > 0:
            msg += " | " + self.tr("msg_polish_conv").format(count=conv_total)
        self.status.showMessage(msg)
        if errors:
            QMessageBox.warning(self, self.tr("msg_err"), "\n".join(errors[:20]))
        else:
            QMessageBox.information(self, self.tr("msg_ok"), msg)

    # --- EXPORT / IMPORT ---
    def _export_txt(self):
        if not self.current_file: return
        fp, _ = QFileDialog.getSaveFileName(self, "Export TXT", "", "TXT (*.txt)")
        if fp:
            self.file_parsers[self.current_file].export_to_txt(fp)

    def _export_json(self):
        if not self.current_file: return
        fp, _ = QFileDialog.getSaveFileName(self, "Export JSON", "", "JSON (*.json)")
        if fp:
            self.file_parsers[self.current_file].export_to_json(fp)

    def _batch_export_txt(self):
        if not self.file_parsers: return
        d = QFileDialog.getExistingDirectory(self, self.tr("fd_dir"))
        if d:
            for fp, p in self.file_parsers.items():
                p.export_to_txt(os.path.join(d, os.path.splitext(os.path.basename(fp))[0] + '.txt'))
            QMessageBox.information(self, self.tr("msg_ok"), "Export TXT OK.")

    def _batch_export_json(self):
        if not self.file_parsers: return
        d = QFileDialog.getExistingDirectory(self, self.tr("fd_dir"))
        if d:
            for fp, p in self.file_parsers.items():
                p.export_to_json(os.path.join(d, os.path.splitext(os.path.basename(fp))[0] + '.json'))
            QMessageBox.information(self, self.tr("msg_ok"), "Export JSON OK.")

    def _import_txt(self):
        if not self.current_file: return
        fp, _ = QFileDialog.getOpenFileName(self, "Import TXT", "", "TXT (*.txt)")
        if fp:
            self.file_parsers[self.current_file].import_from_txt(fp)
            self.set_modified(True)
            self._refresh_table()
            self._refresh_file_list()

    def _import_json(self):
        if not self.current_file: return
        fp, _ = QFileDialog.getOpenFileName(self, "Import JSON", "", "JSON (*.json)")
        if fp:
            self.file_parsers[self.current_file].import_from_json(fp)
            self.set_modified(True)
            self._refresh_table()
            self._refresh_file_list()

    def _batch_import_txt(self):
        if not self.file_parsers: return
        files, _ = QFileDialog.getOpenFileNames(self, "Import TXT", "", "TXT (*.txt)")
        if not files: return
        count = 0
        for tf in files:
            base = os.path.splitext(os.path.basename(tf))[0]
            for uf, p in self.file_parsers.items():
                if os.path.splitext(os.path.basename(uf))[0] == base:
                    p.import_from_txt(tf)
                    p.save_file(uf)
                    count += 1
                    break
        self._refresh_file_list()
        if self.current_file: self._refresh_table()
        QMessageBox.information(self, self.tr("msg_ok"), f"Imported: {count}")

    def _batch_import_json(self):
        if not self.file_parsers: return
        files, _ = QFileDialog.getOpenFileNames(self, "Import JSON", "", "JSON (*.json)")
        if not files: return
        count = 0
        for jf in files:
            base = os.path.splitext(os.path.basename(jf))[0]
            for uf, p in self.file_parsers.items():
                if os.path.splitext(os.path.basename(uf))[0] == base:
                    p.import_from_json(jf)
                    p.save_file(uf)
                    count += 1
                    break
        self._refresh_file_list()
        if self.current_file: self._refresh_table()
        QMessageBox.information(self, self.tr("msg_ok"), f"Imported: {count}")

    def _batch_import_folder(self, ext):
        """Masowy import z FOLDERU: wskazujesz folder, a program dopasowuje
        pliki .txt/.json (także z podfolderów) do wczytanych plików po nazwie,
        importuje i od razu zapisuje. Pliki bez pary są pomijane i raportowane."""
        if not self.file_parsers:
            QMessageBox.information(self, self.tr("msg_ok"), self.tr("msg_imp_dir_nofiles"))
            return
        folder = QFileDialog.getExistingDirectory(self, self.tr("fd_imp_dir"))
        if not folder: return

        # Zbierz pliki o zadanym rozszerzeniu (również z podfolderów)
        found = []
        for root, _, files in os.walk(folder):
            for name in files:
                if os.path.splitext(name)[1].lower() == ext:
                    found.append(os.path.join(root, name))
        if not found:
            QMessageBox.information(self, self.tr("msg_ok"),
                                    self.tr("msg_imp_dir_empty").format(ext=ext))
            return

        # Mapa: nazwa bazowa -> wczytany plik (pliki tekstowe pomijamy jako cel)
        targets = {}
        for uf, p in self.file_parsers.items():
            if getattr(p, 'IS_TEXT', False): continue
            targets.setdefault(os.path.splitext(os.path.basename(uf))[0].lower(), uf)

        imported, errors, skipped = 0, [], []
        for sf in sorted(found):
            base = os.path.splitext(os.path.basename(sf))[0].lower()
            uf = targets.get(base)
            if uf is None:
                skipped.append(os.path.basename(sf))
                continue
            p = self.file_parsers[uf]
            try:
                if ext == '.txt': p.import_from_txt(sf)
                else: p.import_from_json(sf)
                p.save_file(uf)
                self._apply_polish_display(p)
                imported += 1
            except Exception as e:
                errors.append(f"{os.path.basename(sf)}: {e}")

        self._refresh_file_list()
        if self.current_file: self._refresh_table()
        if self.current_entry_index >= 0 and self.current_file in self.file_parsers:
            pcur = self.file_parsers[self.current_file]
            if self.current_entry_index < len(pcur.entries):
                self.editor.blockSignals(True)
                self.editor.setPlainText(pcur.entries[self.current_entry_index])
                self.editor.blockSignals(False)

        msg = self.tr("msg_imp_dir_done").format(
            imported=imported, found=len(found), skipped=len(skipped), errors=len(errors))
        if skipped:
            msg += "\n\n" + self.tr("msg_imp_dir_skipped") + "\n" + "\n".join(skipped[:15])
            if len(skipped) > 15: msg += f"\n… (+{len(skipped) - 15})"
        if errors:
            msg += "\n\n" + self.tr("msg_err") + ":\n" + "\n".join(errors[:10])
        if errors:
            QMessageBox.warning(self, self.tr("msg_err"), msg)
        else:
            QMessageBox.information(self, self.tr("msg_ok"), msg)

    def _transfer_lang(self):
        if not self.current_file: return
        target_fp, _ = QFileDialog.getOpenFileName(self, "Select TARGET base file", "", self.FTYPES_ALL)
        if not target_fp: return
        target = UKDParser()
        try: target.parse_file(target_fp)
        except Exception as e: return QMessageBox.critical(self, self.tr("msg_err"), str(e))

        out_fp, _ = QFileDialog.getSaveFileName(self, "Save new file as...", os.path.basename(target_fp))
        if not out_fp: return

        src = self.file_parsers[self.current_file]
        common = min(len(src.entries), len(target.entries))
        for i in range(common): target.entries[i] = src.entries[i]

        try:
            target.save_file(out_fp)
            QMessageBox.information(self, self.tr("msg_ok"), f"Transfer OK: {common}")
        except Exception as e: QMessageBox.critical(self, self.tr("msg_err"), str(e))

    def _batch_transfer_folders(self):
        src_dir = QFileDialog.getExistingDirectory(self, self.tr("d_trans_1"))
        if not src_dir: return
        tgt_dir = QFileDialog.getExistingDirectory(self, self.tr("d_trans_2"))
        if not tgt_dir: return
        out_dir = QFileDialog.getExistingDirectory(self, self.tr("d_trans_3"))
        if not out_dir: return

        src_files = {}
        for ext in self.EXTS_ALL:
            for fp in glob.glob(os.path.join(src_dir, f"*{ext}")):
                src_files[os.path.splitext(os.path.basename(fp))[0]] = fp

        matched = []
        for ext in self.EXTS_ALL:
            for fp in glob.glob(os.path.join(tgt_dir, f"*{ext}")):
                base = os.path.splitext(os.path.basename(fp))[0]
                if base in src_files:
                    matched.append((base, src_files[base], fp))

        if not matched: return QMessageBox.warning(self, self.tr("msg_err"), self.tr("d_trans_err"))

        d = QDialog(self)
        d.setWindowTitle(self.tr("d_trans_title"))
        d.resize(800, 500)
        lay = QVBoxLayout(d)
        log = QTextEdit()
        lay.addWidget(log)
        d.show()

        ok, err = 0, 0
        for base, s_fp, t_fp in matched:
            try:
                s_p = UKDParser(); s_p.parse_file(s_fp)
                t_p = UKDParser(); t_p.parse_file(t_fp)
                c = min(len(s_p.entries), len(t_p.entries))
                for i in range(c): t_p.entries[i] = s_p.entries[i]

                out_path = os.path.join(out_dir, base + os.path.splitext(t_fp)[1].lower())
                t_p.save_file(out_path)
                log.append(f"✅ {base}: {c} OK.")
                ok += 1
            except Exception as e:
                log.append(f"❌ {base}: ERROR - {e}")
                err += 1

        log.append(f"\nDONE! OK: {ok}, ERROR: {err}")

    # --- INNE ---
    def _mass_search_dialog(self):
        if not self.file_parsers: return
        d = QDialog(self)
        d.setWindowTitle(self.tr("menu_mass_search"))
        d.resize(800, 500)
        lay = QVBoxLayout(d)

        top = QHBoxLayout()
        fe = QLineEdit(); fe.setPlaceholderText(self.tr("search_find"))
        re_ = QLineEdit(); re_.setPlaceholderText(self.tr("search_replace"))
        top.addWidget(fe); top.addWidget(re_)
        lay.addLayout(top)

        res = QTableWidget()
        res.setColumnCount(4)
        res.setHorizontalHeaderLabels(["Plik/File", "ID", "Tekst/Text", "Ścieżka/Path"])
        res.horizontalHeader().setSectionResizeMode(2, QHeaderView.Stretch)
        lay.addWidget(res)
        lbl = QLabel("")
        lay.addWidget(lbl)

        def do_find():
            res.setRowCount(0)
            q = fe.text()
            if not q: return
            c = 0
            for fp, parser in self.file_parsers.items():
                for i, txt in enumerate(parser.entries):
                    if q in txt:
                        res.insertRow(res.rowCount())
                        res.setItem(res.rowCount() - 1, 0, QTableWidgetItem(os.path.basename(fp)))
                        res.setItem(res.rowCount() - 1, 1, QTableWidgetItem(str(i)))
                        res.setItem(res.rowCount() - 1, 2, QTableWidgetItem(self._pv(txt)))
                        res.setItem(res.rowCount() - 1, 3, QTableWidgetItem(fp))
                        c += 1
            lbl.setText(self.tr("search_found") + str(c))

        def do_replace():
            q, r = fe.text(), re_.text()
            if not q: return
            for fp, parser in self.file_parsers.items():
                for i, txt in enumerate(parser.entries):
                    if q in txt: parser.entries[i] = txt.replace(q, r)
            self.set_modified(True)
            self._refresh_table()
            do_find()
            lbl.setText(self.tr("search_replaced"))

        btns = QHBoxLayout()
        bf = QPushButton(self.tr("search_btn_find")); bf.clicked.connect(do_find)
        br = QPushButton(self.tr("search_btn_replace")); br.clicked.connect(do_replace)
        btns.addWidget(bf); btns.addWidget(br)
        lay.addLayout(btns)
        d.exec()

    def _edit_pointers(self):
        if not self.current_file: return
        p = self.file_parsers[self.current_file]
        d = QDialog(self)
        d.setWindowTitle(self.tr("menu_edit_pointers"))
        d.resize(700, 500)
        lay = QVBoxLayout(d)
        tab = QTableWidget()
        tab.setColumnCount(4)
        tab.setHorizontalHeaderLabels(["IDX", "Pointer Value", "Entry ID", "Offset"])
        lay.addWidget(tab)

        for pi, ptr_val in enumerate(p.pointer_table):
            tab.insertRow(tab.rowCount())
            tab.setItem(tab.rowCount() - 1, 0, QTableWidgetItem(str(pi)))
            tab.setItem(tab.rowCount() - 1, 1, QTableWidgetItem(str(ptr_val)))
            mapping = p.pointer_to_entry.get(pi)
            if mapping:
                tab.setItem(tab.rowCount() - 1, 2, QTableWidgetItem(str(mapping[0])))
                tab.setItem(tab.rowCount() - 1, 3, QTableWidgetItem(str(mapping[1])))
            else:
                tab.setItem(tab.rowCount() - 1, 2, QTableWidgetItem("NULL"))
                tab.setItem(tab.rowCount() - 1, 3, QTableWidgetItem("-"))
        d.exec()

    def _hex_view(self):
        if self.current_entry_index < 0: return
        p = self.file_parsers[self.current_file]
        d = QDialog(self)
        d.setWindowTitle(self.tr("menu_hex"))
        d.resize(800, 500)
        lay = QVBoxLayout(d)
        txt = QTextEdit()
        txt.setFontFamily("Consolas")
        txt.setPlainText(p.get_raw_hex(self.current_entry_index))
        txt.setReadOnly(True)
        lay.addWidget(txt)
        d.exec()

    def _struct_view(self):
        if not self.current_file: return
        p = self.file_parsers[self.current_file]
        d = QDialog(self)
        d.setWindowTitle(self.tr("menu_struct"))
        d.resize(800, 500)
        lay = QVBoxLayout(d)
        txt = QTextEdit()
        txt.setFontFamily("Consolas")
        ls = [f"File: {self.current_file}", f"Size: {len(p.original_data)} bytes", "", "=== HEADER ===",
              f"header_size: {p.header_size}", f"pointer_count: {p.pointer_count}"]
        txt.setPlainText('\n'.join(ls))
        txt.setReadOnly(True)
        lay.addWidget(txt)
        d.exec()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    window = UKDEditorMainWindow()
    window.show()
    sys.exit(app.exec())
