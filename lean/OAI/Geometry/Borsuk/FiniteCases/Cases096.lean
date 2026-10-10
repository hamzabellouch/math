import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases095

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31475 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 2, 3, 9} → Q {3, 4, 6, 7} → T {1, 6, 7} → T {1, 4, 7} → T {0, 2, 7} → ¬ T {4, 7, 9} → ¬ Q {0, 2, 5, 9} → ¬ T {0, 2, 5} → ¬ Q {0, 2, 3, 8} → ¬ T {4, 6, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 8, 9} → False := by
  classical
  intro n167 n162 n127 n169 n154 a300 a59 a52 a13 n109 n163 n11 n153 n106 n195 n286 a240
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u0_121 n106 hv
  have u2_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u3_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2505 h hv u2_87 u1_115
  have u4_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h a300 hv
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u6_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c31474 h h0 hv n167 n162 n127 n169 u3_126 u5_88 n154 a52 a13 n109 n163 n153 n195 n286 a240
  have u7_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c178 h hv u6_12
  have u8_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c180 h hv u6_12
  have u9_102 : T {4, 5, 7} := by
    by_contra hv
    exact c18466 h a240 u6_12 hv
  have u10_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c203 h hv u3_126 n153 n162 u7_165 n167 n169
  have u11_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u10_158 n169 hv n167 n153 u7_165 n162
  have u12_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u0_121 u9_102 hv
  have u13_15 : T {0, 2, 9} := by
    by_contra hv
    exact c26896 h a300 n11 u11_14 hv
  have u14_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1906 h u0_121 n106 hv u12_119
  have u15_159 : Q {0, 2, 4, 9} := by
    by_contra hv
    exact c31473 h u8_166 hv n163 n127 n154 n169 u13_15
  exact c7241 h u15_159 a59 u4_95 u14_117

theorem c31476 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n114 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u4_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u5_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u6_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u7_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u6_240 hv
  have u8_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u1_2 u7_48 a49
  have u9_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u7_48 a49
  have u10_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u1_2 u7_48 a49
  have u11_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u7_48 a49
  have u12_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u1_2 u7_48 a49
  have u13_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u7_48 a49
  have u14_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u13_185 u12_276 u11_189 u10_280 u9_195 u8_286 u6_240
  have u15_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u2_121 hv n114
  have u16_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31472 h h0 hv n114 a49 n210
  have u17_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u2_121 hv u16_116
  have u18_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1884 h u2_121 hv n114 u16_116
  have u19_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1837 h u2_121 u17_105 hv u15_107
  have u20_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c1833 h u2_121 hv u17_105 u15_107
  have u21_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u10_280 hv u17_105 u11_189
  have u22_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6355 h hv u14_51 u17_105 u15_107
  have u23_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u6_240 hv u17_105
  have u24_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7689 h hv u7_48 u17_105
  have u25_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u2_121 hv u18_112
  have u26_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18468 h u6_240 hv u20_101
  have u27_52 : T {1, 4, 7} := by
    by_contra hv
    exact c776 h u21_245 hv
  have u28_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u21_245 hv
  have u29_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1566 h u21_245 u11_189 u10_280 hv u5_316 u4_322 u3_323
  have u30_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6427 h hv u27_52 u18_112
  have u31_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u29_300 hv
  have u32_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u29_300 hv
  have u33_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8625 h hv u14_51 u31_87 u17_105
  have u34_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2647 h hv u32_88 u18_112
  have u35_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8345 h hv u14_51 u31_87 u15_107
  have u36_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7549 h hv a49 u17_105
  exact c31475 h h0 u35_167 u36_162 u34_127 u33_169 u30_154 u29_300 u28_59 u27_52 u26_13 u25_109 u24_163 u23_11 u22_153 u19_106 u9_195 u8_286 u6_240

private theorem c31477 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 7} → ¬ Q {1, 3, 5, 8} → T {0, 2, 4} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 6, 7} → ¬ Q {3, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 8, 9} → T {3, 4, 6} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {4, 6, 9} → T {1, 4, 6} → Q {1, 3, 8, 9} → False := by
  classical
  intro a13 n233 a10 n158 n218 n177 n268 n141 n126 n153 n164 n298 n243 n157 n169 a87 n162 n256 n311 n107 a51 a240
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u4_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv a51 u3_100
  have u5_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h a240 a13 hv
  have u6_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27871 h hv u0_1 a10 a13
  have u7_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20163 h hv u1_9 a10 a13
  have u8_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18487 h a240 a10 hv a13
  have u9_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u2_121 u5_101 hv n107
  have u10_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1394 h hv n177 n233 n268 n298 u6_307 n311
  have u11_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv n177 n233 n268 n298 u6_307 u10_309 n311
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c854 h hv n141 n218 n233 n243 u7_252 n256
  have u13_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv n141 n218 n233 n243 u7_252 u12_254 n256
  have u14_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c178 h hv u8_12
  have u15_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8485 h hv a51 a87 u9_106
  have u16_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2372 h hv u11_93 n107
  have u17_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6152 h hv u13_57 n107
  have u18_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c209 h hv n126 n153 n158 n162 u14_165 n169
  exact c182 h a13 u16_125 u17_152 n157 u4_161 n164 u18_167 u15_168

theorem c31478 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a112 a105 a49 n210
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u7_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u8_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u9_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u8_240 hv
  have u10_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u6_2 u9_48 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u5_37 u9_48 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u6_2 u9_48 a49
  have u13_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u5_37 u9_48 a49
  have u14_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u6_2 u9_48 a49
  have u15_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u5_37 u9_48 a49
  have u16_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u15_185 u14_276 u13_189 u12_280 u11_195 u10_286 u8_240
  have u17_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u12_280 hv a105 u13_189
  have u18_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1566 h u17_245 u13_189 u12_280 hv u2_316 u3_322 u4_323
  have u19_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u18_300 hv
  have u20_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8625 h hv u16_51 u19_87 a105
  have u21_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u18_300 hv
  have u22_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u17_245 hv
  have u23_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u8_240 hv a105
  have u24_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7549 h hv a49 a105
  have u25_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20703 h hv u1_9 a105
  have u26_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28403 h hv u0_1 a105
  have u27_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u7_121 a105 hv
  have u28_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u29_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u7_121 hv u28_114
  have u30_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u8_240 hv
  have u31_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u8_240 hv
  have u32_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u7_121 hv a112
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6849 h hv a49 a112
  have u34_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1879 h u7_121 hv a112 u28_114
  have u35_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1860 h u7_121 u29_107 u32_109 hv
  have u36_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1854 h u7_121 hv u29_107 u32_109
  have u37_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c1535 h hv u34_103
  have u38_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u34_103
  have u39_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u7_121 u34_103 hv
  have u40_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u7_121 u35_110 hv
  have u41_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7955 h hv u31_64 u30_100 u35_110
  have u42_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u7_121 u36_104 hv
  have u43_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6297 h hv u22_59 u36_104
  have u44_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2517 h hv u21_95 u36_104
  have u45_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4725 h hv u21_95 a105 u39_118
  have u46_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22505 h hv u22_59 a105 u39_118
  have u47_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9763 h hv u22_59 a105 u39_118
  have u48_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15505 h hv u21_95 a105 u39_118
  have u49_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7101 h hv u22_59 u21_95 u39_118
  have u50_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18462 h u8_240 hv u40_111
  have u51_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17062 h hv u23_11 u42_117
  have u52_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18323 h hv u50_10 a112
  have u53_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17483 h hv u50_10 u39_118
  have u54_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18043 h hv u50_10 u28_114
  have u55_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c31477 h h0 hv u53_233 u50_10 u49_158 u48_218 u47_177 u46_268 u45_141 u44_126 u43_153 u41_164 u38_298 u37_243 u33_157 u20_169 u19_87 u24_162 u25_256 u26_311 u29_107 u16_51 u8_240
  have u56_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c193 h hv u55_13
  have u57_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u8_240 u55_13 hv
  have u58_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c207 h hv u44_126 u43_153 u49_158 u24_162 u56_167 u20_169
  have u59_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u49_158 u20_169 hv u56_167 u43_153 u58_165 u24_162
  have u60_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u7_121 u57_101 hv
  have u61_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1831 h u7_121 u57_101 a105 hv
  have u62_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c18567 h u8_240 hv u57_101 a105
  have u63_15 : T {0, 2, 9} := by
    by_contra hv
    exact c26896 h u18_300 u23_11 u59_14 hv
  have u64_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u15_185 hv u60_120
  have u65_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u55_13 u61_106
  have u66_77 : T {2, 5, 7} := by
    by_contra hv
    exact c18472 h u8_240 u62_23 hv
  have u67_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c26875 h u18_300 u63_15 hv
  have u68_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c736 h u8_240 hv n210 u51_230 u65_234 u54_237 u52_239
  have u69_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c3515 h u68_133 u64_71 u66_77 hv
  exact c26984 h u18_300 u67_57 u69_78 u27_116

end BorsukNine.FiniteObstruction

end OAI
