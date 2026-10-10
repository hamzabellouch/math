import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases096

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31479 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 7} → T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n13 a105 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u3_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31478 h h0 hv a105 a49 n210
  have u5_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u1_121 hv u4_112
  have u6_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u1_121 hv a105 u5_109
  have u7_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u3_240 hv u6_102
  have u8_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17065 h hv u7_12 u2_114
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u1_121 a105 hv
  have u10_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1880 h u1_121 hv u4_112 u9_116
  have u11_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18327 h hv u7_12 u10_103
  have u12_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u3_240 hv a105
  have u13_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u1_121 a105 hv u5_109
  have u14_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18044 h hv u12_11 u13_108
  have u15_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u3_240 hv
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u15_48 a49
  have u17_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u3_240 n13 hv
  have u18_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u17_101 hv
  have u19_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1831 h u1_121 u17_101 a105 hv
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1922 h u1_121 u13_108 hv u18_120
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u16_185 hv u18_120
  have u22_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv n13 u19_106
  have u23_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3483 h hv u21_71 u20_117
  exact c736 h u3_240 u23_133 n210 u8_230 u22_234 u14_237 u11_239

private theorem c31480 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a105 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u8_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u6_121 hv u7_114
  have u9_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u10_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u9_240 hv
  have u11_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u9_240 hv
  have u12_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u1_2 u11_48 a49
  have u13_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u11_48 a49
  have u14_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u1_2 u11_48 a49
  have u15_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u11_48 a49
  have u16_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u1_2 u11_48 a49
  have u17_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u11_48 a49
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u17_185 u16_276 u15_189 u14_280 u13_195 u12_286 u9_240
  have u19_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv u18_51 u10_100
  have u20_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u6_121 a105 hv
  have u21_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20703 h hv u5_9 a105
  have u22_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7549 h hv a49 a105
  have u23_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u14_280 hv a105 u15_189
  have u24_52 : T {1, 4, 7} := by
    by_contra hv
    exact c776 h u23_245 hv
  have u25_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1566 h u23_245 u15_189 u14_280 hv u4_316 u3_322 u2_323
  have u26_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u25_300 hv
  have u27_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u25_300 hv
  have u28_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8625 h hv u18_51 u26_87 a105
  have u29_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31478 h h0 hv a105 a49 n210
  have u30_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv u29_112
  have u31_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u6_121 hv u29_112
  have u32_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1880 h u6_121 hv u29_112 u20_116
  have u33_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u6_121 a105 hv u31_109
  have u34_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u6_121 hv a105 u31_109
  have u35_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6363 h hv u24_52 a105 u31_109
  have u36_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15489 h hv u27_88 a105 u31_109
  have u37_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u27_88 a105 u31_109
  have u38_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u27_88 a105 u31_109
  have u39_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8065 h hv u24_52 u27_88 u31_109
  have u40_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7829 h hv a49 u32_103
  have u41_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u6_121 u33_108 hv
  have u42_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u9_240 hv u34_102
  have u43_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6847 h hv u11_48 u41_113
  have u44_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17485 h hv u42_12 u31_109
  have u45_13 : T {0, 2, 7} := by
    by_contra hv
    exact c31479 h h0 hv a105 a49 n210
  have u46_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h u9_240 u45_13 hv
  have u47_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c18487 h u9_240 hv u42_12 u45_13
  have u48_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18903 h hv u5_9 u42_12 u45_13
  have u49_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u6_121 u46_101 hv u8_107
  have u50_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c148 h hv u47_10
  have u51_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c854 h hv u38_141 u36_218 u44_233 u48_243 u30_252 u21_256
  have u52_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv u38_141 u36_218 u44_233 u48_243 u30_252 u51_254 u21_256
  have u53_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8485 h hv u18_51 u26_87 u49_106
  have u54_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c209 h hv u37_126 u35_153 u50_158 u22_162 u39_165 u28_169
  have u55_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6152 h hv u52_57 u8_107
  have u56_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c184 h hv u55_152 u43_157 u19_161 u40_164 u54_167 u53_168
  exact c182 h u45_13 u56_125 u55_152 u43_157 u19_161 u40_164 u54_167 u53_168

theorem c31481 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u5_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u6_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u7_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u6_240 hv
  have u8_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u6_240 hv
  have u9_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u6_240 hv
  have u10_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u5_2 u7_48 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u7_48 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u5_2 u7_48 a49
  have u13_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10935 h hv u0_37 u7_48 a49
  have u14_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u7_48 a49
  have u15_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u5_2 u7_48 a49
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u7_48 a49
  have u17_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u16_185 u15_276 u14_189 u12_280 u11_195 u10_286 u6_240
  have u18_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u19_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u1_121 hv u18_114
  have u20_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31480 h h0 hv a49 n210
  have u21_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1810 h u1_121 u20_105 hv
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1836 h u1_121 u20_105 hv u19_107
  have u23_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h u6_240 hv u20_105
  have u24_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1832 h u1_121 hv u20_105 u19_107
  have u25_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6975 h hv u8_64 u9_100 u21_116
  have u26_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1883 h u1_121 hv u18_114 u21_116
  have u27_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1885 h u1_121 hv u18_114 u21_116
  have u28_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u1_121 u22_106 hv
  have u29_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u0_37 u22_106
  have u30_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10587 h hv u17_51 u24_101 u22_106
  have u31_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8487 h hv u17_51 u24_101 u22_106
  have u32_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u24_101 hv
  have u33_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13423 h hv u0_37 u24_101
  have u34_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u16_185 hv u24_101 u15_276
  have u35_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1533 h hv u26_103
  have u36_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u1_121 u26_103 hv
  have u37_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u27_112
  have u38_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u16_185 hv u32_120
  have u39_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u34_241 hv
  have u40_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u34_241 hv
  have u41_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u34_241 u16_185 u15_276 hv u2_316 u3_317 u4_318
  have u42_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c18531 h u6_240 u23_11 u38_71 hv
  have u43_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c18555 h u6_240 hv u38_71 u24_101
  have u44_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c18561 h u6_240 u38_71 u24_101 hv
  have u45_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18533 h u6_240 u23_11 u38_71 hv
  have u46_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13015 h hv a49 u38_71
  have u47_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13155 h hv u7_48 u38_71
  have u48_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u41_296 hv
  have u49_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u41_296 hv
  have u50_24 : T {0, 4, 7} := by
    by_contra hv
    exact c18474 h u6_240 hv u42_76
  have u51_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18470 h u6_240 u43_22 hv
  have u52_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u44_102 hv
  have u53_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1828 h u1_121 u44_102 u26_103 hv
  have u54_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1872 h u1_121 u44_102 hv u28_115
  have u55_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5142 h hv u45_77 u44_102 u28_115
  have u56_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10184 h hv u45_77 u44_102 u28_115
  have u57_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5535 h hv u38_71 u48_86 u24_101
  have u58_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8057 h hv u39_50 u48_86 u53_104
  have u59_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13399 h hv u39_50 u38_71 u48_86
  have u60_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7075 h hv u40_55 u49_91 u54_111
  have u61_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv u51_80 u54_111 u36_118
  have u62_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv u51_80 u54_111 u36_118
  have u63_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9079 h hv u8_64 u21_116 u52_119
  have u64_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4041 h hv u9_100 u21_116 u52_119
  have u65_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12023 h hv u0_37 u54_111
  have u66_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c475 h hv u55_144 u58_165 u56_180 u37_196 u46_201 u59_203
  have u67_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c520 h hv u57_147 u31_168 u30_183 u29_199 u47_202 u33_204
  have u68_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c374 h hv u61_137 u60_158 u62_173 u35_187 u66_190 u65_194
  exact c347 h u50_24 u64_136 u25_157 u63_172 u13_186 u14_189 u68_192 u67_193

end BorsukNine.FiniteObstruction

end OAI
