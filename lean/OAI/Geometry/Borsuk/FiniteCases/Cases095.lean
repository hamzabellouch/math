import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases094

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31469 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n240 a49 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u3_230 : Q {1, 3, 4, 9} := by
    by_contra hv
    exact c31437 h h0 hv n240 n210 a49
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h u3_230 hv
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12333 h hv u1_37 u4_44 a49
  have u6_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24965 h hv u2_2 u4_44 a49
  have u7_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u2_2 u4_44 a49
  have u8_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u4_44 a49
  have u9_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u1_37 u4_44 a49
  have u10_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c31440 h h0 hv u3_230 a49
  have u11_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv u3_230 a49
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31447 h h0 u11_162 hv u10_237 u9_198 u8_195 u6_286 u5_196 u3_230 n240 n210
  have u13_46 : T {1, 3, 6} := by
    by_contra hv
    exact c31466 h h0 hv n240 a49 n210
  have u14_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23705 h hv u2_2 u13_46 a49
  have u15_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u13_46 a49
  have u16_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24547 h hv u2_2 u13_46 a49
  have u17_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11775 h hv u1_37 u13_46 a49
  have u18_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7425 h hv u4_44 u13_46 a49
  have u19_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25663 h hv u2_2 u4_44 u13_46
  have u20_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12891 h hv u1_37 u4_44 u13_46
  have u21_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8267 h hv u4_44 u13_46 a49
  have u22_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c31467 h h0 hv u21_167 u18_161 u17_192 u16_283 u15_186 u14_277 u12_103 u3_230 n240 a49
  have u23_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31468 h h0 hv u22_51 u13_46 u12_103 u10_237 u9_198 u7_289 u3_230 n240 n210
  have u24_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u0_121 u12_103 u23_114 hv
  have u25_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u0_121 u12_103 hv u23_114
  have u26_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u24_116 u20_200 hv u19_291
  have u27_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h u3_230 hv u25_112
  exact c28414 h u26_311 u27_13 u22_51

theorem c31470 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 8, 9} → False := by
  classical
  intro n51 n185 n276 n189 n280 n195 n286 a240
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h a240 hv
  have u8_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c757 h hv n51
  have u9_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c759 h hv n51
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u11_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31261 h h0 n185 u9_241 hv n276
  have u12_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c1510 h hv n185 u9_241 n276 u4_316 u1_317 u0_318
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 n280 u10_245 hv n189
  have u14_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1570 h hv n189 u10_245 n280 u4_316 u3_322 u2_323
  have u15_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u6_121 u11_101 hv
  have u16_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8626 h hv n51 u11_101 u13_105
  have u17_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6490 h hv n51 u11_101 u13_105
  have u18_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6350 h hv n51 u11_101 u13_105
  have u19_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18468 h a240 hv u11_101
  have u20_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1810 h u6_121 u13_105 hv
  have u21_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h a240 hv u13_105
  have u22_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1832 h u6_121 u11_101 u13_105 hv
  have u23_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1937 h u6_121 hv u20_116 u15_120
  have u24_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21681 h hv u7_64 u20_116 u15_120
  have u25_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8939 h hv u7_64 u20_116 u15_120
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27031 h hv u5_1 u21_11 u19_13
  have u27_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18489 h a240 u21_11 hv u19_13
  have u28_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27171 h hv u5_1 u21_11 u19_13
  have u29_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c18485 h a240 hv u21_11 u19_13
  have u30_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1815 h u6_121 u22_107 hv
  have u31_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u6_121 u23_110 hv
  have u32_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c1292 h hv u25_171 u8_227 u24_262 u12_296 u14_300 u26_301 u28_302
  have u33_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c178 h hv u27_12
  have u34_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c180 h hv u27_12
  have u35_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c148 h hv u29_10
  have u36_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c150 h hv u29_10
  have u37_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u31_111 hv n195
  have u38_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2644 h hv u32_87 u30_114
  have u39_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8342 h hv n51 u32_87 u11_101
  have u40_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7774 h hv n51 u32_87 u13_105
  have u41_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8482 h hv n51 u32_87 u11_101
  have u42_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7634 h hv n51 u32_87 u13_105
  have u43_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u35_158 u16_169 hv u39_167 u18_153 u33_165 u42_162
  have u44_15 : T {0, 2, 9} := by
    by_contra hv
    exact c20028 h u37_251 u29_10 u43_14 hv
  exact c31451 h u40_163 u38_127 u36_159 u17_154 u44_15 u34_166 u41_168

private theorem c31471 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 7} → T {5, 8, 9} → T {1, 4, 6} → Q {1, 3, 8, 9} → False := by
  classical
  intro a13 a116 a51 a240
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u3_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h a240 hv u2_105
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u0_9 a116
  have u5_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u6_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h a240 a13 hv
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18605 h hv a13 u5_100
  have u8_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16645 h hv a13 a116
  have u9_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19323 h hv u0_9 u3_11 a13
  have u10_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19463 h hv u0_9 u3_11 a13
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u1_121 u6_101 hv
  have u12_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14681 h hv u5_100 a116 u11_120
  have u13_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3901 h hv u5_100 a116 u11_120
  exact c752 h a51 u13_135 u12_212 u8_227 u7_241 u4_245 u9_246 u10_247

theorem c31472 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {5, 7, 8} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a116 n114 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u2_121 hv n114
  have u4_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u5_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u4_240 hv
  have u6_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u1_2 u5_48 a49
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u5_48 a49
  have u8_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u1_2 u5_48 a49
  have u9_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u5_48 a49
  have u10_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u1_2 u5_48 a49
  have u11_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u5_48 a49
  have u12_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u11_185 u10_276 u9_189 u8_280 u7_195 u6_286 u4_240
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv a116
  have u14_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h u4_240 hv u13_105
  have u15_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c31471 h h0 hv a116 u12_51 u4_240
  have u16_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u4_240 u15_13 hv
  have u17_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u2_121 u16_101 hv
  have u18_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1835 h u2_121 u16_101 hv u3_107
  have u19_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1920 h u2_121 hv n114 u17_120
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1924 h u2_121 n114 hv u17_120
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u11_185 hv u17_120
  have u22_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u15_13 u18_106
  have u23_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18045 h hv u14_11 u19_108
  have u24_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u2_121 hv u20_117
  have u25_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17063 h hv u14_11 u20_117
  have u26_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c18561 h u4_240 u21_71 u16_101 hv
  have u27_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3483 h hv u21_71 u20_117
  have u28_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u4_240 hv u26_102
  have u29_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1828 h u2_121 u26_102 hv u24_104
  have u30_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c736 h u4_240 u27_133 n210 u25_230 u22_234 u23_237 hv
  exact c18327 h u30_239 u28_12 u29_103

theorem c31473 (h : TenSystem T Q) :
    ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 8, 9} → T {0, 2, 9} → False := by
  classical
  intro n166 n159 n163 n127 n154 n169 a15
  have u0_168 : Q {0, 2, 7, 9} := by
    by_contra hv
    exact c212 h a15 n127 n154 n159 n163 n166 hv n169
  exact c224 h u0_168 n127 n154 n159 n163 n166 n169

theorem c31474 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 6} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 1, 2, 8} → T {3, 4, 7} → ¬ Q {0, 2, 3, 9} → T {1, 4, 7} → T {0, 2, 7} → ¬ T {4, 7, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 8, 9} → False := by
  classical
  intro a12 n167 n162 n127 n169 n126 a88 n154 a52 a13 n109 n163 n153 n195 n286 a240
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c18487 h a240 hv a12 a13
  have u2_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c18467 h a240 a12 hv
  have u3_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c148 h hv u1_10
  have u4_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c150 h hv u1_10
  have u5_111 : T {5, 6, 7} := by
    by_contra hv
    exact c18462 h a240 u1_10 hv
  have u6_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1842 h u0_121 u2_102 hv n109
  have u7_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c207 h hv n126 n153 u3_158 n162 n167 n169
  have u8_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u5_111 hv n195
  have u9_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8205 h hv a52 a88 u6_108
  have u10_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u3_158 n169 hv n167 n153 u7_165 n162
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c20028 h u8_251 u1_10 u10_14 hv
  exact c31473 h u9_166 u4_159 n163 n127 n154 n169 u11_15

end BorsukNine.FiniteObstruction

end OAI
