import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases093

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31463 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 6, 7} → ¬ T {4, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 6, 7} → False := by
  classical
  intro n59 n105 n201 n195 n292 n286
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c881 h hv n59
  have u5_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c883 h hv n59
  have u6_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u4_251 n195
  have u7_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u5_257 n292 u3_322 u2_326 u1_330
  have u8_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1894 h u0_121 n105 u6_111 hv
  exact c1742 h u8_117 n201 u5_257 n292 u7_312 u3_322 u2_326 u1_330

theorem c31464 (h : TenSystem T Q) :
    ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 8, 9} → T {0, 2, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n158 n169 a14 n167 n153 n165 n162
  have u0_126 : Q {0, 1, 2, 8} := by
    by_contra hv
    exact c197 h a14 hv n153 n158 n162 n165 n167 n169
  exact c199 h u0_126 n153 n158 n162 n165 n167 n169

private theorem c31465 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → T {1, 4, 6} → ¬ T {4, 5, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n114 a51 n103 a230 n240 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u5_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u6_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8275 h hv u5_44 a51 u4_54
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u3_121 n103 hv
  have u8_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv a230 a49
  have u10_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13033 h hv u1_37 u5_44 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u5_44 a49
  have u12_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25805 h hv u0_2 u5_44 a49
  have u13_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24965 h hv u0_2 u5_44 a49
  have u14_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv n114
  have u15_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u3_121 n103 n114 hv
  have u16_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u3_121 n103 hv n114
  have u17_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u3_121 u14_107 hv u7_118
  have u18_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u3_121 u14_107 u7_118 hv
  have u19_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u3_121 hv u15_116
  have u20_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27423 h hv u2_1 u16_112
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv u16_112
  have u22_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1816 h u3_121 hv u17_113
  have u23_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u3_121 hv u18_119
  have u24_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7269 h hv a49 u22_108
  have u25_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7969 h hv a49 u23_102
  have u26_59 : T {1, 6, 7} := by
    by_contra hv
    exact c31463 h h0 hv u19_105 u10_201 u11_195 u12_292 u13_286
  have u27_56 : ¬ T {1, 5, 7} := by
    intro hv
    exact c31462 h h0 u26_59 hv u25_165 u24_160 u21_13 u20_304 u15_116 n114 a51 u7_118 u8_298 u10_201 u12_292 a230 n240
  have u28_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c836 h hv u27_56
  have u29_247 : Q {1, 4, 6, 9} := by
    by_contra hv
    exact c31460 h h0 u27_56 n114 hv u11_195 u13_286 a230
  have u30_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 u13_286 hv u28_251 u11_195
  have u31_61 : T {1, 6, 9} := by
    by_contra hv
    exact c909 h u29_247 hv
  have u32_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u30_111
  have u33_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6409 h hv u31_61 u14_107 u7_118
  have u34_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c19449 h u29_247 u32_14 hv
  have u35_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8648 h hv u27_56 u34_92 u30_111
  have u36_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7082 h hv u27_56 u34_92 u30_111
  exact c31464 h u36_158 u35_169 u32_14 u6_167 u33_153 u25_165 u9_162

theorem c31466 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 6} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n46 n240 a49 n210
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
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
    exact c24965 h hv u0_2 u4_44 a49
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u4_44 a49
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u1_37 u4_44 a49
  have u9_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c31440 h h0 hv u3_230 a49
  have u10_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv u3_230 a49
  have u11_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31447 h h0 u10_162 hv u9_237 u8_198 u7_195 u6_286 u5_196 u3_230 n240 n210
  have u12_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u2_121 u11_103 hv
  have u13_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13033 h hv u1_37 u4_44 a49
  have u14_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25805 h hv u0_2 u4_44 a49
  have u15_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u0_2 u4_44 a49
  have u16_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h u3_230 hv
  have u17_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c682 h hv n46
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31461 h h0 hv n46 u11_103 u9_237 u8_198 u13_201 u7_195 u14_292 u15_289 u6_286 u3_230 n240 n210
  have u19_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31465 h h0 hv u18_51 u11_103 u3_230 n240 a49
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h u3_230 hv u19_114
  have u21_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv u19_114 u8_198 u15_289
  have u22_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c28135 h u21_309 hv u18_51
  have u23_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28195 h u21_309 hv u18_51 u16_54
  have u24_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28197 h u21_309 hv u18_51 u16_54
  have u25_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u23_3
  have u26_82 : T {2, 6, 9} := by
    by_contra hv
    exact c28124 h u21_309 u23_3 hv
  have u27_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u24_38
  have u28_33 : T {0, 6, 9} := by
    by_contra hv
    exact c28140 h u21_309 hv u24_38
  have u29_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16611 h hv u28_33 u26_82 u12_118
  have u30_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c17049 h hv u28_33 u26_82 u12_118
  have u31_228 : Q {1, 3, 4, 7} := by
    by_contra hv
    exact c661 h u3_230 u25_128 u27_205 u29_226 u17_227 hv u30_229
  have u32_116 : T {5, 8, 9} := by
    by_contra hv
    exact c16784 h u31_228 u20_12 hv
  have u33_112 : T {5, 6, 8} := by
    by_contra hv
    exact c16788 h u31_228 u22_15 hv
  exact c1885 h u2_121 u33_112 u19_114 u32_116

theorem c31467 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 6} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {2, 4, 7, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ T {4, 5, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro a51 n167 n161 n192 n283 n186 n277 n103 a230 n240 a49
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u4_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u4_37 u7_44 a49
  have u9_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u3_2 u7_44 a49
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31465 h h0 hv a51 n103 a230 n240 a49
  have u12_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u11_114
  have u13_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv u11_114 u8_198 u9_289
  have u14_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c176 h hv u12_12
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1393 h u13_309 hv
  have u16_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u13_309 u8_198 hv u9_289 u2_319 u1_326 u0_329
  have u17_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c28135 h u13_309 hv a51
  have u18_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28195 h u13_309 hv a51 u10_54
  have u19_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28197 h u13_309 hv a51 u10_54
  have u20_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8393 h hv a51 u15_93
  have u21_57 : T {1, 5, 8} := by
    by_contra hv
    exact c853 h u16_254 hv
  have u22_10 : T {0, 2, 4} := by
    by_contra hv
    exact c20448 h u16_254 hv u12_12 u17_15
  have u23_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c41 h hv u18_3
  have u24_82 : T {2, 6, 9} := by
    by_contra hv
    exact c28124 h u13_309 u18_3 hv
  have u25_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c566 h hv u19_38
  have u26_33 : T {0, 6, 9} := by
    by_contra hv
    exact c28140 h u13_309 hv u19_38
  have u27_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c28131 h u13_309 u22_10 hv
  have u28_97 : ¬ T {3, 6, 9} := by
    intro hv
    exact c20425 h u16_254 u22_10 hv
  have u29_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8953 h hv u21_57 u24_82
  have u30_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21699 h hv u26_33 u21_57
  have u31_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6158 h hv u27_61 n103
  have u32_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2378 h hv u28_97 n103
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u32_125 u31_152 n161 u14_164 n167 u20_168
  have u34_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c182 h hv u32_125 u31_152 u33_157 n161 u14_164 n167 u20_168
  have u35_112 : T {5, 6, 8} := by
    by_contra hv
    exact c17066 h a230 u34_13 hv
  have u36_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17082 h a230 hv u12_12 u34_13
  have u37_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17088 h a230 u12_12 u34_13 hv
  have u38_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24623 h hv u3_2 u35_112
  have u39_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11883 h hv u4_37 u35_112
  have u40_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1885 h u6_121 u35_112 u11_114 hv
  have u41_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19183 h hv u5_9 u36_11 u37_14
  have u42_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1092 h hv u33_157 u25_213 u30_263 n277 n283 u38_284
  have u43_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c357 h hv u23_136 u33_157 u29_172 n186 n192 u39_193
  have u44_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u6_121 hv u40_116
  exact c31281 h h0 u42_280 u41_245 u44_105 u43_189

theorem c31468 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → ¬ T {1, 4, 6} → T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a114 n51 a46 n103 n237 n198 n289 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv a114
  have u6_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u7_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8103 h hv u4_44 a114
  have u8_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv a114 n198 n289
  have u9_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18326 h hv u6_12 n103
  have u10_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u8_309 n198 hv n289 u3_319 u2_326 u1_329
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c28134 h u8_309 hv n51
  have u12_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28240 h u8_309 hv n51 u5_107
  have u13_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28244 h u8_309 n51 hv u5_107
  have u14_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c20437 h u10_254 u12_23 hv
  have u15_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv u13_72 a114
  have u16_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c1038 h hv u14_70
  have u17_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c728 h a230 u15_133 n210 hv n237 u9_239 n240
  have u18_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h u17_234 hv
  have u19_168 : Q {0, 2, 7, 9} := by
    by_contra hv
    exact c31453 h h0 u17_234 u16_154 a230 u11_15 u8_309 u7_166 hv
  exact c8403 h u19_168 u4_44 u18_45 a46

end BorsukNine.FiniteObstruction

end OAI
