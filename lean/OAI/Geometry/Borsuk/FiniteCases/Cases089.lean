import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases088

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31420 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {0, 2, 4, 8} → T {5, 6, 7} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → Q {0, 1, 3, 9} → Q {1, 3, 7, 9} → False := by
  classical
  intro n103 n158 a111 n194 n187 n190 a133 a239
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3489 h a133 hv a111
  have u2_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 n103 hv
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv n103
  have u4_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18430 h a239 hv u1_74 n103
  have u5_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv u3_80 a111 u2_118
  have u6_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv u3_80 a111 u2_118
  have u7_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c374 h hv u6_137 n158 u5_173 n187 n190 n194
  exact c362 h u4_25 u6_137 n158 u5_173 n187 n190 u7_192 n194

theorem c31421 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 5, 8} → T {4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → False := by
  classical
  intro n243 a103 n187 n278
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u2_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u3_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1540 h hv n187 n243 n278 u2_317 u1_319 u0_321
  exact c1532 h a103 n187 n243 n278 u3_298 u2_317 u1_319 u0_321

private theorem c31422 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 2, 3, 9} → T {1, 3, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro n234 n237 n230 n210 a49 n240
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u6_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u7_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31392 h n237 n210 n230 n234 a49 n240 hv
  have u8_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u7_239 hv
  have u9_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c734 h u7_239 hv n210 n230 n234 n237 n240
  have u10_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11495 h hv u6_37 u8_47 a49
  have u11_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12335 h hv u6_37 u8_47 a49
  have u12_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23847 h hv u5_2 u8_47 a49
  have u13_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11075 h hv u6_37 u8_47 a49
  have u14_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24267 h hv u5_2 u8_47 a49
  have u15_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25107 h hv u5_2 u8_47 a49
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10793 h hv u6_37 u8_47 a49
  have u17_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23565 h hv u5_2 u8_47 a49
  have u18_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h u9_133 hv
  have u19_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h u9_133 hv
  have u20_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31410 h h0 hv u9_133 u7_239 a49 n210
  have u21_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u20_110
  have u22_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u4_121 u20_110 hv
  have u23_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c6989 h hv a49 u22_111
  have u24_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3489 h u9_133 hv u22_111
  have u25_27 : T {0, 5, 6} := by
    by_contra hv
    exact c18336 h u7_239 hv u24_74
  have u26_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c31419 h h0 hv u20_110 u18_8 u14_281 u13_187 u12_278 u10_190
  have u27_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31420 h h0 hv u23_158 u22_111 u21_194 u13_187 u10_190 u9_133 u7_239
  have u28_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18327 h u7_239 hv u27_103
  have u29_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h u9_133 hv u27_103
  have u30_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c174 h hv u28_12
  have u31_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1196 h hv u29_80
  have u32_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u27_103 u13_187 u12_278
  have u33_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c18915 h u32_243 u0_9 hv u19_21
  have u34_82 : T {2, 6, 9} := by
    by_contra hv
    exact c18954 h u32_243 u28_12 u29_80 hv
  have u35_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u32_243 u13_187 u12_278 hv u1_317 u2_319 u3_321
  have u36_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c18913 h u32_243 u0_9 hv u19_21
  have u37_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15104 h hv u33_19 u20_110
  have u38_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c26587 h u35_298 hv u34_82
  have u39_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c264 h hv u36_18
  have u40_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22104 h hv u38_6 u20_110
  have u41_76 : T {2, 5, 6} := by
    by_contra hv
    exact c31412 h h0 hv u39_175 u26_139 u25_27 u16_185 u11_196 u9_133
  have u42_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u30_160 u37_216 u40_266 u17_276 u31_286 u15_287
  exact c1127 h u41_76 u30_160 u37_216 u40_266 u17_276 u31_286 u15_287 u42_288

theorem c31423 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n237 n230 n210 n240 a49
  have u0_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c31405 h h0 hv n237 n230 n240 a49 n210
  exact c31422 h h0 u0_234 n237 n230 n210 a49 n240

private theorem c31425 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n103 a239 a237
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u6_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u7_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u8_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u9_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u10_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12055 h hv u1_37 u8_46 u9_47
  have u11_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c11211 h hv u1_37 u8_46 u9_47
  have u12_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c23983 h hv u0_2 u8_46 u9_47
  have u13_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u7_121 n103 hv
  have u14_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18326 h a239 hv n103
  have u15_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u16_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27595 h hv u2_1 u14_12 u15_13
  have u17_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19887 h hv u3_9 u14_12 u15_13
  have u18_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26751 h hv u2_1 u14_12 u15_13
  have u19_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19043 h hv u3_9 u14_12 u15_13
  have u20_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31402 h h0 u17_250 hv u16_305 u10_194
  have u21_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1547 h hv u11_188 u19_244 u12_279 u18_299 u6_318 u5_320 u4_321
  have u22_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u7_121 u20_110 hv
  have u23_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1808 h u7_121 u21_104 hv
  exact c1901 h u7_121 u22_111 u23_117 u13_118

private theorem c31426 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 5} → Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n11 a239 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31425 h h0 hv a239 a237
  have u2_108 : T {4, 7, 8} := by
    by_contra hv
    exact c18044 h a237 n11 hv
  have u3_106 : T {4, 6, 8} := by
    by_contra hv
    exact c18324 h a239 n11 hv
  exact c1847 h u0_121 u1_103 u3_106 u2_108

theorem c31427 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → T {1, 3, 9} → False := by
  classical
  intro a239 a237 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u7_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12615 h hv u5_37 u6_46 a49
  have u8_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24547 h hv u0_2 u6_46 a49
  have u9_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23845 h hv u0_2 u6_46 a49
  have u10_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11073 h hv u5_37 u6_46 a49
  have u11_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u5_37 u6_46 a49
  have u12_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u13_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u14_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1475 h a239 hv
  have u15_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24267 h hv u0_2 u13_47 a49
  have u16_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7009 h hv u6_46 u13_47 a49
  have u17_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24827 h hv u0_2 u6_46 u13_47
  have u18_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31425 h h0 hv a239 a237
  have u19_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv u18_103
  have u20_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u18_103 u10_187 u9_278
  have u21_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c189 h hv u19_13
  have u22_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c18995 h u20_243 hv u12_97 u14_99
  have u23_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18997 h u20_243 hv u12_97 u14_99
  have u24_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18894 h u20_243 u22_21 hv
  have u25_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u20_243 u10_187 u9_278 hv u3_317 u2_319 u1_321
  have u26_31 : T {0, 6, 7} := by
    by_contra hv
    exact c18896 h u20_243 hv u23_70
  have u27_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c26589 h u25_298 hv u24_80
  have u28_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26597 h u25_298 u26_31 hv
  have u29_11 : T {0, 2, 5} := by
    by_contra hv
    exact c31426 h h0 hv a239 a237
  have u30_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c18045 h a237 u29_11 hv
  have u31_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c18325 h a239 u29_11 hv
  have u32_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1852 h u4_121 u31_106 u30_108 hv
  have u33_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4468 h hv u23_70 u31_106
  have u34_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9508 h hv u28_43 u31_106
  have u35_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u4_121 u32_110 hv
  have u36_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12163 h hv u5_37 u32_110
  have u37_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c421 h hv u33_140 u21_161 u34_176 u11_186 u36_195 u7_198
  have u38_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c407 h hv u33_140 u21_161 u34_176 u11_186 u36_195 u7_198 u37_199
  have u39_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14828 h hv u22_21 u35_111
  have u40_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21828 h hv u27_8 u35_111
  have u41_74 : T {2, 4, 8} := by
    by_contra hv
    exact c18056 h a237 u38_28 hv
  exact c1097 h u41_74 u16_158 u39_214 u40_264 u9_278 u15_281 u8_283 u17_285

end BorsukNine.FiniteObstruction

end OAI
