import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases100

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31520 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a118 a304
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u4_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u5_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u6_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u8_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u9_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u7_109 a118 hv
  have u10_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u7_109 hv a118
  have u11_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u5_258 u6_313 a118 hv
  have u12_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u9_120
  have u13_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1719 h hv u10_115
  have u14_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1812 h u0_121 hv u10_115
  have u15_35 : T {0, 7, 9} := by
    by_contra hv
    exact c523 h u11_202 hv
  have u16_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u11_202 u5_258 hv u6_313 u3_323 u2_327 u1_330
  have u17_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1258 h u16_293 hv
  have u18_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19435 h hv u15_35 u17_84 u8_99
  have u19_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c31518 h h0 hv a118 a304
  have u20_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c31519 h h0 hv a118 a304
  have u21_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31288 h u13_310 u19_183 u12_315 u20_274 u6_313 u8_99 hv
  have u22_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u21_239 hv
  have u23_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h u21_239 hv
  have u24_63 : T {1, 7, 9} := by
    by_contra hv
    exact c937 h u21_239 hv
  have u25_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11495 h hv u4_37 u22_47 u23_49
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27135 h hv u15_35 u24_63 u17_84
  exact c31307 h h0 u18_246 u14_106 u26_301 u25_190

theorem c31521 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a239 a304
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u7_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u8_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv u7_118
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u2_37 u9_109
  have u11_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u12_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u13_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u14_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u15_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h a239 hv
  have u16_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23847 h hv u1_2 u14_47 u15_49
  have u17_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11075 h hv u2_37 u14_47 u15_49
  have u18_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7621 h hv u14_47 u13_88 u11_99
  have u19_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u15_49 hv
  have u20_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u8_103 u17_187 u16_278
  have u21_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u19_210 hv
  have u22_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u19_210 hv
  have u23_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14277 h u19_210 hv u8_103
  have u24_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u20_243 u17_187 u16_278 hv u5_317 u4_319 u3_321
  have u25_95 : T {3, 6, 7} := by
    by_contra hv
    exact c19002 h u20_243 u23_31 hv u7_118
  have u26_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c26645 h u24_298 u6_1 hv u21_43
  have u27_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4689 h hv u22_70 u12_90 u11_99
  have u28_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12691 h hv u15_49 u22_70 u12_90
  have u29_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12975 h hv u14_47 u13_88 u25_95
  have u30_29 : T {0, 5, 8} := by
    by_contra hv
    exact c27438 h a304 hv u26_40
  have u31_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c428 h hv u27_141 u18_162 u17_187 u10_196 u28_198 u29_200
  exact c422 h u30_29 u27_141 u18_162 u31_177 u17_187 u10_196 u28_198 u29_200

private theorem c31523 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → Q {1, 2, 3, 9} → ¬ Q {0, 3, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a29 a210 n183 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u6_24 : T {0, 4, 7} := by
    by_contra hv
    exact c14266 h a210 hv u5_112
  have u7_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31521 h h0 hv a304
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u9_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u8_118
  have u10_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u11_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 a29 hv
  have u12_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c14373 h a210 a29 u9_103 hv
  have u13_23 : T {0, 4, 6} := by
    by_contra hv
    exact c14264 h a210 hv u12_114
  have u14_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1884 h u1_121 u5_112 u12_114 hv
  have u15_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c14289 h a210 u13_23 u6_24 hv
  have u16_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c14283 h a210 hv u13_23 u6_24
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28278 h hv u15_25 u11_40
  have u18_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c31252 h h0 hv u16_22
  have u19_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1480 h a304 n183 u7_239 hv u17_310 u10_313 u18_315
  have u20_68 : T {2, 3, 7} := by
    by_contra hv
    exact c1020 h u19_274 hv
  have u21_3 : T {0, 1, 4} := by
    by_contra hv
    exact c23222 h u19_274 hv u5_112
  have u22_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20717 h hv u13_23 u20_68
  have u23_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25643 h hv u21_3 u13_23 u6_24
  have u24_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28443 h hv u21_3 u13_23 u6_24
  have u25_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u14_116 hv u24_311 u23_291
  exact c1729 h u25_200 u22_256 u23_291 u24_311 u4_321 u3_328 u2_329

theorem c31524 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → ¬ Q {0, 3, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a210 n183 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u3_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv u2_118
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u1_1 u4_109
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u1_1 hv
  have u7_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u8_24 : T {0, 4, 7} := by
    by_contra hv
    exact c14266 h a210 hv u6_112
  have u9_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14277 h a210 hv u3_103
  have u10_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c459 h hv u9_31
  have u11_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c31523 h h0 hv a210 n183 a304
  have u12_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c427 h hv u11_29
  have u13_105 : T {4, 6, 7} := by
    by_contra hv
    exact c14274 h a210 u11_29 hv
  have u14_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 u11_29 hv
  have u15_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u0_121 u13_105 hv
  have u16_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28403 h hv u1_1 u13_105
  have u17_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22487 h hv u8_24 u13_105 u4_109
  have u18_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17587 h hv u8_24 u13_105 u4_109
  have u19_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26645 h hv u1_1 u14_40 u7_43
  have u20_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28187 h hv u1_1 u14_40 u7_43
  have u21_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u12_177 u18_233 u17_268 u19_298 u5_307 u20_309 u16_311
  have u22_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24182 h hv u11_29 u21_93 u15_116
  have u23_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19282 h hv u11_29 u21_93 u15_116
  exact c31281 h h0 u22_280 u23_245 u13_105 u10_189

theorem c31525 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n116 n29 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u4_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u7_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u8_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u10_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27550 h a304 n29 hv u9_112
  have u11_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27427 h a304 hv u10_78
  have u12_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c73 h hv u11_5
  have u13_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u14_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c27483 h a304 u0_1 hv u13_40
  have u15_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u14_39
  have u16_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c27487 h a304 u0_1 u13_40 hv
  have u17_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c626 h hv u16_42
  have u18_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c620 h hv u16_42
  have u19_57 : T {1, 5, 8} := by
    by_contra hv
    exact c27548 h a304 n29 hv u9_112
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u19_57
  have u21_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27468 h a304 u11_5 u20_12 hv
  have u22_27 : T {0, 5, 6} := by
    by_contra hv
    exact c27466 h a304 u11_5 u20_12 hv
  have u23_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u24_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8119 h hv u19_57 u23_88
  have u25_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 n49
  have u26_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u27_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u26_118
  have u28_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv n49 u9_112
  have u29_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u26_118
  have u31_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u32_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20143 h hv u5_9 u31_109
  have u33_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u0_1 u31_109
  have u34_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u35_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1884 h u1_121 u9_112 hv n116
  have u36_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14786 h hv n29 u9_112 n116
  have u37_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21786 h hv n29 u9_112 n116
  have u38_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14086 h hv n29 u9_112 n116
  have u39_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u1_121 u34_105 hv u31_109
  have u40_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u1_121 hv u34_105 u31_109
  have u41_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6435 h hv u19_57 u34_105
  have u42_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c544 h u1_121 u27_205 u15_206 hv u38_208 u18_209 u29_210
  have u43_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c1612 h hv u39_108
  have u44_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c1522 h hv u40_102
  have u45_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u40_102 hv
  have u46_46 : T {1, 3, 6} := by
    by_contra hv
    exact c680 h u42_207 hv
  have u47_67 : T {2, 3, 6} := by
    by_contra hv
    exact c995 h u42_207 hv
  have u48_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c13859 h u42_207 hv u30_103
  have u49_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c13849 h u42_207 hv u35_114
  have u50_24 : T {0, 4, 7} := by
    by_contra hv
    exact c13844 h u42_207 hv n116
  have u51_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1096 h hv u28_157 u36_213 u37_263 u44_277 u25_280 u43_283
  have u52_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7125 h hv u46_46 u35_114
  have u53_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11893 h hv u46_46 u10_78
  have u54_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27020 h hv u48_35 u14_39
  have u55_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28558 h hv u49_26 u14_39
  have u56_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c1630 h a304 u53_193 hv u51_284 u4_320 u3_323 u2_325
  have u57_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u56_249 hv
  have u58_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c19773 h u56_249 hv u22_27 u21_32
  have u59_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c19783 h u56_249 u5_9 hv u47_67
  have u60_93 : T {3, 5, 8} := by
    by_contra hv
    exact c19850 h u56_249 n29 hv u9_112
  have u61_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u50_24 u57_52 u31_109
  have u62_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7783 h hv u57_52 u23_88 u34_105
  have u63_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8633 h hv u57_52 u23_88 u34_105
  have u64_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26147 h hv u50_24 u57_52 u23_88
  have u65_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c268 h hv u58_18
  have u66_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19320 h hv u48_35 u59_66
  have u67_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20858 h hv u49_26 u59_66
  have u68_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2753 h hv u60_93 u30_103 u35_114
  have u69_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c31473 h u24_166 u52_159 u62_163 u68_127 u41_154 u63_169 hv
  have u70_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17908 h hv u69_15 u40_102
  have u71_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1441 h hv u65_180 u70_236 u61_271 u54_301 u33_307 u55_312
  have u72_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c901 h hv u12_144 u17_221 u70_236 u66_246 u32_252 u67_257
  have u73_203 : Q {0, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 hv u64_294 u71_314 u45_119
  exact c1774 h u73_203 u72_259 u64_294 u71_314 u8_324 u7_328 u6_330

end BorsukNine.FiniteObstruction

end OAI
