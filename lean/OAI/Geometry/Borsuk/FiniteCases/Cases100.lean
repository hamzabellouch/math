import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases097
import OAI.Geometry.Borsuk.FiniteCases.Cases099

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31512 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n258 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u3_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31506 h h0 hv n258 a313 a304
  have u4_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv u3_71
  have u5_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u4_7 hv
  have u6_63 : T {1, 7, 9} := by
    by_contra hv
    exact c31511 h h0 hv u3_71 a313 a304
  have u7_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31508 h h0 u6_63 hv n258 a313 a304
  have u8_78 : T {2, 5, 8} := by
    by_contra hv
    exact c18452 h u7_239 hv u1_103 u2_112
  exact c18397 h u7_239 u3_71 u5_76 u8_78

theorem c31513 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u1_37 u3_109
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u6_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u7_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u9_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1425 h a313 hv
  have u10_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h a313 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u13_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7625 h hv u8_88 u9_95 u6_99
  have u14_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4685 h hv u8_88 u9_95 u6_99
  have u15_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11043 h hv u1_37 u11_118
  have u16_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u2_121 u3_109 hv u11_118
  have u17_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u16_115
  have u18_258 : Q {1, 6, 7, 9} := by
    by_contra hv
    exact c31512 h h0 hv a313 a304
  have u19_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h u18_258 hv
  have u20_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31505 h h0 u18_258 a313 a304 u17_255 hv u11_118
  have u21_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u19_63 u3_109 u11_118
  have u22_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u20_239 hv
  have u23_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h u20_239 hv
  have u24_29 : T {0, 5, 8} := by
    by_contra hv
    exact c18450 h u20_239 hv u12_103 u5_112
  have u25_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12975 h hv u22_47 u8_88 u9_95
  have u26_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12695 h hv u23_49 u7_90 u10_97
  exact c422 h u24_29 u14_141 u13_162 u21_177 u15_187 u4_196 u26_198 u25_200

private theorem c31514 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → ¬ T {7, 8, 9} → Q {1, 6, 7, 9} → T {3, 7, 9} → False := by
  classical
  intro a239 n120 a258 a99
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u4_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u6_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h a239 hv
  have u7_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23565 h hv u1_2 u5_47 u6_49
  have u8_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u6_49 hv
  have u9_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10793 h hv u2_37 u5_47 u6_49
  have u10_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u8_210 hv
  have u11_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u9_185 hv n120
  have u12_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u9_185 hv u4_101 u7_276
  have u13_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c20995 h a258 hv u11_71
  have u14_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c18667 h u12_241 u3_9 hv u10_70
  have u15_84 : T {2, 7, 9} := by
    by_contra hv
    exact c18612 h u12_241 u13_20 hv
  have u16_35 : T {0, 7, 9} := by
    by_contra hv
    exact c18618 h u12_241 hv u14_69
  exact c18727 h u12_241 u16_35 u15_84 a99

private theorem c31516 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → Q {1, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a274 a258 a304
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1760 h a258 hv
  have u3_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u1_1 u2_118
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u6_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22521 h hv u5_63 u4_109 u2_118
  have u7_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u5_63 u4_109 u2_118
  have u8_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c20983 h a258 u0_9 hv
  have u9_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u1_1 u4_109
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u1_1 hv
  have u11_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1252 h a274 hv
  have u12_3 : T {0, 1, 4} := by
    by_contra hv
    exact c23222 h a274 hv u10_112
  have u13_5 : T {0, 1, 6} := by
    by_contra hv
    exact c23226 h a274 hv u8_103
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17621 h hv u11_84 u4_109 u2_118
  have u15_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28423 h hv u1_1 u12_3 u13_5
  have u16_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c27427 h a304 u13_5 hv
  have u17_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28143 h hv u1_1 u12_3 u13_5
  have u18_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u7_177 u14_233 u6_268 u3_298 u9_307 u17_309 u15_311
  exact c21120 h a258 u16_78 u18_93 u8_103

theorem c31517 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a258 a304
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u2_1 u4_109
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u2_1 hv
  have u7_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u8_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u9_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1760 h a258 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c20983 h a258 u0_9 hv
  have u11_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u8_63 u4_109 u9_118
  have u12_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22521 h hv u8_63 u4_109 u9_118
  have u13_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u2_1 u9_118
  have u14_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u4_109 u9_118 hv
  have u15_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u4_109 hv u9_118
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u14_120
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1719 h hv u15_115
  have u18_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31514 h h0 hv u14_120 a258 u7_99
  have u19_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c31516 h h0 hv a258 a304
  have u20_183 : Q {0, 3, 7, 9} := by
    by_contra hv
    exact c31288 h u17_310 hv u16_315 u19_274 u3_313 u7_99 u18_239
  have u21_35 : T {0, 7, 9} := by
    by_contra hv
    exact c517 h u20_183 hv
  have u22_38 : T {1, 2, 4} := by
    by_contra hv
    exact c10482 h u20_183 hv u6_112
  have u23_40 : T {1, 2, 6} := by
    by_contra hv
    exact c10486 h u20_183 hv u10_103
  have u24_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17619 h hv u21_35 u4_109 u9_118
  have u25_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28463 h hv u2_1 u22_38 u23_40
  have u26_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c27439 h a304 hv u23_40
  have u27_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28183 h hv u2_1 u22_38 u23_40
  have u28_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u11_177 u24_233 u12_268 u13_298 u5_307 u27_309 u25_311
  exact c21118 h a258 u26_29 u28_93 u10_103

theorem c31518 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 7, 9} → T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a183 a118 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u4_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u5_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u6_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u7_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u6_258 u5_313 a118 hv
  have u8_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u7_202 u6_258 hv u5_313 u2_323 u3_327 u4_330
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u1_121 hv a118
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u11_38 : T {1, 2, 4} := by
    by_contra hv
    exact c10482 h a183 hv u10_112
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c10486 h a183 hv u9_103
  have u13_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c13145 h u7_202 u11_38 hv
  have u14_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c27439 h a304 hv u12_40
  exact c26018 h u8_293 u14_29 u13_93 u9_103

theorem c31519 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a274 a118 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u4_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u5_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u6_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u7_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u6_258 u5_313 a118 hv
  have u8_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u7_202 u6_258 hv u5_313 u2_323 u3_327 u4_330
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u1_121 hv a118
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u11_3 : T {0, 1, 4} := by
    by_contra hv
    exact c23222 h a274 hv u10_112
  have u12_5 : T {0, 1, 6} := by
    by_contra hv
    exact c23226 h a274 hv u9_103
  have u13_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c25885 h u8_293 u11_3 hv
  have u14_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c27427 h a304 u12_5 hv
  exact c13280 h u7_202 u14_78 u13_93 u9_103

end BorsukNine.FiniteObstruction

end OAI
