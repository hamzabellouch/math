import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases114

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32600 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro n311 a41 a49
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32593 h h0 hv a41 a49
  have u1_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32588 h h0 u0_29 hv a41 a49
  have u2_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31920 h h0 u1_200 hv a41
  have u3_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u2_40
  have u4_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12866 h u1_200 u2_40 hv
  have u5_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31919 h h0 u1_200 a41 hv
  have u6_95 : T {3, 6, 7} := by
    by_contra hv
    exact c12864 h u1_200 u5_38 hv
  have u7_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u8_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u7_210 hv
  have u9_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32375 h h0 a41 hv u8_43
  have u10_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c31769 h h0 a41 hv u8_43
  have u11_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32597 h h0 n311 u3_177 hv a41 a49
  have u12_101 : T {4, 5, 6} := by
    by_contra hv
    exact c32595 h h0 hv n311 u3_177 a41 a49
  have u13_98 : ¬ T {3, 7, 8} := by
    intro hv
    exact c2691 h u11_127 u4_88 u6_95 hv
  have u14_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31628 h h0 u12_101 hv
  have u15_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c14281 h u7_210 hv u12_101
  have u16_276 : Q {2, 4, 5, 6} := by
    by_contra hv
    exact c32596 h h0 hv u12_101 u9_296 u10_185
  exact c23622 h u16_276 u15_34 u13_98 u14_120

theorem c32601 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro a41 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32396 h h0 a41 hv u1_43
  have u3_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32486 h h0 hv u1_43 a41
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32593 h h0 hv a41 a49
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c14275 h u0_210 u4_29 hv
  have u6_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32588 h h0 u4_29 hv a41 a49
  have u7_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c12869 h u6_200 a41 hv
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31919 h h0 u6_200 a41 hv
  have u9_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31920 h h0 u6_200 hv a41
  have u10_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12982 h u6_200 hv u7_87 u5_105
  have u11_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12984 h u6_200 hv u7_87 u5_105
  have u12_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c12877 h u6_200 u10_51 hv
  have u13_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c1010 h hv u12_68
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c32594 h h0 hv a41 a49
  have u15_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u9_40
  have u16_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32600 h h0 hv a41 a49
  have u17_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28417 h u16_311 hv a41
  have u18_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32598 h h0 u16_311 hv u13_208 u9_40 u8_38 u7_87 u5_105 a41 u0_210
  have u19_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c32592 h h0 hv u17_23 a41 u0_210
  have u20_8 : T {0, 1, 9} := by
    by_contra hv
    exact c108 h u18_127 hv
  have u21_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c1396 h u16_311 u15_177 u14_233 u19_268 u2_298 u3_307 hv
  exact c28129 h u21_309 u20_8 u11_72

private theorem c32602 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → Q {0, 1, 2, 9} → ¬ Q {3, 5, 7, 8} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 7, 8} → Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → T {1, 2, 9} → False := by
  classical
  intro a200 a127 n309 n157 n136 n186 n192 a311 n177 a43
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_15 : T {0, 2, 9} := by
    by_contra hv
    exact c213 h a127 hv
  have u2_8 : T {0, 1, 9} := by
    by_contra hv
    exact c108 h a127 hv
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h a311 hv
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv u3_116
  have u5_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u6_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11329 h hv a43 u5_93
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32517 h h0 a311 hv
  have u8_30 : T {0, 5, 9} := by
    by_contra hv
    exact c450 h a200 hv
  have u9_36 : T {0, 8, 9} := by
    by_contra hv
    exact c536 h a200 hv
  have u10_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27335 h hv u2_8 u1_15 u8_30
  have u11_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21737 h hv u2_8 u8_30 u9_36
  have u12_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16837 h hv u1_15 u8_30 u9_36
  have u13_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26497 h hv u2_8 u1_15 u9_36
  have u14_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c1309 h hv u12_228 u11_263 u13_297 u4_300 u10_303 u0_304
  have u15_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u14_172 u12_228 u11_263 u13_297 u4_300 u10_303 u0_304
  have u16_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c361 h hv n136 n157 u14_172 n186 u6_189 n192
  have u17_112 : T {5, 6, 8} := by
    by_contra hv
    exact c2646 h a127 u15_88 hv
  have u18_40 : T {1, 2, 6} := by
    by_contra hv
    exact c12866 h a200 hv u15_88
  have u19_52 : T {1, 4, 7} := by
    by_contra hv
    exact c12990 h a200 hv u15_88 u7_105
  have u20_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c347 h hv n136 n157 u14_172 n186 u6_189 n192 u16_193
  have u21_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u17_112
  have u22_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32395 h h0 hv a43 u18_40
  have u23_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27855 h hv u1_15 u19_52
  have u24_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv u20_24 u7_105 u21_109
  have u25_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv u20_24 u7_105 u21_109
  exact c1396 h a311 n177 u25_233 u24_268 u22_298 u23_307 n309

private theorem c32603 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 6} → T {0, 1, 9} → ¬ Q {3, 5, 7, 8} → Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a40 a8 n309 a311 n177 a210
  have u0_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32517 h h0 a311 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u2_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32395 h h0 hv u1_43 a40
  have u3_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c28419 h a311 hv a40
  have u4_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h a210 u3_24 hv
  have u5_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28530 h a311 u3_24 hv u0_105
  have u6_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u4_112
  have u7_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27849 h hv a8 u5_73
  have u8_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv u3_24 u0_105 u6_109
  have u9_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv u3_24 u0_105 u6_109
  exact c1396 h a311 n177 u8_233 u9_268 u2_298 u7_307 n309

theorem c32604 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 2, 9} → Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a127 a311 n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u3_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28416 h a311 hv u2_41
  have u4_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28137 h hv u3_23 u1_43
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32517 h h0 a311 hv
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u0_210 hv u5_105
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h a311 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv u7_116
  have u9_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u10_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1496 h a311 hv
  have u11_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6929 h hv a49 u9_94 u10_100
  have u12_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u13_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3989 h hv u12_70 u9_94 u10_100
  have u14_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c11013 h hv a49 u12_70 u10_100
  have u15_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11851 h hv a49 u12_70 u9_94
  have u16_8 : T {0, 1, 9} := by
    by_contra hv
    exact c108 h a127 hv
  have u17_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32602 h h0 hv a127 u4_309 u11_157 u13_136 u14_186 u15_192 a311 n177 u1_43
  have u18_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32603 h h0 hv u16_8 u4_309 a311 n177 u0_210
  have u19_24 : T {0, 4, 7} := by
    by_contra hv
    exact c28418 h a311 hv u18_40
  have u20_38 : T {1, 2, 4} := by
    by_contra hv
    exact c28468 h a311 hv u18_40 u2_41
  have u21_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c14289 h u0_210 u3_23 u19_24 hv
  have u22_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c14283 h u0_210 hv u3_23 u19_24
  have u23_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28445 h a311 hv u3_23 u19_24
  have u24_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28443 h a311 hv u3_23 u19_24
  have u25_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28701 h hv u6_29 u20_38
  have u26_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9923 h hv u20_38 u7_116
  have u27_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c28421 h a311 hv u20_38
  have u28_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c32475 h h0 hv u20_38 u1_43
  have u29_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c32535 h h0 hv u20_38 u1_43
  have u30_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22690 h hv u24_3 u22_22 u21_25
  have u31_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17790 h hv u23_10 u22_22 u21_25
  have u32_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u26_179 u31_235 u30_270 u8_300 u28_306 u29_312 u25_313
  exact c32584 h h0 u27_31 u32_95 u5_105 u17_200

theorem c32605 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 6} → ¬ Q {0, 1, 2, 9} → Q {3, 5, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n40 n127 a311 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32517 h h0 a311 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u0_210 hv u1_105
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h a311 hv
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv u3_116
  have u5_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u6_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28416 h a311 hv u5_41
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u8_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u5_41
  have u9_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u10_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c588 h hv n40
  have u11_24 : T {0, 4, 7} := by
    by_contra hv
    exact c28418 h a311 hv n40
  have u12_38 : T {1, 2, 4} := by
    by_contra hv
    exact c28468 h a311 hv n40 u5_41
  have u13_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c14289 h u0_210 u6_23 u11_24 hv
  have u14_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c14283 h u0_210 hv u6_23 u11_24
  have u15_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28445 h a311 hv u6_23 u11_24
  have u16_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28443 h a311 hv u6_23 u11_24
  have u17_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28701 h hv u2_29 u12_38
  have u18_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9923 h hv u12_38 u3_116
  have u19_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13145 h hv u12_38 u7_93
  have u20_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c32475 h h0 hv u12_38 u9_43
  have u21_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c32535 h h0 hv u12_38 u9_43
  have u22_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22690 h hv u16_3 u14_22 u13_25
  have u23_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c138 h hv u15_10
  have u24_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17790 h hv u15_10 u14_22 u13_25
  have u25_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21022 h hv u15_10 u14_22 u13_25
  have u26_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u18_179 u24_235 u22_270 u4_300 u20_306 u21_312 u17_313
  have u27_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31500 h h0 u25_258 u17_313 hv u19_202
  have u28_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2620 h hv u26_95 u1_105 u27_118
  have u29_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2176 h hv u26_95 u1_105 u27_118
  exact c31532 h h0 u23_122 u8_125 u10_124 n127 u29_123 u28_126

end BorsukNine.FiniteObstruction

end OAI
