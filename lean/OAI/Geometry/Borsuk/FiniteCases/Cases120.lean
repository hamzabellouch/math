import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases119

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32639 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 3, 9} → False := by
  classical
  intro a133
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c723 h a133 u0_49

theorem c32640 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → False := by
  classical
  intro a210
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c725 h a210 u0_49

theorem c32641 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 4, 9} → False := by
  classical
  intro a230
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c727 h a230 u0_49

theorem c32642 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → False := by
  classical
  intro a234
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c729 h a234 u0_49

theorem c32643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 9} → False := by
  classical
  intro a237
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c731 h a237 u0_49

theorem c32644 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → False := by
  classical
  intro a239
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c733 h a239 u0_49

theorem c32645 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 8, 9} → False := by
  classical
  intro a240
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c735 h a240 u0_49

theorem c32646 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro a177 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u3_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u4_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h a177 hv
  have u5_20 : T {0, 3, 8} := by
    by_contra hv
    exact c294 h a177 hv
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c427 h a177 hv
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1383 h a177 hv
  have u8_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 a177 hv
  have u9_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32211 h h0 hv u5_20 u4_17
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c32011 h h0 u5_20 u4_17 hv
  have u11_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c9645 h a177 u8_40 hv
  have u12_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 u9_280 u10_245 hv u2_189
  have u13_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c31558 h h0 hv u10_245 u2_189 u9_280
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u11_109 hv
  have u15_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u11_109 u12_105
  have u16_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u12_105 hv
  have u17_43 : T {1, 2, 9} := by
    by_contra hv
    exact c9648 h a177 hv u12_105
  have u18_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16349 h hv u6_29 u7_93 u14_112
  have u19_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u6_29 u14_112 u16_116
  have u20_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u6_29 u14_112 u16_116
  have u21_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c15071 h hv u6_29 u7_93 u14_112
  have u22_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15945 h hv u4_17 u15_108
  have u23_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u17_43 u8_40
  have u24_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u17_43 u8_40
  have u25_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u3_172 u20_228 u19_263 u24_297 u13_300 u23_303 u0_304
  have u26_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16472 h hv n24 u25_88 u12_105
  have u27_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15622 h hv n24 u25_88 u12_105
  exact c31390 h u22_222 u17_43 u26_225 u18_224 u21_215 u1_210 u27_219

private theorem c32647 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 5, 8} → T {0, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a112 n297 n303 n198 n187 a29 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u6_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u7_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u8_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u9_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14087 h hv a29 a112 u4_116
  have u10_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13641 h hv a29 a112 u4_116
  have u11_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv a29 a112 u4_116
  have u12_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv a29 a112 u4_116
  have u13_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u8_109 n105
  have u14_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u8_109
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u8_109
  have u16_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c31535 h h0 u14_206 u15_209 u1_210 hv u9_208 u10_205
  have u17_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u7_172 u12_228 u11_263 n297 u5_300 n303 u2_304
  have u18_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c13855 h u16_207 hv u13_108
  have u19_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4708 h hv u17_88 n105 u8_109
  have u20_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c450 h hv u18_30
  have u21_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c432 h hv u19_141 u3_162 u6_177 n187 n198 u20_200
  exact c422 h a29 u19_141 u3_162 u6_177 n187 u21_196 n198 u20_200

theorem c32648 (h : TenSystem T Q) :
    ¬ Q {0, 1, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → T {0, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n141 n187 n196 n198 a29 n177 n162
  have u0_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c422 h a29 n141 n162 n177 n187 n196 n198 hv
  exact c436 h u0_200 n141 n162 n177 n187 n196 n198

private theorem c32649 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a43 a40 a29 a93 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u3_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u4_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u5_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31789 h h0 hv a40 a43
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31900 h h0 hv a40 a43
  have u7_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv a43 a40
  have u8_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv a43 a40
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32647 h h0 hv u8_297 u7_303 u6_198 u5_187 a29 n105 n24
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u9_112
  have u11_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u9_112
  have u12_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u4_193 u11_109 hv u1_304
  have u13_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u12_249 hv u4_193 u1_304
  have u14_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24747 h u13_284 a29 hv a93
  have u15_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c843 h hv u14_57
  exact c32648 h u15_141 u5_187 u10_196 u6_198 a29 u3_177 u2_162

private theorem c32650 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 8} → ¬ Q {1, 2, 6, 9} → T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ Q {0, 4, 7, 9} → False := by
  classical
  intro n112 n222 a40 a29 a93 n105 n193
  have u0_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u1_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u5_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15781 h hv a29 a93 u4_116
  have u6_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14645 h hv a29 a93 u4_116
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u8_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13853 h hv a29 u7_109
  have u9_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2233 h hv a93 u7_109
  have u10_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 n193 u7_109 hv u2_304
  have u11_221 : Q {1, 2, 6, 8} := by
    by_contra hv
    exact c31365 h n222 u5_220 u8_207 u9_124 hv u6_212 a40
  have u12_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u10_249 hv
  have u13_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u10_249 hv n193 u2_304
  have u14_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u10_249 a29 hv
  have u15_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c19847 h u10_249 a29 hv a93
  have u16_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c19727 h u10_249 hv a93
  have u17_81 : T {2, 6, 8} := by
    by_contra hv
    exact c19800 h u10_249 u16_12 u14_67 hv
  have u18_42 : T {1, 2, 8} := by
    by_contra hv
    exact c626 h u11_221 hv
  have u19_216 : Q {1, 2, 5, 6} := by
    by_contra hv
    exact c599 h u11_221 u9_124 u8_207 u6_212 hv u5_220 n222
  have u20_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24747 h u13_284 a29 hv a93
  have u21_76 : T {2, 5, 6} := by
    by_contra hv
    exact c19798 h u10_249 u16_12 u14_67 hv
  have u22_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9793 h hv u12_52 u17_81
  have u23_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32516 h h0 hv u18_42 a40
  have u24_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32405 h h0 hv a40 u18_42
  have u25_39 : T {1, 2, 5} := by
    by_contra hv
    exact c579 h u19_216 hv
  have u26_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6434 h hv u20_57 n105
  have u27_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9330 h hv u20_57 u15_78 n112
  have u28_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10608 h hv u20_57 u15_78 n112
  have u29_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10635 h hv u12_52 u21_76
  have u30_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32464 h h0 u25_39 hv a40
  have u31_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c32566 h h0 u25_39 hv a40
  have u32_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32435 h h0 u25_39 u18_42 hv
  have u33_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c32546 h h0 u25_39 u18_42 hv
  have u34_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c31485 h u22_178 hv u28_183 u29_184 u0_133 u26_154 u27_174
  have u35_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c1343 h hv u27_174 u1_230 u24_299 u32_302 u2_304 u30_305
  have u36_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c1337 h hv u27_174 u1_230 u35_265 u24_299 u32_302 u2_304 u30_305
  have u37_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c1478 h hv u28_183 u3_239 u2_304 u23_310 u33_313 u31_315
  have u38_99 : T {3, 7, 9} := by
    by_contra hv
    exact c15888 h u11_221 u34_21 u36_90 hv
  exact c31288 h u23_310 u28_183 u31_315 u37_274 u33_313 u38_99 u3_239

theorem c32651 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a40 a29 a93 n105 n24
  have u0_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u1_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32649 h h0 hv a40 a29 a93 n105 n24
  have u4_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c641 h hv u3_43
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27856 h hv n24 u3_43
  have u6_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32650 h h0 hv u4_222 a40 a29 a93 n105 u2_193
  have u7_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u6_112
  have u8_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 u6_112 hv u0_116
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u6_112 hv u0_116
  have u10_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv n24 n105 u7_109
  have u11_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv n24 n105 u7_109
  have u12_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u8_103
  have u13_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv u9_114
  have u14_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32591 h u11_268 u10_233 a93 hv u1_177 u5_307 u12_298
  exact c1396 h u14_311 u1_177 u10_233 u11_268 u12_298 u5_307 u13_309

end BorsukNine.FiniteObstruction

end OAI
