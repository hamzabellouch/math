import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases115

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32606 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a311 n177 a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u2_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u1_41
  have u3_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u4_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u3_210 hv
  have u5_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h a311 hv
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32517 h h0 a311 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv u6_116
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u3_210 hv u7_105
  have u10_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c32604 h h0 hv a311 n177 a49
  have u11_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32605 h h0 hv u10_127 a311 a49
  have u12_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u4_43 u11_40
  have u13_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u4_43 u11_40
  have u14_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c28419 h a311 hv u11_40
  have u15_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv u11_40 u6_116
  have u16_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32524 h h0 a311 hv u11_40
  have u17_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u3_210 u14_24 hv
  have u18_108 : T {4, 7, 8} := by
    by_contra hv
    exact c14342 h u3_210 u14_24 u7_105 hv
  have u19_102 : T {4, 5, 7} := by
    by_contra hv
    exact c14338 h u3_210 u14_24 hv u7_105
  have u20_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c558 h hv u16_38
  have u21_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u9_29 u17_112 u6_116
  have u22_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u9_29 u17_112 u6_116
  have u23_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u18_108 hv
  have u24_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2235 h hv u5_94 u18_108
  have u25_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u19_102 hv
  have u26_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u15_172 u22_228 u21_263 u13_297 u8_300 u12_303 u0_304
  have u27_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2506 h hv u26_88 u23_113
  have u28_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2084 h hv u26_88 u25_119
  exact c31532 h h0 u20_122 u2_125 u24_124 u10_127 u28_123 u27_126

private theorem c32607 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → T {1, 2, 6} → ¬ Q {3, 5, 8, 9} → Q {1, 2, 3, 9} → False := by
  classical
  intro n24 n105 a40 n311 a210
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u2_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv a40 u1_116
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h a210 hv n105
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u5_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u6_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u5_43 a40
  have u7_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u5_43 a40
  have u8_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h a210 n24 hv
  have u9_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u3_29 u8_112 u1_116
  have u10_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u3_29 u8_112 u1_116
  have u11_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u2_172 u10_228 u9_263 u6_297 u4_300 u7_303 u0_304
  have u12_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20830 h hv n24 u11_88 n105
  have u13_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25730 h hv n24 u11_88 n105
  have u14_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u1_116 hv n311 u13_291
  exact c31604 h h0 u14_200 u13_291 u12_256 n311

private theorem c32608 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 4, 6, 9} → T {1, 4, 7} → ¬ Q {0, 4, 6, 7} → Q {1, 2, 3, 9} → False := by
  classical
  intro a291 n202 n191 a52 n189 a210
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h a210 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u2_79 : T {2, 5, 9} := by
    by_contra hv
    exact c1185 h a291 hv
  have u3_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1271 h a291 hv
  have u4_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c25613 h a291 hv a52
  have u5_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13089 h hv u1_43 u0_70 u2_79
  have u6_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11547 h hv u1_43 u0_70 u2_79
  have u7_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3817 h hv u0_70 u2_79 u3_85
  have u8_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8889 h hv u1_43 u2_79 u3_85
  have u9_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10849 h hv u1_43 u0_70 u3_85
  have u10_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12249 h hv u1_43 u0_70 u3_85
  have u11_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10011 h hv u1_43 u2_79 u3_85
  have u12_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4939 h hv u0_70 u2_79 u3_85
  have u13_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c336 h hv u7_135 u8_171 u9_185 n189 u6_190 n191
  have u14_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c456 h hv u12_143 u11_179 n189 u10_195 u5_201 n202
  have u15_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c31487 h u8_171 u9_185 n189 u7_135 u13_156 hv n191
  have u16_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c452 h hv u12_143 u14_164 u11_179 n189 u10_195 u5_201 n202
  exact c25652 h a291 u4_18 u15_23 u16_31

private theorem c32609 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → T {1, 2, 6} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a200 n88 n105 a40 n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32607 h h0 hv n105 a40 u1_311 u0_210
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h u0_210 u2_24 hv
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u3_112
  have u5_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u6_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u2_24 u5_43
  have u7_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c1563 h hv n105
  have u8_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32395 h h0 hv u5_43 a40
  have u9_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u10_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31918 h h0 a200 a40 hv
  have u11_52 : T {1, 4, 7} := by
    by_contra hv
    exact c12990 h a200 hv n88 n105
  have u12_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12992 h a200 hv n88 n105
  have u13_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22485 h hv u2_24 u11_52 u4_109
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17585 h hv u2_24 u12_73 u4_109
  have u15_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32591 h u13_268 u14_233 hv u1_311 n177 u6_307 u8_298
  have u16_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11606 h hv u9_41 u15_93
  have u17_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13144 h hv u10_38 u15_93
  have u18_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32608 h hv u17_202 u16_191 u11_52 u7_189 u0_210
  have u19_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31604 h h0 a200 u18_291 hv u1_311
  have u20_58 : T {1, 5, 9} := by
    by_contra hv
    exact c870 h u19_256 hv
  have u21_64 : T {1, 8, 9} := by
    by_contra hv
    exact c956 h u19_256 hv
  have u22_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c20713 h u19_256 hv u12_73
  have u23_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7879 h hv a49 u20_58 u21_64
  have u24_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6757 h hv a49 u20_58 u21_64
  have u25_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9979 h hv u5_43 u20_58 u21_64
  have u26_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13057 h hv u5_43 a49 u20_58
  have u27_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11515 h hv u5_43 a49 u20_58
  have u28_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12217 h hv u5_43 a49 u21_64
  have u29_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8857 h hv u5_43 u20_58 u21_64
  have u30_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10817 h hv u5_43 a49 u21_64
  have u31_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c334 h hv u24_156 u29_171 u30_185 u7_189 u27_190 u16_191
  have u32_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c31487 h u29_171 u30_185 u7_189 u31_135 u24_156 hv u16_191
  have u33_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c454 h hv u23_164 u25_179 u7_189 u28_195 u26_201 u17_202
  have u34_31 : T {0, 6, 7} := by
    by_contra hv
    exact c20752 h u19_256 u22_18 u32_23 hv
  exact c452 h u34_31 u33_143 u23_164 u25_179 u7_189 u28_195 u26_201 u17_202

private theorem c32610 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 8, 9} → ¬ T {4, 6, 7} → T {1, 2, 6} → ¬ Q {3, 5, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n200 n105 a40 n311 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32607 h h0 hv n105 a40 n311 u0_210
  have u2_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u3_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv a40 u2_116
  have u4_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c1563 h hv n105
  have u5_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u6_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31840 h h0 hv u5_43 a40
  have u7_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31779 h h0 hv u5_43 a40
  have u8_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u9_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u2_116 n200 n311 hv
  have u10_79 : T {2, 5, 9} := by
    by_contra hv
    exact c1185 h u9_291 hv
  have u11_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1271 h u9_291 hv
  have u12_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31606 h h0 u9_291 hv n200 n311
  have u13_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3957 h hv u8_70 u10_79 u11_85
  have u14_58 : T {1, 5, 9} := by
    by_contra hv
    exact c870 h u12_256 hv
  have u15_64 : T {1, 8, 9} := by
    by_contra hv
    exact c956 h u12_256 hv
  have u16_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6897 h hv a49 u14_58 u15_64
  have u17_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c361 h hv u13_136 u16_157 u3_172 u7_186 u4_189 u6_192
  exact c347 h u1_24 u13_136 u16_157 u3_172 u7_186 u4_189 u6_192 u17_193

theorem c32611 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → T {1, 2, 6} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n105 a40 n177 a49
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u1_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32610 h h0 hv n105 a40 u0_311 a49
  have u2_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c12867 h u1_200 a40 hv
  exact c32609 h h0 u1_200 u2_88 n105 a40 n177 a49

private theorem c32612 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 7} → T {3, 5, 8} → T {4, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a24 a93 a105 n309 n298 n311 n177 a210
  have u0_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u1_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h a210 a24 hv
  have u2_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv a24 u0_43
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u1_112
  have u4_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22487 h hv a24 a105 u3_109
  have u5_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17587 h hv a24 a105 u3_109
  exact c1382 h a93 n177 u5_233 u4_268 n298 u2_307 n309 n311

theorem c32615 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 7} → T {4, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a24 a105 n309 n298 n311 n177 a210
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h a210 hv a105
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h a210 a24 hv
  have u3_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32612 h h0 a24 hv a105 n309 n298 n311 n177 a210
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u2_112
  have u5_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24750 h hv u1_29 u3_93 u2_112
  have u6_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19850 h hv u1_29 u3_93 u2_112
  have u7_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31573 h h0 hv u5_284 u6_249 u0_304
  exact c31572 h h0 u6_249 u7_193 u4_109 u0_304 u5_284

end BorsukNine.FiniteObstruction

end OAI
