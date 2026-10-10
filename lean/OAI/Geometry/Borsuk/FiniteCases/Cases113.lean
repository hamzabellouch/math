import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases112

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32583 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 9} → False := by
  classical
  intro a304
  have u0_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u1_118
  have u3_49 : T {1, 3, 9} := by
    by_contra hv
    exact c32582 h h0 hv a304
  have u4_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u3_49 hv
  have u5_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u4_210 hv
  have u6_183 : Q {0, 3, 7, 9} := by
    by_contra hv
    exact c31524 h h0 u4_210 hv a304
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11153 h hv u3_49 u5_70 u0_99
  have u8_19 : T {0, 3, 7} := by
    by_contra hv
    exact c285 h u6_183 hv
  have u9_21 : T {0, 3, 9} := by
    by_contra hv
    exact c313 h u6_183 hv
  have u10_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c32193 h h0 hv u8_19 u9_21
  have u11_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c31993 h h0 u8_19 u9_21 hv
  exact c31421 h h0 u11_243 u2_103 u7_187 u10_278

theorem c32584 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → ¬ Q {0, 5, 8, 9} → False := by
  classical
  intro n31 n95 n105 n200
  have u0_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u1_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25738 h hv n31 n95 n105
  have u2_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20838 h hv n31 n95 n105
  have u3_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u0_116 n200 hv u1_291
  exact c31607 h h0 u1_291 n200 u2_256 u3_311

theorem c32585 (h : TenSystem T Q) :
    ¬ Q {0, 5, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n198 n162 n141 a29 n200 n187 n196
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c428 h hv n141 n162 n187 n196 n198 n200
  exact c31443 h u0_177 n141 a29 n200 n162 n198 n196

theorem c32586 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → False := by
  classical
  intro a198 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u2_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u3_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31897 h h0 a198 hv
  have u4_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c12635 h a198 u2_43 a49 hv
  have u5_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c12691 h a198 a49 u1_70 hv
  exact c12710 h a198 u4_54 u5_90 u3_107

private theorem c32587 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 5, 8} → ¬ Q {3, 4, 6, 7} → ¬ T {4, 6, 7} → T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 5, 6} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → T {1, 2, 7} → ¬ Q {0, 5, 7, 8} → False := by
  classical
  intro n141 n300 n105 a29 n200 n301 n296 n187 n196 a41 n198
  have u0_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u1_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8805 h hv a41 u0_116
  have u2_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27159 h hv a29 a41
  have u3_162 : Q {0, 2, 5, 8} := by
    by_contra hv
    exact c32585 h n198 hv n141 a29 n200 n187 n196
  have u4_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1158 h u3_162 hv
  have u5_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c426 h u3_162 n141 hv n187 n196 n198 n200
  have u6_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16745 h hv a29 u4_78 u0_116
  have u7_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c9647 h u5_177 a41 hv
  have u8_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c1298 h hv u1_171 u6_227 n296 n300 n301 u2_302
  have u9_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c1292 h hv u1_171 u6_227 u8_262 n296 n300 n301 u2_302
  exact c7640 h u3_162 u9_87 n105 u7_107

theorem c32588 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro a29 n200 a41 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32426 h h0 hv a41 u1_43
  have u3_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32375 h h0 a41 hv u1_43
  have u4_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31790 h h0 hv a41 u1_43
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31880 h h0 a41 u1_43 hv
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32586 h h0 hv a49
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c14275 h u0_210 a29 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26877 h hv a29 u1_43
  have u9_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27159 h hv a29 a41
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u7_105 hv
  have u11_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8805 h hv a41 u10_116
  have u12_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c32587 h h0 hv u8_300 u7_105 a29 n200 u2_301 u3_296 u4_187 u5_196 a41 u6_198
  have u13_4 : T {0, 1, 5} := by
    by_contra hv
    exact c58 h u12_141 hv
  have u14_7 : T {0, 1, 8} := by
    by_contra hv
    exact c99 h u12_141 hv
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c843 h u12_141 hv
  have u16_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c32229 h h0 hv u14_7 u13_4
  have u17_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21645 h hv a29 u15_57 u10_116
  have u18_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c1296 h hv u11_171 u17_262 u3_296 u8_300 u2_301 u9_302
  have u19_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c1292 h hv u11_171 u18_227 u17_262 u3_296 u8_300 u2_301 u9_302
  have u20_72 : T {2, 4, 6} := by
    by_contra hv
    exact c4694 h u12_141 hv u19_87 u7_105
  have u21_107 : T {4, 6, 9} := by
    by_contra hv
    exact c4700 h u12_141 u19_87 u7_105 hv
  have u22_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c4611 h u12_141 u20_72 hv
  have u23_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9647 h hv a41 u21_107
  have u24_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c4607 h u12_141 hv u21_107
  have u25_95 : T {3, 6, 7} := by
    by_contra hv
    exact c4682 h u12_141 u24_68 hv u22_99
  have u26_162 : Q {0, 2, 5, 8} := by
    by_contra hv
    exact c424 h u12_141 hv u23_177 u4_187 u5_196 u6_198 n200
  have u27_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c7555 h u26_162 hv u25_95
  have u28_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c806 h hv u27_54
  have u29_191 : Q {0, 4, 6, 9} := by
    by_contra hv
    exact c31459 h h0 u16_282 hv u28_247 u21_107
  exact c31563 h h0 u29_191 u16_282 u28_247 u9_302

private theorem c32589 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 9} → ¬ T {0, 5, 8} → T {1, 2, 7} → Q {1, 2, 3, 9} → False := by
  classical
  intro a107 n29 a41 a210
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c14274 h a210 n29 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32517 h h0 hv u0_105
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u0_105 hv
  have u3_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c427 h hv n29
  have u4_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32486 h h0 hv u4_43 a41
  have u6_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32396 h h0 a41 hv u4_43
  have u7_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 a107 hv
  have u8_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32497 h h0 hv a107
  have u9_23 : T {0, 4, 6} := by
    by_contra hv
    exact c14264 h a210 hv u7_114
  have u10_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14374 h a210 n29 hv u7_114
  have u11_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22479 h hv u9_23 u0_105 a107
  have u12_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17579 h hv u9_23 u0_105 a107
  have u13_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c14267 h a210 hv u10_112
  have u14_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u3_177 u12_233 u11_268 u6_298 u5_307 u8_309 u1_311
  have u15_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv u13_24
  have u16_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24182 h hv n29 u14_93 u2_116
  have u17_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19282 h hv n29 u14_93 u2_116
  exact c31281 h h0 u16_280 u17_245 u0_105 u15_189

theorem c32590 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 5, 8} → ¬ Q {0, 4, 6, 7} → T {4, 6, 7} → ¬ T {0, 5, 8} → False := by
  classical
  intro n93 n189 a105 n29
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u1_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24182 h hv n29 n93 u0_116
  have u2_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19282 h hv n29 n93 u0_116
  exact c31281 h h0 u1_280 u2_245 a105 n189

theorem c32591 (h : TenSystem T Q) :
    ¬ Q {2, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → T {3, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 4, 5, 8} → False := by
  classical
  intro n268 n233 a93 n311 n177 n307 n298
  have u0_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1394 h hv n177 n233 n268 n298 n307 n311
  exact c1382 h a93 n177 n233 n268 n298 n307 u0_309 n311

theorem c32592 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 5, 8} → ¬ T {0, 4, 6} → T {1, 2, 7} → Q {1, 2, 3, 9} → False := by
  classical
  intro a268 n23 a41 a210
  have u0_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u1_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32426 h h0 hv a41 u0_43
  have u2_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32375 h h0 a41 hv u0_43
  have u3_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c31769 h h0 a41 hv u0_43
  have u4_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c31820 h h0 a41 hv u0_43
  have u5_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h a210 hv
  have u6_66 : T {2, 3, 5} := by
    by_contra hv
    exact c988 h a268 hv
  have u7_69 : T {2, 3, 8} := by
    by_contra hv
    exact c1029 h a268 hv
  have u8_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c32025 h h0 hv u6_66 u5_70
  have u9_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c31976 h h0 hv u7_69 u5_70
  have u10_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31307 h h0 u8_246 hv u1_301 u4_190
  have u11_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c31538 h h0 hv u3_185 u2_296 u9_241
  have u12_101 : T {4, 5, 6} := by
    by_contra hv
    exact c14332 h a210 n23 hv u10_106
  exact c31261 h h0 u3_185 u9_241 u12_101 u11_276

theorem c32593 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro n29 a41 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32486 h h0 hv u1_43 a41
  have u3_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32396 h h0 a41 hv u1_43
  have u4_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c427 h hv n29
  have u5_105 : T {4, 6, 7} := by
    by_contra hv
    exact c14274 h u0_210 n29 hv
  have u6_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32517 h h0 hv u5_105
  have u7_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c32589 h h0 hv n29 a41 u0_210
  have u8_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c1597 h hv u7_107
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 u7_107 hv
  have u10_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6709 h hv a49 u9_114
  have u11_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c14265 h u0_210 hv u9_114
  have u12_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c341 h hv u11_23
  have u13_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u12_189 u5_105 n29
  have u14_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c32592 h h0 hv u11_23 a41 u0_210
  have u15_233 : Q {1, 3, 5, 8} := by
    by_contra hv
    exact c32591 h u14_268 hv u13_93 u6_311 u4_177 u2_307 u3_298
  have u16_45 : T {1, 3, 5} := by
    by_contra hv
    exact c673 h u15_233 hv
  have u17_48 : T {1, 3, 8} := by
    by_contra hv
    exact c714 h u15_233 hv
  have u18_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c1386 h u15_233 u4_177 u14_268 u3_298 u2_307 hv u6_311
  have u19_72 : T {2, 4, 6} := by
    by_contra hv
    exact c17576 h u15_233 u11_23 hv u7_107
  have u20_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32215 h h0 u16_45 hv a49
  have u21_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c32225 h h0 hv u16_45 a49
  have u22_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c32176 h h0 hv u17_48 a49
  have u23_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32505 h h0 u18_309 hv u1_43
  have u24_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv u23_38
  have u25_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c1073 h hv u10_156 u24_212 u22_276 u20_280 u21_281 u8_282
  exact c31226 h u21_281 u8_282 u10_156 u19_72 u22_276 u24_212 u25_262

end BorsukNine.FiniteObstruction

end OAI
