import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases118

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n252 n307 n196 a112
  have u0_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c31588 h h0 hv n196 n252 n307
  exact c31585 h h0 n196 u0_287 n252 n307 a112

private theorem c32632 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 3, 4} → T {2, 4, 7} → Q {2, 5, 6, 8} → Q {1, 5, 6, 8} → ¬ T {0, 6, 9} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 7, 9} → ¬ Q {0, 2, 4, 7} → ¬ Q {2, 4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro n16 a73 a287 a252 n33 n263 n284 n157 n280 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u2_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 a252 hv u1_70
  have u3_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u4_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c607 h hv u3_41
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c20234 h a252 n16 u2_65 hv
  have u6_90 : T {3, 4, 9} := by
    by_contra hv
    exact c20236 h a252 n16 u2_65 hv
  have u7_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c20251 h a252 hv u1_70 u6_90
  have u8_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c25049 h a287 hv u5_88
  have u9_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24536 h hv u8_8 u7_21 n33
  have u10_277 : Q {2, 4, 5, 7} := by
    by_contra hv
    exact c1082 h a73 n157 u4_213 n263 hv n280 u9_283 n284
  exact c23694 h u10_277 u8_8 u7_21 n33

private theorem c32633 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n127 n177 a49
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u1_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u2_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32621 h h0 hv n127 n177 a49
  have u4_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32626 h h0 hv n127 n177 a49
  have u5_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1567 h hv u4_105
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u4_105 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u2_210 hv u4_105
  have u8_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c32630 h h0 hv n127 n177 a49
  have u9_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c350 h hv u8_24
  have u10_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv u8_24
  have u11_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u2_210 u8_24 hv
  have u12_108 : T {4, 7, 8} := by
    by_contra hv
    exact c14342 h u2_210 u8_24 u4_105 hv
  have u13_102 : T {4, 5, 7} := by
    by_contra hv
    exact c14338 h u2_210 u8_24 hv u4_105
  have u14_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u11_112
  have u15_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32247 h h0 hv u11_112
  have u16_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 u11_112 hv u6_116
  have u17_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u11_112 hv u6_116
  have u18_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u7_29 u11_112 u6_116
  have u19_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u12_108 hv
  have u20_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c31887 h h0 hv u12_108
  have u21_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c14271 h u2_210 hv u12_108
  have u22_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u13_102 hv
  have u23_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c31947 h h0 hv u13_102
  have u24_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv u8_24 u4_105 u14_109
  have u25_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv u8_24 u4_105 u14_109
  have u26_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u16_103
  have u27_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c31458 h h0 hv u0_311 u17_114 u16_103
  have u28_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10206 h hv u1_41 u16_103
  have u29_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv u17_114
  have u30_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u3_40 u17_114
  have u31_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9086 h hv u1_41 u19_113
  have u32_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c403 h hv u21_27
  have u33_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8664 h hv u1_41 u22_119
  have u34_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv n177 u24_233 u25_268 u26_298 u29_309 u0_311
  have u35_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv n177 u24_233 u25_268 u26_298 u34_307 u29_309 u0_311
  have u36_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11606 h hv u1_41 u35_93
  have u37_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5292 h hv u35_93 u16_103 u17_114
  have u38_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c494 h hv u37_145 u27_166 u28_181 u36_191 u20_197 u23_203
  have u39_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv u37_145 u27_166 u28_181 u36_191 u20_197 u38_202 u23_203
  have u40_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 hv u34_307 u32_196 u11_112
  have u41_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u40_252 hv
  have u42_287 : Q {2, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u40_252 u34_307 u32_196 hv
  have u43_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h u40_252 u8_24 hv u14_109
  have u44_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5801 h hv u41_57 u11_112 u6_116
  have u45_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1166 h u42_287 hv
  have u46_16 : T {0, 3, 4} := by
    by_contra hv
    exact c32632 h h0 hv u43_73 u42_287 u40_252 u39_33 u18_263 u15_284 u9_157 u5_280 a49
  have u47_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2861 h hv u45_78 u11_112 u6_116
  have u48_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u41_57 u45_78 u6_116
  exact c227 h u46_16 u47_128 u44_149 u33_170 u48_171 u10_172 u31_173 u30_174

theorem c32634 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n307 n252 n287 a112
  have u0_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 n252 n307 hv a112
  exact c31586 h h0 u0_196 n287 n252 n307

private theorem c32635 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 7} → Q {0, 1, 2, 9} → Q {1, 2, 3, 9} → False := by
  classical
  intro n24 a127 a210
  have u0_15 : T {0, 2, 9} := by
    by_contra hv
    exact c213 h a127 hv
  have u1_8 : T {0, 1, 9} := by
    by_contra hv
    exact c108 h a127 hv
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h a210 n24 hv
  have u3_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u2_112
  have u4_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c2647 h a127 hv u2_112
  have u5_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25162 h hv n24 u4_88 u3_109
  have u6_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20262 h hv n24 u4_88 u3_109
  have u7_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 hv u6_252 u5_287 u2_112
  have u8_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c32479 h h0 u7_307 hv u1_8
  have u9_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32482 h h0 u7_307 u0_15 hv
  exact c27878 h u7_307 u8_3 u9_10 n24

private theorem c32636 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n105 n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32633 h h0 hv n177 a49
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32635 h h0 hv u2_127 u0_210
  have u4_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u3_24 u1_43
  have u5_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u0_210 hv n105
  have u8_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32611 h h0 n105 hv n177 a49
  have u9_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2654 h u2_127 hv n105
  have u10_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32627 h h0 hv u4_307 n105 u5_311 n177 u0_210
  have u11_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c592 h hv u8_40
  have u12_233 : Q {1, 3, 5, 8} := by
    by_contra hv
    exact c32628 h h0 hv u9_93 u10_298 u4_307 n105 u5_311 n177 u1_43
  exact c32629 h h0 u12_233 u3_24 u7_29 u6_116 u11_212 a49

private theorem c32637 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u2_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32633 h h0 hv n177 a49
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32635 h h0 hv u2_127 u0_210
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32636 h h0 hv n177 a49
  have u5_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c2655 h u2_127 hv u4_105
  have u6_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1389 h hv u5_93
  have u7_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1393 h hv u5_93
  exact c32615 h h0 u3_24 u4_105 u7_309 u6_298 u1_311 n177 u0_210

theorem c32638 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 9} → False := by
  classical
  intro a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u2_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u1_210 hv
  have u3_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u4_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u3_41
  have u5_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c32637 h h0 hv a49
  have u6_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h u5_177 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c427 h u5_177 hv
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c9649 h u5_177 u2_43 hv
  have u9_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 u5_177 hv
  have u10_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26877 h hv u7_29 u2_43
  have u11_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u8_105 hv
  have u12_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c9645 h u5_177 u9_40 hv
  have u13_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c9665 h u5_177 hv u9_40 u2_43
  have u14_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u2_43 u9_40
  have u15_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u2_43 u9_40
  have u16_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv u9_40 u11_116
  have u17_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u12_109 hv
  have u18_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u12_109 u8_105
  have u19_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u12_109 u8_105
  have u20_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c570 h hv u13_38
  have u21_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c14267 h u1_210 hv u17_112
  have u22_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u7_29 u17_112 u11_116
  have u23_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u7_29 u17_112 u11_116
  have u24_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c14271 h u1_210 hv u18_108
  have u25_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15945 h hv u6_17 u18_108
  have u26_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c14279 h u1_210 hv u19_102
  have u27_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c32635 h h0 u21_24 hv u1_210
  have u28_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u16_172 u23_228 u22_263 u15_297 u10_300 u14_303 u0_304
  have u29_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16376 h hv u24_27 u28_88
  have u30_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15538 h hv u26_32 u28_88
  exact c636 h u1_210 u27_127 u20_215 u30_219 u25_222 u4_224 u29_225

end BorsukNine.FiniteObstruction

end OAI
