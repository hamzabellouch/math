import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases120

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32652 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {1, 2, 3, 6} → T {0, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a112 n207 a29 n105 n24
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u3_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14087 h hv a29 a112 u1_116
  have u4_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13641 h hv a29 a112 u1_116
  have u5_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u2_109
  have u6_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u2_109
  exact c31535 h h0 u5_206 u6_209 u0_210 n207 u3_208 u4_205

private theorem c32653 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a29 a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32651 h h0 hv a29 a93 n105 n24
  have u4_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c590 h hv u3_40
  have u5_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28418 h hv n24 u3_40
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32652 h h0 hv u4_207 a29 n105 n24
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u6_112
  have u8_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u2_193 u7_109 hv u0_304
  have u9_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u8_249 a29 hv
  have u10_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c19847 h u8_249 a29 hv a93
  have u11_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20718 h hv n24 u9_67
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1170 h hv u10_78
  have u13_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u1_116 hv u5_311 u12_291
  exact c31604 h h0 u13_200 u12_291 u11_256 u5_311

private theorem c32654 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n311 a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u2_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u1_29
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u5_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u6_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u3_116 u2_200 n311 hv
  have u7_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1170 h u6_291 hv
  have u8_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31606 h h0 u6_291 hv u2_200 n311
  have u9_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u6_291 n24 hv n105
  have u10_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c25607 h u6_291 hv u9_88
  have u11_46 : T {1, 3, 6} := by
    by_contra hv
    exact c25618 h u6_291 n24 hv
  have u12_52 : T {1, 4, 7} := by
    by_contra hv
    exact c25728 h u6_291 n24 hv n105
  have u13_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10213 h hv u12_52 u7_78
  have u14_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5179 h hv u7_78 u9_88
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h u8_256 hv
  have u16_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c20707 h u8_256 hv u9_88
  have u17_67 : T {2, 3, 6} := by
    by_contra hv
    exact c20718 h u8_256 n24 hv
  have u18_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20828 h u8_256 n24 hv n105
  have u19_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12559 h hv u12_52 u18_73 u9_88
  have u20_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13407 h hv u12_52 u18_73 u9_88
  have u21_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c32324 h h0 u11_46 hv u6_291
  have u22_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8113 h hv u12_52 a93
  have u23_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u15_57 u7_78 a93
  have u24_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u15_57 u7_78 a93
  have u25_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32126 h h0 u17_67 hv u8_256
  have u26_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv u14_145 u22_166 u13_181 u24_191 u19_197 u23_202 u20_203
  have u27_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c656 h hv u21_44
  have u28_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c1012 h hv u25_68
  have u29_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27328 h hv u10_5 u16_12 u26_33
  have u30_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26480 h hv u10_5 u16_12 u26_33
  exact c1307 h u9_88 u5_172 u27_228 u28_263 u30_297 u4_300 u29_303 u0_304

private theorem c32655 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → T {2, 5, 8} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 1, 4, 6} → T {0, 4, 6} → T {0, 6, 7} → ¬ Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro a256 a78 n156 n135 a23 a31 n313 n29 a93 a116 n189
  have u0_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h a256 hv
  have u1_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20721 h a256 a31 hv
  have u2_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u0_57 a78 a93
  have u3_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u0_57 a78 a93
  have u4_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u0_57 a78 a116
  have u5_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21000 h hv n29 u1_65
  have u6_185 : Q {0, 4, 5, 6} := by
    by_contra hv
    exact c31487 h u4_171 hv n189 n135 n156 a23 u3_191
  have u7_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31500 h h0 u5_258 n313 hv u2_202
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31767 h h0 u6_185 hv
  have u9_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c340 h u6_185 n135 n156 u4_171 n189 hv u3_191
  have u10_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31757 h h0 hv u8_120 u7_118
  exact c31817 h h0 u9_190 u10_115

private theorem c32656 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 8} → ¬ Q {2, 4, 6, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 5, 6, 9} → ¬ T {0, 3, 6} → Q {2, 5, 8, 9} → ¬ Q {0, 3, 6, 9} → T {2, 5, 8} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {0, 2, 6, 9} → ¬ T {0, 1, 6} → ¬ Q {0, 1, 6, 9} → T {3, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a57 n282 n293 n203 n197 n18 a291 n181 a78 n302 n313 n166 n5 n145 a93 n162 n287
  have u0_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv a57 a78 a93
  have u1_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv a57 a78 a93
  have u2_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv n145 n166 n181 u1_191 n197 u0_202 n203
  have u3_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31614 h h0 n293 u0_202 n313 hv
  have u4_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c31564 h h0 n302 hv n282 u1_191
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31459 h h0 n282 u1_191 u4_247 hv
  have u6_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23820 h hv n5 n18 u2_33
  have u7_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25368 h hv n5 n18 u2_33
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31500 h h0 u3_258 n313 hv u0_202
  have u9_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15510 h hv u2_33 u5_107 u8_118
  have u10_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22510 h hv u2_33 u5_107 u8_118
  exact c1171 h a291 n162 u9_218 u10_268 u6_278 n287 u7_289

private theorem c32657 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a78 a93 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32654 h h0 hv a93 n105 n24
  have u3_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28528 h u2_311 n24 hv n105
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28413 h u2_311 hv u3_52
  have u5_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c172 h hv u4_12
  have u6_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28530 h u2_311 n24 hv n105
  have u7_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28407 h u2_311 hv u6_73
  have u8_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c67 h hv u7_5
  have u9_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28418 h u2_311 n24 hv
  have u10_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32526 h h0 hv u2_311 u9_40
  have u11_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28416 h u2_311 hv u10_41
  have u12_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u13_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27158 h hv u12_29 u10_41
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32524 h h0 u2_311 hv u9_40
  have u15_31 : T {0, 6, 7} := by
    by_contra hv
    exact c28420 h u2_311 hv u14_38
  have u16_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28700 h hv u12_29 u14_38
  have u17_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8113 h hv u3_52 a93
  have u18_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u6_73 a93
  have u19_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u12_29
  have u20_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u12_29
  have u21_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u22_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u23_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u24_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u25_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u26_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10213 h hv u3_52 a78
  have u27_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32655 h h0 hv a78 u5_156 u8_135 u11_23 u15_31 u16_313 u12_29 a93 u22_116 u25_189
  have u28_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 hv u19_200 u27_256 u2_311
  have u29_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u28_291 n24 hv n105
  have u30_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c25613 h u28_291 hv u3_52
  have u31_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c25621 h u28_291 u15_31 hv
  have u32_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c25617 h u28_291 u11_23 hv
  have u33_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12559 h hv u3_52 u6_73 u29_88
  have u34_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13407 h hv u3_52 u6_73 u29_88
  have u35_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c25900 h hv u12_29 u31_44
  have u36_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24358 h hv u12_29 u32_47
  have u37_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32656 h h0 hv u36_282 u35_293 u34_203 u33_197 u30_18 u28_291 u26_181 a78 u13_302 u16_313 u17_166 u7_5 u18_145 a93 u21_162 u23_287
  have u38_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c851 h hv u37_57
  have u39_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24632 h hv u30_18 u37_57
  have u40_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c31589 h h0 hv u38_252 u20_196 u23_287
  have u41_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c31574 h h0 hv u39_284 u24_193 u1_304
  have u42_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32634 h h0 u40_307 u38_252 u23_287 hv
  have u43_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31572 h h0 u41_249 u24_193 hv u1_304 u39_284
  exact c31643 h h0 u43_109 u42_112

theorem c32658 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u3_29
  have u5_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32654 h h0 hv a93 n105 n24
  have u6_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28418 h u5_311 n24 hv
  have u7_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28530 h u5_311 n24 hv n105
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32524 h h0 u5_311 hv u6_40
  have u9_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32526 h h0 hv u5_311 u6_40
  have u10_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u8_38
  have u11_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c605 h hv u9_41
  have u12_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c32657 h h0 hv a93 n105 n24
  have u13_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1170 h hv u12_78
  have u14_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 u13_291 u4_200 hv u5_311
  have u15_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c20713 h u14_256 hv u7_73
  have u16_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19732 h hv u15_18 u12_78
  have u17_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31322 h h0 u2_193 hv u16_249 u0_304
  have u18_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u17_109
  have u19_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u17_109
  have u20_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13852 h hv u3_29 u17_109
  exact c31535 h h0 u18_206 u19_209 u1_210 u20_207 u11_208 u10_205

end BorsukNine.FiniteObstruction

end OAI
