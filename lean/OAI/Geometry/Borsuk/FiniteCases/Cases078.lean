import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases004
import OAI.Geometry.Borsuk.FiniteCases.Cases005
import OAI.Geometry.Borsuk.FiniteCases.Cases008
import OAI.Geometry.Borsuk.FiniteCases.Cases009
import OAI.Geometry.Borsuk.FiniteCases.Cases010
import OAI.Geometry.Borsuk.FiniteCases.Cases011
import OAI.Geometry.Borsuk.FiniteCases.Cases017
import OAI.Geometry.Borsuk.FiniteCases.Cases019
import OAI.Geometry.Borsuk.FiniteCases.Cases021
import OAI.Geometry.Borsuk.FiniteCases.Cases022
import OAI.Geometry.Borsuk.FiniteCases.Cases028
import OAI.Geometry.Borsuk.FiniteCases.Cases029
import OAI.Geometry.Borsuk.FiniteCases.Cases032
import OAI.Geometry.Borsuk.FiniteCases.Cases034
import OAI.Geometry.Borsuk.FiniteCases.Cases036
import OAI.Geometry.Borsuk.FiniteCases.Cases037
import OAI.Geometry.Borsuk.FiniteCases.Cases038
import OAI.Geometry.Borsuk.FiniteCases.Cases041
import OAI.Geometry.Borsuk.FiniteCases.Cases042
import OAI.Geometry.Borsuk.FiniteCases.Cases044
import OAI.Geometry.Borsuk.FiniteCases.Cases045
import OAI.Geometry.Borsuk.FiniteCases.Cases046
import OAI.Geometry.Borsuk.FiniteCases.Cases047
import OAI.Geometry.Borsuk.FiniteCases.Cases049
import OAI.Geometry.Borsuk.FiniteCases.Cases051
import OAI.Geometry.Borsuk.FiniteCases.Cases052
import OAI.Geometry.Borsuk.FiniteCases.Cases053
import OAI.Geometry.Borsuk.FiniteCases.Cases056
import OAI.Geometry.Borsuk.FiniteCases.Cases057
import OAI.Geometry.Borsuk.FiniteCases.Cases060
import OAI.Geometry.Borsuk.FiniteCases.Cases061
import OAI.Geometry.Borsuk.FiniteCases.Cases070
import OAI.Geometry.Borsuk.FiniteCases.Cases072
import OAI.Geometry.Borsuk.FiniteCases.Cases077

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31229 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ T {2, 5, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n111 n311 n305 n275 n314 n76 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u2_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10744 h hv n76 u1_101 n111
  have u3_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18584 h hv n76 u1_101 n111
  exact c1501 h a315 u2_184 u3_240 n275 n305 n311 n314

theorem c31230 (h : TenSystem T Q) :
    ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → T {1, 4, 5} → False := by
  classical
  intro n226 n244 n134 n211 n241 n242 a50
  have u0_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c737 h a50 n134 n211 n226 n241 n242 hv n244
  exact c749 h u0_243 n134 n211 n226 n241 n242 n244

theorem c31231 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 8, 9} → ¬ Q {1, 3, 5, 9} → T {6, 8, 9} → ¬ T {2, 3, 4} → T {4, 6, 7} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 2, 4, 5} → ¬ T {0, 2, 4} → T {2, 4, 6} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 4, 5} → T {1, 5, 6} → ¬ T {4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a184 n234 a119 n65 a105 n256 n211 n10 a72 n142 n134 a55 n101 a120
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18743 h hv u1_9 a119
  have u3_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1805 h u0_121 hv a119
  have u4_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u1_9 a120
  have u5_20 : T {0, 3, 8} := by
    by_contra hv
    exact c300 h a184 hv
  have u6_36 : T {0, 8, 9} := by
    by_contra hv
    exact c532 h a184 hv
  have u7_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c10637 h a184 a55 hv
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c10718 h a184 hv n101 u3_102
  have u9_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15529 h hv u5_20 a105
  have u10_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20575 h hv u5_20 a72
  have u11_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16639 h hv u6_36 a119 a120
  have u12_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20350 h hv n10 n65 u7_73
  have u13_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c865 h hv n142 u9_219 n234 u12_253 u10_255 n256
  exact c31230 h u11_226 u13_244 n134 n211 u4_241 u2_242 u8_50

private theorem c31232 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → T {0, 4, 5} → False := by
  classical
  intro n170 n188 n134 n155 n185 n186 a22
  have u0_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c317 h a22 n134 n155 n170 n185 n186 hv n188
  exact c329 h u0_187 n134 n155 n170 n185 n186 n188

private theorem c31233 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 4, 8} → ¬ T {0, 1, 7} → ¬ Q {3, 6, 8, 9} → T {2, 4, 6} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ T {0, 1, 6} → ¬ T {2, 5, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n116 n305 n265 n264 n6 n314 a72 n142 n134 n5 n76 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u4_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv n6 u3_101
  have u5_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv n76 u3_101
  have u6_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u5_55
  have u7_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c142 h hv u6_10
  have u8_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv n76 u3_101
  have u9_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u8_27 hv
  have u10_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u9_38
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u12_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u5_55 u11_120
  have u13_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u8_27 u11_120
  have u14_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10763 h hv u2_37 u11_120
  have u15_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv n116
  have u16_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv n116
  have u17_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv n116
  have u18_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u19_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21684 h hv n5 n116
  have u20_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21544 h hv n6 n116
  have u21_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31229 h h0 hv u17_311 n305 u4_275 n314 n76 a315
  have u22_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c968 h hv u12_149 u13_205 u20_262 u19_263 n264 n265
  have u23_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1821 h u1_121 hv u21_111
  have u24_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1895 h u1_121 u18_105 u21_111 hv
  have u25_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u12_149 u13_205 u22_261 u20_262 u19_263 n264 n265
  have u26_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1934 h u1_121 u23_110 n116 hv
  have u27_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9782 h hv u9_38 u24_117
  have u28_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17622 h hv u6_10 u24_117
  have u29_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10903 h hv u2_37 u26_119
  have u30_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c31231 h h0 hv u28_234 u26_119 u25_65 u18_105 u16_256 u10_211 u6_10 a72 n142 n134 u5_55 u3_101 u11_120
  have u31_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u30_184 hv u4_275 n305 u17_311 n314
  have u32_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u31_240 hv
  have u33_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u31_240 hv
  have u34_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u31_240 hv u18_105
  have u35_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18477 h u31_240 u8_27 hv
  have u36_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c18479 h u31_240 hv a72
  have u37_22 : T {0, 4, 5} := by
    by_contra hv
    exact c18500 h u31_240 u34_11 hv u36_28
  have u38_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7689 h hv u32_48 u18_105
  have u39_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12735 h hv u32_48 a72
  have u40_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8799 h hv u33_64 u26_119 u11_120
  have u41_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12510 h hv u9_38 u25_65 u35_73
  have u42_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c445 h hv n142 u38_163 u27_178 u41_197 u39_199 u15_200
  exact c31232 h u40_170 u42_188 n134 u7_155 u14_185 u29_186 u37_22

private theorem c31234 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ T {0, 4, 5} → ¬ T {0, 1, 7} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro n311 n22 n6 a315 a3
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u6_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u7_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u0_1 a3 hv
  have u8_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u9_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c52 h hv u8_4
  have u10_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u8_4
  have u11_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u8_4 hv
  have u12_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u13_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21842 h hv u8_4 u7_5 n6
  have u14_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21982 h hv u8_4 u7_5 n6
  have u15_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27588 h hv u8_4 u7_5 n6
  have u16_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31233 h h0 hv u15_305 u14_265 u13_264 n6 u12_314 u11_72 u10_142 u9_134 u7_5 u6_76 a315
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1941 h u1_121 u16_116 hv u5_120
  have u18_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u1_121 hv u17_119
  have u19_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u20_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u19_40 u18_102
  have u21_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u22_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u6_76 u21_101
  have u23_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u22_55
  have u24_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29004 h a315 u23_10 n22 hv
  have u25_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u8_4 u17_119
  have u26_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv n6 u17_119
  have u27_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u6_76 u21_101
  have u28_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u27_27 u5_120
  have u29_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u22_55 u5_120
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c970 h hv u29_149 u28_205 u26_261 u25_263 u13_264 u14_265
  have u31_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u29_149 u28_205 u26_261 u30_262 u25_263 u13_264 u14_265
  have u32_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv n6 u21_101
  have u33_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u27_27 hv
  have u34_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u20_184 hv u32_275 u15_305 n311 u12_314
  have u35_24 : T {0, 4, 7} := by
    by_contra hv
    exact c18474 h u34_240 hv u6_76
  have u36_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18477 h u34_240 u27_27 hv
  have u37_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25643 h hv a3 u24_23 u35_24
  have u38_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20772 h hv u23_10 u31_65 u36_73
  have u39_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12932 h hv u33_38 u31_65 u36_73
  exact c1727 h u16_116 u39_200 u38_256 u37_291 n311 u4_321 u3_328 u2_329

theorem c31235 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 5} → ¬ T {0, 1, 7} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro n22 n6 a315 a3
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u0_1 a3 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u4_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21982 h hv u3_4 u2_5 n6
  have u5_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21842 h hv u3_4 u2_5 n6
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u7_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u8_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c52 h hv u3_4
  have u9_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u3_4
  have u10_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u3_4 hv
  have u11_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u12_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27588 h hv u3_4 u2_5 n6
  have u13_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31233 h h0 hv u12_305 u4_265 u5_264 n6 u11_314 u10_72 u9_142 u8_134 u2_5 u7_76 a315
  have u14_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1941 h u1_121 u13_116 hv u6_120
  have u15_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u3_4 u14_119
  have u16_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u17_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u7_76 u16_101
  have u18_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u17_55 u6_120
  have u19_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u7_76 u16_101
  have u20_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u19_27 u6_120
  have u21_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv n6 u14_119
  have u22_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c970 h hv u18_149 u20_205 u21_261 u15_263 u5_264 u4_265
  have u23_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22663 h hv a3 u13_116
  have u24_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u17_55
  have u25_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u19_27 hv
  have u26_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22103 h hv a3 u6_120
  have u27_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u28_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u16_101
  have u29_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u14_119
  have u30_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29004 h a315 u24_10 n22 hv
  have u31_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29071 h a315 hv u27_40 u10_72
  have u32_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u28_50 u6_120
  have u33_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13703 h hv u30_23 u6_120
  have u34_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31234 h h0 hv n22 n6 a315 a3
  have u35_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28412 h u34_311 u31_12 hv
  have u36_31 : T {0, 6, 7} := by
    by_contra hv
    exact c28420 h u34_311 hv u25_38
  have u37_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22863 h hv a3 u28_50 u35_52
  have u38_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23003 h hv a3 u28_50 u35_52
  have u39_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14159 h hv u30_23 u19_27 u36_31
  have u40_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14299 h hv u30_23 u19_27 u36_31
  have u41_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c996 h hv u32_151 u22_262 u26_266 u23_270 u37_271 u38_272
  exact c544 h u1_121 u20_205 u33_206 u41_207 u29_208 u39_209 u40_210

end BorsukNine.FiniteObstruction

end OAI
