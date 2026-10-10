import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases137

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32770 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 6} → ¬ T {2, 4, 6} → False := by
  classical
  intro a51 n72
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u4_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32768 h h0 hv n72
  have u5_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12314 h u4_196 u1_49 hv
  have u6_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u7_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23239 h hv u0_29 a51
  have u8_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32769 h h0 hv a51 n72
  have u9_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u8_300 hv
  have u10_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h u8_300 u0_29 hv
  have u11_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12419 h u4_196 hv u5_73 u9_88
  have u12_63 : T {1, 7, 9} := by
    by_contra hv
    exact c12356 h u4_196 u10_43 u1_49 hv
  have u13_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c776 h hv u11_52
  have u14_70 : T {2, 3, 9} := by
    by_contra hv
    exact c12316 h u4_196 u11_52 hv
  have u15_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c12321 h u4_196 u12_63 hv
  have u16_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u6_280 u13_245 u2_105 hv
  have u17_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c31816 h h0 u16_189 hv u14_70
  have u18_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c31815 h h0 u16_189 hv u14_70
  have u19_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c975 h hv u15_65
  have u20_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c1035 h hv u17_69
  have u21_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c990 h hv u18_66
  exact c32665 h h0 u21_269 u14_70 u3_154 u7_274 u19_265 u20_275

theorem c32771 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 4, 6} → False := by
  classical
  intro n72
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u3_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u4_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32768 h h0 hv n72
  have u5_27 : T {0, 5, 6} := by
    by_contra hv
    exact c403 h u4_196 hv
  have u6_32 : T {0, 6, 8} := by
    by_contra hv
    exact c476 h u4_196 hv
  have u7_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12314 h u4_196 u0_49 hv
  have u8_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c32770 h h0 hv n72
  have u9_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv u8_51
  have u10_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 u3_280 u9_245 hv
  have u11_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u3_280 u9_245 u1_105 hv
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u10_300 hv
  have u13_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u11_189 hv
  have u14_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u11_189 hv
  have u15_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12419 h u4_196 hv u7_73 u12_88
  have u16_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23273 h hv u13_23 u5_27 u6_32
  have u17_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23413 h hv u13_23 u5_27 u14_31
  have u18_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22005 h hv u5_27 u14_31 u6_32
  have u19_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22565 h hv u13_23 u14_31 u6_32
  have u20_70 : T {2, 3, 9} := by
    by_contra hv
    exact c12316 h u4_196 u15_52 hv
  exact c32665 h h0 u19_269 u20_70 u2_154 u16_274 u18_265 u17_275

theorem c32772 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 7, 8, 9} → T {1, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {0, 1, 8, 9} → False := by
  classical
  intro n260 a64 n259 n225 n148
  have u0_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u1_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32746 h h0 hv
  have u2_250 : Q {1, 4, 8, 9} := by
    by_contra hv
    exact c947 h a64 n148 n225 u0_240 hv u1_256 n259 n260
  exact c955 h u2_250 n148 n225 u0_240 u1_256 n259 n260

theorem c32773 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → ¬ Q {1, 6, 8, 9} → Q {3, 4, 6, 7} → False := by
  classical
  intro a189 n259 a300
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u4_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u6_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16473 h hv u1_24 u5_88 u2_105
  have u7_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u8_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5685 h hv u4_72 u7_87 u2_105
  have u9_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h a300 u0_29 hv
  have u10_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h a189 hv
  have u11_64 : T {1, 8, 9} := by
    by_contra hv
    exact c11376 h a189 u9_43 u3_49 hv
  have u12_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21387 h hv u10_23 u4_72 u7_87
  exact c32772 h h0 u12_260 u11_64 n259 u6_225 u8_148

private theorem c32774 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 8, 9} → Q {0, 5, 6, 8} → Q {3, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  classical
  intro a64 a196 a300 n51
  have u0_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u5_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u7_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u9_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12314 h a196 u2_49 hv
  have u10_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21247 h hv u3_24 u9_73 u8_88
  have u11_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c32773 h h0 hv u10_259 a300
  have u12_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 hv u7_245 u4_105 u11_189
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1668 h a196 hv
  have u14_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h a300 u6_29 hv
  have u15_63 : T {1, 7, 9} := by
    by_contra hv
    exact c12356 h a196 u14_43 u2_49 hv
  have u16_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5739 h hv u15_63 u13_112
  have u17_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12419 h a196 hv u9_73 u8_88
  have u18_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6004 h hv u17_52 u1_116
  have u19_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16473 h hv u3_24 u8_88 u4_105
  have u20_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u21_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5685 h hv u0_72 u20_87 u4_105
  have u22_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6144 h hv n51 u1_116
  have u23_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5881 h hv a64 u4_105
  have u24_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c24071 h u12_280 hv a64
  have u25_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c26871 h a300 hv a64
  have u26_260 : Q {1, 7, 8, 9} := by
    by_contra hv
    exact c32772 h h0 hv a64 u10_259 u19_225 u21_148
  have u27_153 : Q {0, 2, 3, 8} := by
    by_contra hv
    exact c31534 h h0 hv u23_150 u16_149 u5_154 u22_152 u18_151
  have u28_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26172 h hv u24_17 n51
  have u29_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28972 h hv u25_11 n51
  have u30_14 : T {0, 2, 8} := by
    by_contra hv
    exact c200 h u27_153 hv
  have u31_204 : Q {0, 7, 8, 9} := by
    by_contra hv
    exact c31624 h h0 u26_260 u28_295 hv u29_315
  have u32_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c26913 h a300 u30_14 u6_29 hv
  exact c540 h u31_204 u32_36

theorem c32775 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → Q {3, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  classical
  intro a196 a300 n51
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u4_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h a300 u0_29 hv
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u6_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u7_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12314 h a196 u3_49 hv
  have u8_54 : T {1, 4, 9} := by
    by_contra hv
    exact c12354 h a196 u4_43 u3_49 hv
  have u9_63 : T {1, 7, 9} := by
    by_contra hv
    exact c12356 h a196 u4_43 u3_49 hv
  have u10_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20259 h hv u1_24 u7_73 u5_88
  have u11_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21247 h hv u1_24 u7_73 u5_88
  have u12_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c32773 h h0 hv u11_259 a300
  have u13_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 hv u6_245 u2_105 u12_189
  have u14_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c32774 h h0 hv a196 a300 n51
  have u15_8 : T {0, 1, 9} := by
    by_contra hv
    exact c24148 h u13_280 hv u3_49 u14_64
  have u16_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25131 h hv u15_8 u8_54 u9_63
  have u17_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27849 h hv u15_8 u7_73
  exact c31586 h h0 a196 u16_287 u10_252 u17_307

theorem c32776 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 8, 9} → Q {3, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  classical
  intro n64 a300 n51
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u6_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c32775 h h0 hv a300 n51
  have u7_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4695 h hv u3_72 u7_87 u2_105
  have u9_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h a300 u4_29 hv
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u11_11 : T {0, 2, 5} := by
    by_contra hv
    exact c26870 h a300 hv n64
  have u12_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11376 h hv u9_43 u0_49 n64
  have u13_58 : T {1, 5, 9} := by
    by_contra hv
    exact c26952 h a300 u9_43 hv n64
  have u14_36 : T {0, 8, 9} := by
    by_contra hv
    exact c26996 h a300 hv n64 u1_116
  have u15_85 : T {2, 8, 9} := by
    by_contra hv
    exact c27000 h a300 n64 hv u1_116
  have u16_8 : T {0, 1, 9} := by
    by_contra hv
    exact c26948 h a300 hv u9_43 n64
  have u17_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c26905 h a300 u11_11 u4_29 hv
  have u18_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c32411 h h0 hv u11_11 a300
  have u19_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c26899 h a300 hv u11_11 u4_29
  have u20_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 hv u10_245 u2_105 u12_189
  have u21_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c24073 h u20_280 hv u13_58
  have u22_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15261 h hv u14_36 u7_87
  have u23_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17361 h hv u14_36 u3_72
  have u24_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4481 h hv u15_85 u7_87
  have u25_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28129 h hv u16_8 u3_72
  have u26_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25329 h hv u16_8 u7_87
  have u27_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c448 h hv u17_30
  have u28_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c204 h hv u18_14
  have u29_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28274 h hv u18_14 n51
  have u30_100 : T {3, 8, 9} := by
    by_contra hv
    exact c24064 h u20_280 u19_4 hv
  have u31_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c294 h hv u21_20
  have u32_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25474 h hv u21_20 n51
  have u33_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18875 h hv u14_36 u15_85 u30_100
  have u34_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20135 h hv u14_36 u15_85 u30_100
  have u35_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u31_177 u8_141 u4_29 u5_200 u28_162 hv u6_196
  have u36_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c31601 h h0 hv u29_310 u32_290 u27_199
  have u37_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c839 h hv u24_140 u22_217 u23_232 u33_242 u34_251 u36_255
  exact c31596 h h0 u35_198 u26_289 u37_254 u25_309

end BorsukNine.FiniteObstruction

end OAI
