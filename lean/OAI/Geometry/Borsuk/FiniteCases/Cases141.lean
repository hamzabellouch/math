import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases140

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32789 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 8} → Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → False := by
  classical
  intro a233 a307 n309
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u3_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u4_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h a307 u0_24 hv
  have u5_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c32477 h h0 a307 hv
  have u6_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c17575 h a233 hv u2_72 u1_105
  have u7_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c17581 h a233 u2_72 u1_105 hv
  have u8_26 : T {0, 4, 9} := by
    by_contra hv
    exact c17594 h a233 hv u7_107 u5_109
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c17596 h a233 hv u7_107 u5_109
  have u10_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25336 h hv u6_23 u3_49
  have u11_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 u7_107 hv
  have u12_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c27967 h a307 u8_26 hv u9_75
  have u13_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 n309 u11_114 hv u10_289
  exact c12634 h u13_198 u4_43 u3_49 u12_54

private theorem c32790 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 8} → Q {3, 5, 6, 8} → False := by
  classical
  intro a298 a307
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u6_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u7_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u8_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u9_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h a307 u0_24 hv
  have u10_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c32477 h h0 a307 hv
  have u11_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1674 h a307 hv
  have u12_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1539 h a298 hv
  have u13_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c32387 h h0 a298 hv
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31704 h h0 u11_112 u12_103 hv
  have u15_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31751 h h0 u13_118 hv u10_109
  have u16_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31755 h h0 u13_118 u10_109 hv
  have u17_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u14_114
  have u18_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u14_114
  have u19_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6285 h hv u1_51 u15_115
  have u20_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u1_51 u16_120
  have u21_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7639 h hv u1_51 u3_105 u18_107
  have u22_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4699 h hv u2_72 u3_105 u18_107
  have u23_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31443 h u6_177 u22_141 u4_29 u5_200 u21_162 u17_198 hv
  have u24_54 : T {1, 4, 9} := by
    by_contra hv
    exact c12354 h u23_196 u9_43 u7_49 hv
  have u25_63 : T {1, 7, 9} := by
    by_contra hv
    exact c12356 h u23_196 u9_43 u7_49 hv
  have u26_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6149 h hv u24_54 u11_112
  have u27_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6019 h hv u25_63 u12_103
  have u28_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5739 h hv u25_63 u11_112
  exact c31534 h h0 u19_153 u20_150 u28_149 u8_154 u26_152 u27_151

private theorem c32791 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → T {3, 5, 8} → False := by
  classical
  intro a307 n309 a93
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u4_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u5_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c32477 h h0 a307 hv
  have u6_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h a307 u1_24 hv
  have u7_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c32789 h h0 hv a307 n309
  have u8_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32790 h h0 hv a307
  have u9_268 : Q {2, 3, 5, 8} := by
    by_contra hv
    exact c32783 h h0 u8_298 hv u0_177 u7_233 a93 n309
  have u10_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c22389 h u9_268 hv u2_105
  have u11_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c22483 h u9_268 u1_24 hv u2_105
  have u12_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c22393 h u9_268 u1_24 hv
  have u13_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c22481 h u9_268 u3_51 u2_105 hv
  have u14_33 : T {0, 6, 9} := by
    by_contra hv
    exact c22506 h u9_268 hv u12_61 u13_107
  have u15_15 : T {0, 2, 9} := by
    by_contra hv
    exact c27854 h a307 hv u11_52
  have u16_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25408 h hv u10_8 u4_49 u12_61
  have u17_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12636 h hv u6_43 u4_49 u12_61
  have u18_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 u13_107 hv
  have u19_26 : T {0, 4, 9} := by
    by_contra hv
    exact c22494 h u9_268 hv u13_107 u5_109
  have u20_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20479 h hv u15_15 u19_26 u14_33
  exact c31595 h h0 u20_254 u16_289 n309 u17_198 u18_114

private theorem c32792 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 5, 8} → ¬ Q {3, 5, 7, 8} → False := by
  classical
  intro a268 n309
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u4_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u5_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u6_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u7_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u8_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c22389 h a268 hv u2_105
  have u9_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c22393 h a268 u0_24 hv
  have u10_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c22487 h a268 u0_24 u2_105 hv
  have u11_5 : T {0, 1, 6} := by
    by_contra hv
    exact c22384 h a268 hv u10_109
  have u12_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c22481 h a268 u1_51 u2_105 hv
  have u13_33 : T {0, 6, 9} := by
    by_contra hv
    exact c22506 h a268 hv u9_61 u12_107
  have u14_118 : T {6, 7, 9} := by
    by_contra hv
    exact c22512 h a268 u9_61 u12_107 hv
  have u15_6 : T {0, 1, 7} := by
    by_contra hv
    exact c22386 h a268 hv u12_107
  have u16_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25408 h hv u8_8 u7_49 u9_61
  have u17_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u10_109 hv
  have u18_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c22451 h a268 u11_5 u1_51 hv
  have u19_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1599 h hv u12_107
  have u20_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 u12_107 hv
  have u21_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c22423 h a268 u11_5 hv u13_33
  have u22_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31722 h h0 hv u2_105 u14_118
  have u23_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31724 h h0 hv u2_105 u14_118
  have u24_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21967 h hv u15_6 u17_112
  have u25_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32398 h h0 hv u15_6 u11_5
  have u26_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32460 h h0 hv u15_6 u11_5
  have u27_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23496 h hv u21_31 u18_59 u22_111
  have u28_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22640 h hv u21_31 u18_59 u23_117
  have u29_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9342 h hv u18_59 u22_111 u23_117
  have u30_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 n309 u20_114 hv u16_289
  have u31_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c1337 h hv u29_174 u3_230 u24_265 u25_299 u19_302 u4_304 u26_305
  have u32_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32665 h h0 u28_269 hv u6_154 u5_274 u24_265 u27_275
  exact c12690 h u30_198 u7_49 u32_70 u31_90

private theorem c32793 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 8} → ¬ Q {3, 5, 7, 8} → T {3, 5, 8} → False := by
  classical
  intro n233 n309 a93
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u1_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u2_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c32792 h h0 hv n309
  have u3_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32791 h h0 hv n309 a93
  have u4_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1390 h hv u1_177 n233 u2_268 u3_307 n309 u0_311
  exact c32783 h h0 u4_298 u2_268 u1_177 n233 a93 n309

private theorem c32794 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 7, 8} → T {3, 5, 8} → False := by
  classical
  intro n309 a93
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32791 h h0 hv n309 a93
  have u6_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c32792 h h0 hv n309
  have u7_233 : Q {1, 3, 5, 8} := by
    by_contra hv
    exact c32793 h h0 hv n309 a93
  have u8_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c17581 h u7_233 u3_72 u4_105 hv
  have u9_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c17493 h u7_233 u2_24 hv
  have u10_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1386 h u7_233 u0_177 u6_268 hv u5_307 n309 u1_311
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c17612 h u7_233 u9_82 u8_107 hv
  exact c32387 h h0 u10_298 u11_118

theorem c32795 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 5, 8} → False := by
  classical
  intro a93
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u4_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u5_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u6_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u7_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u8_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u9_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c32787 h h0 hv
  have u10_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u11_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c32788 h h0 hv
  have u12_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u13_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c32794 h h0 hv a93
  have u14_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c32497 h h0 u13_309 hv
  have u15_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28239 h u13_309 hv u0_51 u4_72
  have u16_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c28129 h u13_309 hv u4_72
  have u17_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c341 h hv u15_23
  have u18_43 : T {1, 2, 9} := by
    by_contra hv
    exact c28136 h u13_309 u15_23 hv
  have u19_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26877 h hv u3_29 u18_43
  have u20_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u6_24 u18_43
  have u21_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32505 h h0 u13_309 hv u18_43
  have u22_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32506 h h0 u13_309 u18_43 hv
  have u23_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u19_300 u17_189 u5_105
  have u24_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9922 h hv u21_38 u1_116
  have u25_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8944 h hv u22_40 u1_116
  have u26_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u23_280 hv
  have u27_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u23_280 hv u17_189 u19_300
  have u28_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24179 h u23_280 u3_29 hv a93
  have u29_58 : T {1, 5, 9} := by
    by_contra hv
    exact c24146 h u23_280 u16_8 u2_49 hv
  have u30_64 : T {1, 8, 9} := by
    by_contra hv
    exact c24148 h u23_280 u16_8 u2_49 hv
  have u31_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17583 h hv u6_24 u26_73 u5_105
  have u32_52 : T {1, 4, 7} := by
    by_contra hv
    exact c776 h u27_245 hv
  have u33_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c19279 h u27_245 u3_29 hv a93
  have u34_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c851 h hv u28_57
  have u35_21 : T {0, 3, 9} := by
    by_contra hv
    exact c24074 h u23_280 hv u28_57
  have u36_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6152 h hv u28_57 u14_107
  have u37_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10359 h hv u29_58 u4_72
  have u38_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9521 h hv u30_64 u4_72
  have u39_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22483 h hv u6_24 u32_52 u5_105
  have u40_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1166 h hv u33_78
  have u41_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3212 h hv u33_78 u14_107
  have u42_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1394 h u13_309 u7_177 u31_233 u39_268 hv u20_307 u8_311
  have u43_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31586 h h0 hv u40_287 u34_252 u20_307
  have u44_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31585 h h0 u43_196 u40_287 u34_252 u20_307 hv
  have u45_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c286 h hv u41_131 u36_152 u25_172 u38_176 u24_179 u37_182
  have u46_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32396 h h0 hv u42_298 u18_43
  have u47_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9226 h hv u46_41 u44_112
  exact c31485 h u11_178 u35_21 u45_183 u9_184 u10_133 u12_154 u47_174

end BorsukNine.FiniteObstruction

end OAI
