import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases142

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32806 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 4, 7} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 7, 8, 9} → T {6, 8, 9} → T {5, 6, 8} → False := by
  classical
  intro a157 n275 n315 a119 a112
  have u0_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u1_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c32787 h h0 hv
  have u2_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u3_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u4_10 : T {0, 2, 4} := by
    by_contra hv
    exact c146 h a157 hv
  have u5_13 : T {0, 2, 7} := by
    by_contra hv
    exact c187 h a157 hv
  have u6_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c6843 h a157 hv a119
  have u7_91 : T {3, 5, 6} := by
    by_contra hv
    exact c6902 h a157 u6_45 hv u0_93
  have u8_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c6935 h a157 hv u7_91 a112
  have u9_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32552 h h0 hv u5_13 u4_10
  have u10_100 : T {3, 8, 9} := by
    by_contra hv
    exact c6850 h a157 u8_55 hv
  have u11_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1495 h hv u1_184 u3_240 n275 u2_311 u9_314 n315
  exact c1487 h u10_100 u1_184 u3_240 n275 u11_305 u2_311 u9_314 n315

private theorem c32807 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 4, 7} → T {2, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a172 a82 a114
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u2_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32800 h h0 hv
  have u3_16 : T {0, 3, 4} := by
    by_contra hv
    exact c236 h a172 hv
  have u4_40 : T {1, 2, 6} := by
    by_contra hv
    exact c8944 h a172 hv u0_116
  have u5_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20431 h hv u3_16 a82
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12663 h hv u4_40 u1_72 a82
  have u7_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c31598 h h0 hv u5_254 u6_198 u2_309
  exact c31595 h h0 u5_254 u7_289 u2_309 u6_198 a114

private theorem c32808 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 8, 9} → T {2, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro a119 a82 n107
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u3_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u4_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c32787 h h0 hv
  have u5_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u6_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u8_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c32807 h h0 hv a82 u7_114
  have u9_118 : T {6, 7, 9} := by
    by_contra hv
    exact c32804 h h0 hv n107
  have u10_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31722 h h0 hv u1_105 u9_118
  have u11_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31645 h h0 hv u10_111
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31632 h h0 hv u9_118
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31705 h h0 u0_116 u12_103 hv
  have u14_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31630 h h0 hv a119
  have u15_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31764 h h0 hv u11_110 a119
  have u16_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31647 h h0 u14_102 hv u12_103
  have u17_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u15_120
  have u18_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23469 h hv u2_51 u16_101 u1_105
  have u19_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c32806 h h0 hv u18_275 u17_315 a119 u13_112
  have u20_136 : Q {0, 1, 4, 7} := by
    by_contra hv
    exact c32805 h h0 u19_157 u8_172 hv a119 a82 n107
  have u21_3 : T {0, 1, 4} := by
    by_contra hv
    exact c41 h u20_136 hv
  have u22_6 : T {0, 1, 7} := by
    by_contra hv
    exact c82 h u20_136 hv
  have u23_96 : ¬ T {3, 6, 8} := by
    intro hv
    exact c4025 h u20_136 hv u13_112 a119
  have u24_100 : T {3, 8, 9} := by
    by_contra hv
    exact c3984 h u20_136 u3_93 u23_96 hv
  have u25_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32549 h h0 hv u22_6 u21_3
  have u26_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1495 h hv u4_184 u6_240 u18_275 u5_311 u25_314 u17_315
  exact c1487 h u24_100 u4_184 u6_240 u18_275 u26_305 u5_311 u25_314 u17_315

private theorem c32809 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → T {7, 8, 9} → ¬ Q {0, 7, 8, 9} → False := by
  classical
  intro n260 n315 a120 n204
  have u0_295 : Q {2, 7, 8, 9} := by
    by_contra hv
    exact c31622 h h0 n260 a120 n204 n315 hv
  exact c31625 h h0 u0_295 n315 n204 n260

private theorem c32810 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 4, 7} → ¬ Q {0, 3, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ T {6, 8, 9} → False := by
  classical
  intro a136 n183 n310 n119
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u2_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u5_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31765 h h0 n119 hv u0_116
  have u7_3 : T {0, 1, 4} := by
    by_contra hv
    exact c41 h a136 hv
  have u8_66 : T {2, 3, 5} := by
    by_contra hv
    exact c3902 h a136 hv n119
  have u9_67 : T {2, 3, 6} := by
    by_contra hv
    exact c3904 h a136 hv u0_116
  have u10_78 : T {2, 5, 8} := by
    by_contra hv
    exact c4004 h a136 hv u1_93 u0_116
  have u11_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28685 h hv u7_3 u10_78
  have u12_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13439 h hv u2_51 u8_66
  have u13_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c32166 h h0 u8_66 hv u9_67
  have u14_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1486 h hv n183 u4_239 u5_274 u3_304 n310 u11_313
  exact c32809 h h0 u13_260 u14_315 u6_120 u12_204

private theorem c32811 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 8, 9} → ¬ Q {0, 1, 4, 7} → ¬ T {2, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ T {6, 8, 9} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 7, 9} → False := by
  classical
  intro n100 n136 n70 n192 n119 n172 n193
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6980 h hv n100 u0_116 n119
  have u3_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c11012 h hv u1_49 n70 n100
  exact c32801 h h0 n172 n193 n136 n192 u3_186 u2_157

private theorem c32812 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 7, 8, 9} → T {3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 6, 8, 9} → False := by
  classical
  intro n315 a100 n275 n314
  have u0_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c32787 h h0 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u2_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u3_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1495 h hv u0_184 u2_240 n275 u1_311 n314 n315
  exact c1487 h a100 u0_184 u2_240 n275 u3_305 u1_311 n314 n315

theorem c32813 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro a82 n107
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u4_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u5_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u6_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u7_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u8_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u9_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32800 h h0 hv
  have u10_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c32804 h h0 hv n107
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31632 h h0 hv u11_118
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31705 h h0 u0_116 u12_103 hv
  have u14_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv u1_29 u13_112 u10_114
  have u15_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31847 h h0 hv u13_112
  have u16_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31724 h h0 hv u3_105 u11_118
  have u17_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c32807 h h0 hv a82 u10_114
  have u18_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c32808 h h0 hv a82 n107
  have u19_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv u18_119
  have u20_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31629 h h0 hv u18_119
  have u21_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31731 h h0 u18_119 hv u16_117
  have u22_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31737 h h0 u18_119 hv n107
  have u23_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23475 h hv u2_24 u20_102 u3_105
  have u24_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u21_106
  have u25_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22621 h hv u6_51 u3_105 u21_106
  have u26_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10585 h hv u6_51 u7_72 u21_106
  have u27_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31837 h h0 hv u22_113
  have u28_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32665 h h0 u25_269 hv u5_154 u4_274 u14_265 u23_275
  have u29_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c32810 h h0 hv u26_183 u24_310 u18_119
  have u30_100 : T {3, 8, 9} := by
    by_contra hv
    exact c32811 h h0 hv u29_136 u28_70 u27_192 u18_119 u17_172 u15_193
  have u31_315 : Q {3, 7, 8, 9} := by
    by_contra hv
    exact c32812 h h0 hv u30_100 u23_275 u19_314
  have u32_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c29087 h u31_315 hv u6_51 u7_72
  have u33_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25336 h hv u32_23 u8_49
  have u34_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20436 h hv u32_23 u28_70
  have u35_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 u9_309 u10_114 hv u33_289
  exact c31596 h h0 u35_198 u33_289 u34_254 u9_309

theorem c32814 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 6} → ¬ T {2, 3, 9} → T {5, 7, 8} → False := by
  classical
  intro n23 n70 a114
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32800 h h0 hv
  have u2_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25336 h hv n23 u0_49
  have u3_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20436 h hv n23 n70
  have u4_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 u1_309 a114 hv u2_289
  exact c31596 h h0 u4_198 u2_289 u3_254 u1_309

theorem c32815 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n119 n107
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u4_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u5_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u6_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u7_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u8_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u9_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u10_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c32813 h h0 hv n107
  have u11_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1222 h hv u10_82
  have u12_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u13_118 : T {6, 7, 9} := by
    by_contra hv
    exact c32804 h h0 hv n107
  have u14_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31632 h h0 hv u13_118
  have u15_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31705 h h0 u1_116 u14_103 hv
  have u16_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv u0_29 u15_112 u12_114
  have u17_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31724 h h0 hv u3_105 u13_118
  have u18_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c1593 h hv n107
  have u19_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv n119
  have u20_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31629 h h0 hv n119
  have u21_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31765 h h0 n119 hv u1_116
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31731 h h0 n119 hv u17_117
  have u23_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23475 h hv u2_24 u20_102 u3_105
  have u24_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c31767 h h0 hv u21_120
  have u25_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u22_106
  have u26_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22621 h hv u4_51 u3_105 u22_106
  have u27_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10585 h hv u4_51 u5_72 u22_106
  have u28_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32710 h h0 u16_265 u11_272 u26_269 u23_275 hv
  have u29_23 : T {0, 4, 6} := by
    by_contra hv
    exact c32814 h h0 hv u28_70 u12_114
  have u30_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c29087 h hv u29_23 u4_51 u5_72
  have u31_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1484 h hv u27_183 u8_239 u7_274 u6_304 u25_310 u30_315
  have u32_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c31288 h u25_310 u27_183 u30_315 u7_274 u31_313 hv u8_239
  have u33_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c32812 h h0 u30_315 hv u23_275 u19_314
  have u34_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11572 h hv u9_49 u28_70 u32_99
  have u35_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3850 h hv u28_70 u32_99 u33_100
  have u36_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6790 h hv u9_49 u32_99 u33_100
  have u37_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11432 h hv u9_49 u28_70 u33_100
  have u38_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c338 h hv u35_135 u36_156 u24_185 u37_189 u34_190 u18_191
  exact c31487 h u38_171 u24_185 u37_189 u35_135 u36_156 u29_23 u18_191

end BorsukNine.FiniteObstruction

end OAI
