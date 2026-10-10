import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases143

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32816 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 9} → False := by
  classical
  intro n107
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u3_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u4_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u5_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u6_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u7_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u8_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c32788 h h0 hv
  have u9_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u10_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u11_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32745 h h0 hv
  have u13_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u14_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u15_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c1593 h hv n107
  have u16_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u17_118 : T {6, 7, 9} := by
    by_contra hv
    exact c32804 h h0 hv n107
  have u18_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31632 h h0 hv u17_118
  have u19_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31722 h h0 hv u5_105 u17_118
  have u20_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31705 h h0 u14_116 u18_103 hv
  have u21_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31645 h h0 hv u19_111
  have u22_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u20_112
  have u23_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv u0_29 u20_112 u16_114
  have u24_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c32813 h h0 hv n107
  have u25_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c1230 h hv u24_82
  have u26_119 : T {6, 8, 9} := by
    by_contra hv
    exact c32815 h h0 hv n107
  have u27_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31630 h h0 hv u26_119
  have u28_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31742 h h0 u26_119 hv u17_118
  have u29_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31764 h h0 hv u21_110 u26_119
  have u30_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31667 h h0 u27_102 hv u22_109
  have u31_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31647 h h0 u27_102 hv u18_103
  have u32_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1689 h hv u28_113
  have u33_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c1792 h hv u29_120
  have u34_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u29_120
  have u35_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22627 h hv u1_24 u5_105 u30_108
  have u36_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10583 h hv u4_51 u3_72 u31_101
  have u37_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23469 h hv u4_51 u31_101 u5_105
  have u38_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8627 h hv u4_51 u31_101 u5_105
  have u39_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32665 h h0 u35_269 hv u2_154 u10_274 u23_265 u37_275
  have u40_23 : T {0, 4, 6} := by
    by_contra hv
    exact c32814 h h0 hv u39_70 u16_114
  have u41_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28379 h hv u40_23 u4_51 u3_72
  have u42_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16467 h hv u40_23 u31_101 u5_105
  have u43_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c1405 h hv u8_178 u9_234 u35_269 u32_308 u41_310 u7_311
  have u44_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1484 h hv u36_183 u11_239 u10_274 u6_304 u41_310 u34_315
  have u45_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c1270 h hv u38_169 u42_225 u37_275 u12_291 u25_294 u33_295
  have u46_94 : ¬ T {3, 5, 9} := by
    intro hv
    exact c1397 h hv u8_178 u9_234 u35_269 u43_299 u32_308 u41_310 u7_311
  have u47_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c31288 h u41_310 u36_183 u34_315 u10_274 u44_313 hv u11_239
  have u48_85 : ¬ T {2, 8, 9} := by
    intro hv
    exact c1262 h hv u38_169 u42_225 u37_275 u45_285 u12_291 u25_294 u33_295
  have u49_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6786 h hv u13_49 u46_94 u47_99
  have u50_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11430 h hv u13_49 u39_70 u46_94
  have u51_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3846 h hv u39_70 u46_94 u47_99
  have u52_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10870 h hv u13_49 u39_70 u47_99
  have u53_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8940 h hv u48_85 u14_116 u29_120
  exact c31487 h u53_171 u52_185 u50_189 u51_135 u49_156 u40_23 u15_191

private theorem c32817 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → False := by
  classical
  intro a114
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  exact c31640 h h0 u0_107 a114

private theorem c32820 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → False := by
  classical
  intro a198
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  exact c31897 h h0 a198 u0_107

private theorem c32824 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 5, 8} → False := by
  classical
  intro a162
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c7639 h a162 u1_51 u2_105 u0_107

private theorem c32829 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 5, 8} → False := by
  classical
  intro a141
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  exact c4699 h a141 u2_72 u1_105 u0_107

theorem c32830 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 8} → False := by
  classical
  intro a153
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c6355 h a153 u1_51 u2_105 u0_107

theorem c32831 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 5} → False := by
  classical
  intro a150
  have u0_107 : T {4, 6, 9} := by
    by_contra hv
    exact c32816 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c5925 h a150 u1_51 u2_105 u0_107

private theorem c32833 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → False := by
  classical
  intro n103
  have u0_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c32817 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  exact c31707 h h0 u1_116 u0_114 n103

theorem c32851 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n196
  have u0_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c32824 h h0 hv
  have u1_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c32829 h h0 hv
  have u2_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u3_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32820 h h0 hv
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u5_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  exact c31443 h u2_177 u1_141 u5_29 u4_200 u0_162 u3_198 n196

private theorem c32853 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 9} → False := by
  classical
  intro a313
  have u0_103 : T {4, 5, 8} := by
    by_contra hv
    exact c32833 h h0 hv
  exact c32537 h h0 a313 u0_103

private theorem c32864 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 4, 7} → False := by
  classical
  intro n73
  have u0_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c12314 h u0_196 u1_49 n73

private theorem c32865 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro n187
  have u0_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  have u1_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32820 h h0 hv
  have u2_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c32829 h h0 hv
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u4_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u5_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c32824 h h0 hv
  exact c432 h u0_196 u2_141 u5_162 u4_177 n187 u1_198 u3_200

private theorem c32867 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 5} → False := by
  classical
  intro n22
  have u0_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c32865 h h0 hv
  exact c328 h u0_187 n22

private theorem c32868 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 8} → False := by
  classical
  intro n25
  have u0_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c32865 h h0 hv
  exact c369 h u0_187 n25

private theorem c32871 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 6, 9} → False := by
  classical
  intro a272
  have u0_25 : T {0, 4, 8} := by
    by_contra hv
    exact c32868 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_22 : T {0, 4, 5} := by
    by_contra hv
    exact c32867 h h0 hv
  exact c22977 h a272 u2_22 u1_24 u0_25

theorem c32873 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 3, 9} → False := by
  classical
  intro n70
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c32865 h h0 hv
  have u2_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  have u3_73 : T {2, 4, 7} := by
    by_contra hv
    exact c32864 h h0 hv
  have u4_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u5_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c32817 h h0 hv
  have u6_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c32871 h h0 hv
  have u7_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u8_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c32853 h h0 hv
  have u9_99 : T {3, 7, 9} := by
    by_contra hv
    exact c11152 h u1_187 u0_49 n70 hv
  have u10_52 : T {1, 4, 7} := by
    by_contra hv
    exact c12316 h u2_196 hv n70
  have u11_97 : T {3, 6, 9} := by
    by_contra hv
    exact c11150 h u1_187 u0_49 n70 hv
  have u12_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c12305 h u2_196 hv u9_99
  have u13_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28099 h hv u4_24 u10_52 u3_73
  have u14_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28947 h hv u4_24 u10_52 u3_73
  have u15_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10202 h hv u12_38 u5_114
  have u16_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1450 h hv u15_181 u7_237 u6_272 u13_308 u8_313 u14_314
  exact c1442 h u11_97 u15_181 u7_237 u6_272 u16_302 u13_308 u8_313 u14_314

theorem c32878 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 7} → False := by
  classical
  intro a68
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c32873 h h0 hv
  have u1_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  exact c31886 h h0 a68 u0_70 u1_196

end BorsukNine.FiniteObstruction

end OAI
