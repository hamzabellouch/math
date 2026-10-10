import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases130

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32717 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → Q {0, 4, 7, 9} → ¬ T {0, 5, 8} → False := by
  classical
  intro a108 a193 n29
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u4_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u6_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32716 h h0 hv n29
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31703 h h0 hv u6_103 u5_112
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u9_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u8_105 hv
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 u9_116
  have u11_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14082 h hv n29 u6_103 u5_112
  have u12_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u6_103 hv
  have u13_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u5_112
  have u14_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14257 h hv u14_35 u13_109 u12_118
  have u16_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13827 h hv u14_35 u13_109 u12_118
  have u17_205 : Q {1, 2, 3, 4} := by
    by_contra hv
    exact c31535 h h0 u16_206 u15_209 u0_210 u10_207 u11_208 hv
  have u18_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c13575 h u17_205 hv u7_114
  have u19_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c495 h hv u18_33
  have u20_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u21_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c13571 h u17_205 hv u9_116
  have u22_95 : T {3, 6, 7} := by
    by_contra hv
    exact c32584 h h0 u21_31 hv u8_105 u20_200
  have u23_27 : T {0, 5, 6} := by
    by_contra hv
    exact c13592 h u17_205 hv u21_31 u18_33
  have u24_38 : T {1, 2, 4} := by
    by_contra hv
    exact c560 h u17_205 hv
  have u25_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15519 h hv u14_35 u13_109 u12_118
  have u26_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31752 h h0 hv u12_118 u13_109
  have u27_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c31330 h hv a193 u26_115
  have u28_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u29_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31756 h h0 hv u12_118 u13_109
  have u30_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31627 h h0 hv u29_120
  have u31_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u29_120
  have u32_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31637 h h0 hv u26_115
  have u33_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1719 h hv u26_115
  have u34_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u7_114
  have u35_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1672 h hv u5_112
  have u36_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 a108 hv
  have u37_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv a108
  have u38_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31668 h h0 hv a108 u13_109
  have u39_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31678 h h0 a108 hv u32_106
  have u40_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31744 h h0 hv a108 u7_114
  have u41_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31693 h h0 hv u36_113 u5_112
  have u42_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31737 h h0 hv u36_113 u34_107
  have u43_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31711 h h0 u36_113 u26_115 hv
  have u44_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16218 h hv u18_33 u34_107 u36_113
  have u45_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7968 h hv u2_49 u38_102
  have u46_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1644 h hv u39_110
  have u47_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c1747 h hv u40_117
  have u48_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22642 h hv u21_31 u8_105 u40_117
  have u49_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c13631 h u17_205 hv u41_111 u7_114
  have u50_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14945 h hv u22_95 u41_111 u12_118
  have u51_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10623 h hv u24_38 u41_111
  have u52_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16483 h hv u23_27 u30_101 u41_111
  have u53_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23483 h hv u23_27 u30_101 u41_111
  have u54_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2623 h hv u22_95 u41_111 u12_118
  have u55_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15915 h hv u28_26 u43_104 u13_109
  have u56_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24216 h hv u49_28 u2_49
  have u57_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c617 h hv u54_126 u15_209 u50_214 u25_218 u55_221 u44_223 u52_225
  have u58_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c1216 h hv u45_165 u55_221 u27_271 u56_281 u35_287 u47_292
  have u59_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9788 h hv u57_42 u8_105
  have u60_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26736 h hv u21_31 u57_42
  have u61_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u19_203 u58_294 hv u42_119
  have u62_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1411 h hv u59_178 u3_234 u48_269 u60_299 u37_308 u33_310
  exact c1499 h u61_314 u51_184 u4_240 u53_275 u46_305 u62_311 u31_315

theorem c32718 (h : TenSystem T Q) :
    ¬ Q {1, 3, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {0, 3, 6, 7} → False := by
  classical
  intro n235 n312 n270 a95 n306 n300 n179
  have u0_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1412 h a95 n179 n235 n270 n300 n306 n312 hv
  exact c1426 h u0_313 n179 n235 n270 n300 n306 n312

private theorem c32719 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → ¬ T {0, 5, 8} → False := by
  classical
  intro a193 n29
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u3_112
  have u5_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32716 h h0 hv n29
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u5_103 hv
  have u7_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31752 h h0 hv u6_118 u4_109
  have u8_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31637 h h0 hv u7_115
  have u9_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c1717 h hv u7_115
  have u10_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31756 h h0 hv u6_118 u4_109
  have u11_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14082 h hv n29 u5_103 u3_112
  have u12_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u13_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u12_105 hv
  have u14_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u13_116
  have u15_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv u12_105
  have u16_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1672 h hv u3_112
  have u17_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u18_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u19_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u20_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14257 h hv u19_35 u4_109 u6_118
  have u21_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13827 h hv u19_35 u4_109 u6_118
  have u22_205 : Q {1, 2, 3, 4} := by
    by_contra hv
    exact c31535 h h0 u21_206 u20_209 u1_210 u14_207 u11_208 hv
  have u23_38 : T {1, 2, 4} := by
    by_contra hv
    exact c560 h u22_205 hv
  have u24_44 : T {1, 3, 4} := by
    by_contra hv
    exact c650 h u22_205 hv
  have u25_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c13571 h u22_205 hv u13_116
  have u26_32 : T {0, 6, 8} := by
    by_contra hv
    exact c13572 h u22_205 hv u7_115
  have u27_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9923 h hv u23_38 u13_116
  have u28_95 : T {3, 6, 7} := by
    by_contra hv
    exact c32584 h h0 u25_31 hv u12_105 u17_200
  have u29_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c32717 h h0 hv a193 n29
  have u30_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u29_108 hv
  have u31_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7268 h hv u2_49 u29_108
  have u32_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31675 h h0 u29_108 hv u5_103
  have u33_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31747 h h0 hv u10_120 u29_108
  have u34_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31714 h h0 u30_113 hv u13_116
  have u35_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31742 h h0 hv u30_113 u6_118
  have u36_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c13649 h u22_205 hv u30_113 u13_116
  have u37_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c13577 h u22_205 hv u30_113
  have u38_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c32467 h h0 hv u32_110
  have u39_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c32267 h h0 hv u32_110
  have u40_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22215 h hv u18_26 u4_109 u32_110
  have u41_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15215 h hv u18_26 u4_109 u32_110
  have u42_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c32197 h h0 hv u33_117
  have u43_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7683 h hv u24_44 u33_117
  have u44_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22651 h hv u26_32 u8_106 u33_117
  have u45_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15651 h hv u26_32 u8_106 u33_117
  have u46_36 : T {0, 8, 9} := by
    by_contra hv
    exact c13698 h u22_205 hv u35_119 u10_120
  have u47_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23516 h hv u37_34 u2_49
  have u48_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u31_160 u41_216 u40_266 u47_276 u39_286 u16_287
  have u49_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1186 h hv u43_163 u45_219 u44_269 u42_279 u48_288 u9_290
  have u50_79 : ¬ T {2, 5, 9} := by
    intro hv
    exact c31342 h u48_288 u44_269 u49_291 u43_163 u9_290 hv u42_279
  have u51_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22799 h hv u46_36 u32_110 u13_116
  have u52_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17899 h hv u46_36 u32_110 u13_116
  have u53_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28678 h hv u36_30 u50_79 u34_104
  exact c32718 h u52_235 u53_312 u51_270 u28_95 u38_306 u15_300 u27_179

theorem c32720 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → False := by
  classical
  intro n29
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u3_112
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u5_105 hv
  have u7_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 u6_116
  have u8_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32716 h h0 hv n29
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31703 h h0 hv u8_103 u3_112
  have u10_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c32719 h h0 hv n29
  have u11_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u10_193 u4_109 hv u0_304
  have u12_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 u10_193 u4_109 hv
  have u13_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19848 h u11_249 n29 hv u3_112
  have u14_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h u12_284 hv
  have u15_46 : T {1, 3, 6} := by
    by_contra hv
    exact c24638 h u12_284 n29 hv
  have u16_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3073 h hv u13_78 u4_109
  have u17_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16749 h hv u13_78 u9_114 u6_116
  have u18_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17297 h hv u1_24 u14_73 u4_109
  have u19_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18005 h hv u1_24 u14_73 u4_109
  have u20_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c687 h hv u16_130 u7_207 u17_227 u18_231 u19_236 u2_237
  exact c677 h u15_46 u16_130 u7_207 u17_227 u18_231 u20_235 u19_236 u2_237

end BorsukNine.FiniteObstruction

end OAI
