import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases127

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32699 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {1, 4, 7} → ¬ Q {0, 1, 3, 6} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  classical
  intro a311 a52 n130 n105 n109
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u2_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h a311 u0_24 hv
  have u4_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c28527 h a311 u0_24 a52 hv
  have u5_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28413 h a311 hv a52
  have u6_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28502 h a311 u5_12 u3_40 hv
  have u7_80 : T {2, 6, 7} := by
    by_contra hv
    exact c28504 h a311 u5_12 u3_40 hv
  have u8_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c2992 h hv u4_73 n105 n109
  have u9_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3422 h hv u4_73 n105 n109
  have u10_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3205 h hv u6_72 u2_116
  have u11_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2791 h hv u7_80 u2_116
  exact c31533 h h0 u8_129 u9_132 u11_128 u1_133 u10_131 n130

private theorem c32700 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 7} → ¬ T {1, 3, 6} → ¬ T {4, 6, 7} → T {5, 6, 8} → ¬ Q {0, 5, 8, 9} → False := by
  classical
  intro a52 n46 n105 a112 n200
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u2_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u3_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c686 h hv n46
  have u4_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c682 h hv n46
  have u5_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c678 h hv n46
  have u6_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u7_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u6_109 n105
  have u8_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u7_102 hv
  have u9_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u6_109 n105
  have u10_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u9_108 hv
  have u11_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u12_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32699 h h0 hv a52 u5_130 n105 u6_109
  have u13_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u11_116 n200 u12_311 hv
  have u14_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c32697 h h0 u12_311 hv u11_116 n200
  have u15_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1170 h u13_291 hv
  have u16_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c25613 h u13_291 hv a52
  have u17_87 : T {3, 4, 6} := by
    by_contra hv
    exact c25702 h u13_291 u16_18 n46 hv
  have u18_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c20719 h u14_256 u0_24 hv
  have u19_95 : T {3, 6, 7} := by
    by_contra hv
    exact c20804 h u14_256 u16_18 u18_67 hv
  have u20_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16889 h hv u15_78 a112 u11_116
  have u21_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3307 h hv u15_78 a112 u11_116
  have u22_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2861 h hv u15_78 a112 u11_116
  have u23_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c20709 h u14_256 hv u17_87
  have u24_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c20705 h u14_256 hv u19_95
  have u25_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv u23_13 u10_113
  have u26_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16504 h hv u23_13 u8_119
  have u27_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u24_10 u10_113
  have u28_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17342 h hv u24_10 u8_119
  have u29_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c651 h hv u22_128 u26_226 u4_227 u20_228 u25_229 u1_230
  have u30_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c647 h hv u22_128 u29_205 u26_226 u4_227 u20_228 u25_229 u1_230
  have u31_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c696 h hv u21_131 u20_228 u28_232 u3_235 u27_238 u2_239
  have u32_47 : T {1, 3, 7} := by
    by_contra hv
    exact c25668 h u13_291 u30_44 n46 hv
  exact c31315 h u27_238 u32_47 u2_239 u20_228 u28_232 u3_235 u31_208

private theorem c32701 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 6} → ¬ T {4, 6, 7} → T {5, 6, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro n46 n105 a112 n29
  have u0_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u3_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u2_109 n105
  have u4_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c32347 h h0 hv u3_102
  have u5_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u3_102
  have u6_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u3_102 hv
  have u7_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u2_109 n105
  have u8_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23047 h hv u1_24 u3_102 u7_108
  have u9_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16047 h hv u1_24 u3_102 u7_108
  have u10_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c32287 h h0 hv u7_108
  have u11_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv u7_108
  have u12_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u7_108 hv
  have u13_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 a112 hv u13_116
  have u15_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 a112 hv u13_116
  have u16_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c1563 h hv n105
  have u17_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31847 h h0 hv a112
  have u18_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u19_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c32700 h h0 hv n46 n105 a112 u18_200
  have u20_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c768 h hv u19_52
  have u21_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32698 h h0 u19_52 hv n46 n105 a112 u18_200
  have u22_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c26016 h hv n29 u21_57 u15_103
  have u23_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28816 h hv n29 u21_57 u15_103
  have u24_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27268 h hv n29 u21_57 u14_114
  have u25_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24468 h hv n29 u21_57 u14_114
  have u26_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10330 h hv u21_57 u15_103 u14_114
  have u27_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8230 h hv u21_57 u15_103 u14_114
  have u28_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c1217 h hv u27_166 u9_222 u8_272 u25_282 u10_288 u22_293 u4_294
  have u29_97 : ¬ T {3, 6, 9} := by
    intro hv
    exact c1442 h hv u26_181 u0_237 u8_272 u24_302 u11_308 u23_313 u5_314
  have u30_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8952 h hv u21_57 u28_82
  have u31_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6852 h hv u21_57 u29_97
  have u32_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c11032 h hv u28_82 u29_97 u6_119
  have u33_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11880 h hv u28_82 u29_97 u12_113
  exact c347 h u1_24 u20_136 u31_157 u30_172 u32_186 u16_189 u33_192 u17_193

private theorem c32702 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 7} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 3, 4} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  classical
  intro n52 n151 n152 n149 n105 n109
  have u0_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u1_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5932 h hv n52 n105 n109
  have u2_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6362 h hv n52 n105 n109
  exact c31534 h h0 u2_153 u1_150 n149 u0_154 n152 n151

theorem c32703 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → T {5, 6, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro n105 a112 n29
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c1565 h hv n105
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u7_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u2_109 n105
  have u8_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u2_109 n105
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 a112 hv u6_116
  have u10_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 a112 hv u6_116
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u9_103 hv
  have u12_46 : T {1, 3, 6} := by
    by_contra hv
    exact c32701 h h0 hv n105 a112 n29
  have u13_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25619 h hv u0_24 u12_46
  have u14_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7685 h hv u12_46 u7_108
  have u15_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8527 h hv u12_46 u8_102
  have u16_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u6_116 u3_200 hv u13_291
  have u17_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u16_311 hv
  have u18_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h u16_311 u0_24 hv
  have u19_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 u13_291 u3_200 hv u16_311
  have u20_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c596 h hv u18_40
  have u21_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h u19_256 hv
  have u22_58 : T {1, 5, 9} := by
    by_contra hv
    exact c870 h u19_256 hv
  have u23_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c20719 h u19_256 u0_24 hv
  have u24_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7231 h hv u21_57 u17_93 a112
  have u25_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8509 h hv u21_57 u17_93 a112
  have u26_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5801 h hv u21_57 a112 u6_116
  have u27_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6247 h hv u21_57 a112 u6_116
  have u28_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6015 h hv u22_58 u7_108
  have u29_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c1001 h hv u23_67
  have u30_52 : T {1, 4, 7} := by
    by_contra hv
    exact c32702 h h0 hv u28_151 u27_152 u26_149 n105 u2_109
  have u31_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8207 h hv u30_52 u8_102 u7_108
  have u32_130 : Q {0, 1, 3, 6} := by
    by_contra hv
    exact c32699 h h0 u16_311 u30_52 hv n105 u2_109
  have u33_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c214 h hv u1_154 u24_159 u14_163 u31_166 u25_168 u15_169
  have u34_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c31473 h u31_166 u24_159 u14_163 u33_127 u1_154 u15_169 hv
  have u35_5 : T {0, 1, 6} := by
    by_contra hv
    exact c65 h u32_130 hv
  have u36_18 : T {0, 3, 6} := by
    by_contra hv
    exact c258 h u32_130 hv
  have u37_75 : T {2, 4, 9} := by
    by_contra hv
    exact c3068 h u32_130 hv u10_114
  have u38_78 : T {2, 5, 8} := by
    by_contra hv
    exact c3072 h u32_130 hv u2_109
  have u39_79 : ¬ T {2, 5, 9} := by
    intro hv
    exact c3075 h u32_130 hv u7_108
  have u40_85 : ¬ T {2, 8, 9} := by
    intro hv
    exact c3081 h u32_130 hv u8_102
  have u41_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17768 h hv u34_15 u9_103
  have u42_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c32518 h h0 hv u35_5 u16_311
  have u43_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c32121 h h0 hv u36_18 u19_256
  have u44_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9937 h hv u21_57 u37_75
  have u45_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4895 h hv u37_75 u17_93
  have u46_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u21_57 u38_78 u17_93
  have u47_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20850 h hv u43_16 u39_79
  have u48_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27704 h hv u42_3 u40_85
  have u49_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20010 h hv u43_16 u40_85
  have u50_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28544 h hv u42_3 u39_79
  have u51_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c886 h hv u45_143 u20_220 u41_235 u4_245 u49_251 u47_257
  have u52_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1426 h hv u44_179 u41_235 u29_270 u5_300 u48_306 u50_312
  exact c31500 h h0 u51_258 u52_313 u11_118 u46_202

end BorsukNine.FiniteObstruction

end OAI
