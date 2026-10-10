import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases133

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32729 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a235 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u3_116
  have u5_46 : T {1, 3, 6} := by
    by_contra hv
    exact c686 h a235 hv
  have u6_47 : T {1, 3, 7} := by
    by_contra hv
    exact c701 h a235 hv
  have u7_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c17763 h a235 hv u3_116
  have u8_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c17777 h a235 u2_29 hv
  have u9_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c17881 h a235 u2_29 hv u3_116
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c17883 h a235 u2_29 hv u3_116
  have u11_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25619 h hv u0_24 u5_46
  have u12_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31923 h h0 hv u5_46 u6_47
  have u13_71 : T {2, 4, 5} := by
    by_contra hv
    exact c17824 h a235 u7_10 hv u8_75
  have u14_74 : T {2, 4, 8} := by
    by_contra hv
    exact c17826 h a235 u7_10 hv u8_75
  have u15_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c1162 h hv u9_78
  have u16_26 : T {0, 4, 9} := by
    by_contra hv
    exact c17774 h a235 hv u9_78
  have u17_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u10_103
  have u18_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u10_103 hv
  have u19_15 : T {0, 2, 9} := by
    by_contra hv
    exact c17768 h a235 hv u10_103
  have u20_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u3_116 u12_200 hv u11_291
  have u21_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c17781 h a235 hv u13_71
  have u22_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c17779 h a235 hv u14_74
  have u23_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u2_29 u18_118
  have u24_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h u20_311 u0_24 hv
  have u25_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13720 h hv u21_36 n105
  have u26_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14134 h hv u22_30 n105
  have u27_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u24_40
  have u28_208 : Q {1, 2, 3, 7} := by
    by_contra hv
    exact c31535 h h0 u25_206 u26_209 u1_210 u4_207 hv u23_205
  have u29_41 : T {1, 2, 7} := by
    by_contra hv
    exact c605 h u28_208 hv
  have u30_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c13985 h u28_208 hv u3_116
  have u31_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c13993 h u28_208 u2_29 hv
  have u32_33 : T {0, 6, 9} := by
    by_contra hv
    exact c13998 h u28_208 hv u10_103
  have u33_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27859 h hv u16_26 u29_41
  have u34_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17578 h hv u30_23 n105 u31_107
  have u35_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28181 h hv u19_15 u16_26 u32_33
  exact c1396 h u20_311 u27_177 u34_233 u15_268 u17_298 u33_307 u35_309

theorem c32730 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 8, 9} → Q {0, 3, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro n200 a179 a116
  have u0_18 : T {0, 3, 6} := by
    by_contra hv
    exact c266 h a179 hv
  have u1_19 : T {0, 3, 7} := by
    by_contra hv
    exact c281 h a179 hv
  have u2_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32123 h h0 u1_19 u0_18 hv
  have u3_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32323 h h0 u1_19 u0_18 hv
  have u4_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 a116 n200 hv u3_291
  exact c31607 h h0 u3_291 n200 u2_256 u4_311

private theorem c32731 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 7, 9} → ¬ Q {1, 2, 3, 7} → ¬ T {3, 4, 6} → ¬ T {0, 4, 6} → ¬ Q {0, 1, 2, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 4, 7} → False := by
  classical
  intro a224 n208 n87 n23 n125 n220 n213
  have u0_101 : T {4, 5, 6} := by
    by_contra hv
    exact c16322 h a224 n23 n87 hv
  have u1_106 : T {4, 6, 8} := by
    by_contra hv
    exact c16324 h a224 n23 n87 hv
  have u2_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c16225 h a224 hv u1_106
  have u3_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c16229 h a224 hv u0_101
  have u4_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31660 h h0 u0_101 u1_106 hv
  have u5_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16084 h hv u2_17 u4_107
  have u6_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15246 h hv u3_20 u4_107
  exact c616 h a224 n125 n208 n213 u6_217 n220 u5_223

theorem c32732 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 6, 7} → T {3, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a179 a95 a116
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u1_29 a95
  have u4_18 : T {0, 3, 6} := by
    by_contra hv
    exact c266 h a179 hv
  have u5_19 : T {0, 3, 7} := by
    by_contra hv
    exact c281 h a179 hv
  have u6_31 : T {0, 6, 7} := by
    by_contra hv
    exact c457 h a179 hv
  have u7_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c9923 h a179 hv a116
  have u8_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14685 h hv u4_18 a116
  have u9_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32323 h h0 u5_19 u4_18 hv
  have u10_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32123 h h0 u5_19 u4_18 hv
  have u11_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16417 h hv u5_19 u0_24 u6_31
  have u12_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15567 h hv u5_19 u0_24 u6_31
  have u13_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32730 h h0 hv a179 a116
  have u14_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31604 h h0 u13_200 u9_291 u10_256 hv
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u14_311 hv
  have u16_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h u14_311 u0_24 hv
  have u17_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28459 h u14_311 hv u0_24 u6_31
  have u18_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28461 h u14_311 hv u0_24 u6_31
  have u19_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15953 h hv u0_24 u15_93
  have u20_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15781 h hv u1_29 u15_93 a116
  have u21_41 : T {1, 2, 7} := by
    by_contra hv
    exact c12888 h u13_200 u7_38 u16_40 hv
  have u22_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12866 h u13_200 u16_40 hv
  have u23_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c78 h hv u17_6
  have u24_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c80 h hv u17_6
  have u25_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c185 h hv u18_13
  have u26_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28417 h u14_311 hv u21_41
  have u27_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c12869 h u13_200 u21_41 hv
  have u28_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c12975 h u13_200 hv u22_88 a95
  have u29_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c695 h hv u28_47
  have u30_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c32731 h h0 hv u29_208 u27_87 u26_23 u23_125 u20_220 u8_213
  have u31_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c31390 h u19_222 hv u11_225 u30_224 u3_215 u2_210 u12_219
  have u32_103 : T {4, 5, 8} := by
    by_contra hv
    exact c9928 h a179 u31_43 hv
  have u33_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9524 h hv u7_38 u16_40 u31_43
  have u34_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10366 h hv u7_38 u16_40 u31_43
  have u35_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31706 h h0 hv u32_103 a116
  have u36_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10482 h hv u7_38 u35_112
  have u37_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8948 h hv u31_43 u35_112
  exact c282 h a179 u24_131 u25_152 u37_172 u33_176 u34_182 u36_183

theorem c32733 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a270 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u3_116
  have u5_67 : T {2, 3, 6} := by
    by_contra hv
    exact c1001 h a270 hv
  have u6_68 : T {2, 3, 7} := by
    by_contra hv
    exact c1016 h a270 hv
  have u7_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c22663 h a270 hv u3_116
  have u8_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c22677 h a270 u2_29 hv
  have u9_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c22781 h a270 u2_29 hv u3_116
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c22783 h a270 u2_29 hv u3_116
  have u11_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20719 h hv u0_24 u5_67
  have u12_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31926 h h0 hv u5_67 u6_68
  have u13_50 : T {1, 4, 5} := by
    by_contra hv
    exact c22724 h a270 u7_3 hv u8_54
  have u14_53 : T {1, 4, 8} := by
    by_contra hv
    exact c22726 h a270 u7_3 hv u8_54
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c847 h hv u9_57
  have u16_26 : T {0, 4, 9} := by
    by_contra hv
    exact c22674 h a270 hv u9_57
  have u17_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u10_103
  have u18_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u10_103 hv
  have u19_8 : T {0, 1, 9} := by
    by_contra hv
    exact c22668 h a270 hv u10_103
  have u20_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32697 h h0 hv u11_256 u3_116 u12_200
  have u21_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c22681 h a270 hv u13_50
  have u22_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c22679 h a270 hv u14_53
  have u23_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u2_29 u18_118
  have u24_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h u20_311 u0_24 hv
  have u25_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13720 h hv u21_36 n105
  have u26_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14134 h hv u22_30 n105
  have u27_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u24_40
  have u28_208 : Q {1, 2, 3, 7} := by
    by_contra hv
    exact c31535 h h0 u25_206 u26_209 u1_210 u4_207 hv u23_205
  have u29_41 : T {1, 2, 7} := by
    by_contra hv
    exact c605 h u28_208 hv
  have u30_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c13985 h u28_208 hv u3_116
  have u31_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c13993 h u28_208 u2_29 hv
  have u32_33 : T {0, 6, 9} := by
    by_contra hv
    exact c13998 h u28_208 hv u10_103
  have u33_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27859 h hv u16_26 u29_41
  have u34_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22478 h hv u30_23 n105 u31_107
  have u35_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28179 h hv u19_8 u16_26 u32_33
  exact c1396 h u20_311 u27_177 u15_233 u34_268 u17_298 u33_307 u35_309

theorem c32735 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → Q {3, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro a256 a311 n200 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h a311 u1_24 hv
  have u4_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c32733 h h0 hv n105
  have u5_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c32729 h h0 hv n105
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u7_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c32730 h h0 n200 hv u6_116
  have u8_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32728 h h0 u5_235 u7_179 u4_270 hv n105
  have u9_31 : T {0, 6, 7} := by
    by_contra hv
    exact c32584 h h0 hv u8_95 n105 n200
  have u10_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28421 h a311 u9_31 hv
  have u11_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28468 h a311 u10_38 u3_40 hv
  have u12_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28417 h a311 hv u11_41
  have u13_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28461 h a311 hv u1_24 u9_31
  have u14_51 : T {1, 4, 6} := by
    by_contra hv
    exact c28414 h a311 u13_13 hv
  have u15_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28459 h a311 hv u1_24 u9_31
  have u16_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28408 h a311 u15_6 hv
  have u17_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u3_40
  have u18_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u19_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c20719 h a256 u1_24 hv
  have u20_87 : T {3, 4, 6} := by
    by_contra hv
    exact c20808 h a256 u19_67 hv u8_95
  have u21_10 : T {0, 2, 4} := by
    by_contra hv
    exact c20704 h a256 hv u8_95
  have u22_80 : T {2, 6, 7} := by
    by_contra hv
    exact c20840 h a256 hv u8_95 n105
  have u23_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20721 h a256 u9_31 hv
  have u24_68 : T {2, 3, 7} := by
    by_contra hv
    exact c20716 h a256 u12_23 hv
  have u25_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12699 h hv u14_51 u16_72 u20_87
  have u26_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c28499 h a311 u21_10 u16_72 hv
  have u27_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11119 h hv u11_41 u24_68 u22_80
  have u28_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12370 h hv u10_38 u23_65 u26_73
  have u29_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c32585 h u25_198 u18_162 hv u2_29 n200 u27_187 u28_196
  exact c424 h u29_141 u18_162 u17_177 u27_187 u28_196 u25_198 n200

end BorsukNine.FiniteObstruction

end OAI
