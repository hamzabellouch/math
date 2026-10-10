import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates033
import OAI.Combinatorics.Ramsey.CycleClique.Certificates034
import OAI.Combinatorics.Ramsey.CycleClique.Certificates035
import OAI.Combinatorics.Ramsey.CycleClique.Certificates036
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_14_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[3,3]]]

theorem patterns_14_8_0_verified : ∀ D ∈ patterns_14_8_0, PatternVerified 14 8 D := by

  simp only [patterns_14_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1033, certificate_1033_valid⟩, ⟨⟨certificate_1034, certificate_1034_valid⟩, ⟨⟨certificate_1035, certificate_1035_valid⟩, ⟨⟨certificate_1036, certificate_1036_valid⟩, ⟨⟨certificate_1037, certificate_1037_valid⟩, ⟨⟨certificate_1038, certificate_1038_valid⟩, ⟨⟨certificate_1039, certificate_1039_valid⟩, ⟨⟨certificate_1040, certificate_1040_valid⟩, ⟨⟨certificate_1041, certificate_1041_valid⟩, ⟨⟨certificate_1042, certificate_1042_valid⟩, ⟨⟨certificate_1043, certificate_1043_valid⟩, ⟨⟨certificate_1044, certificate_1044_valid⟩, ⟨⟨certificate_1045, certificate_1045_valid⟩, ⟨⟨certificate_1046, certificate_1046_valid⟩, ⟨⟨certificate_1047, certificate_1047_valid⟩, ⟨⟨certificate_1048, certificate_1048_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_1 : List (List (List ℕ)) := [[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,4,1]],[[],[],[],[],[2],[2]]]

theorem patterns_14_8_1_verified : ∀ D ∈ patterns_14_8_1, PatternVerified 14 8 D := by

  simp only [patterns_14_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1049, certificate_1049_valid⟩, ⟨⟨certificate_1050, certificate_1050_valid⟩, ⟨⟨certificate_1051, certificate_1051_valid⟩, ⟨⟨certificate_1052, certificate_1052_valid⟩, ⟨⟨certificate_1053, certificate_1053_valid⟩, ⟨⟨certificate_1054, certificate_1054_valid⟩, ⟨⟨certificate_1055, certificate_1055_valid⟩, ⟨⟨certificate_1056, certificate_1056_valid⟩, ⟨⟨certificate_1057, certificate_1057_valid⟩, ⟨⟨certificate_1058, certificate_1058_valid⟩, ⟨⟨certificate_1059, certificate_1059_valid⟩, ⟨⟨certificate_1060, certificate_1060_valid⟩, ⟨⟨certificate_1061, certificate_1061_valid⟩, ⟨⟨certificate_1062, certificate_1062_valid⟩, ⟨⟨certificate_1063, certificate_1063_valid⟩, ⟨⟨certificate_1064, certificate_1064_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_2 : List (List (List ℕ)) := [[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,2,2]],[[],[],[],[],[3],[3]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1,1,1]]]

theorem patterns_14_8_2_verified : ∀ D ∈ patterns_14_8_2, PatternVerified 14 8 D := by

  simp only [patterns_14_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1065, certificate_1065_valid⟩, ⟨⟨certificate_1066, certificate_1066_valid⟩, ⟨⟨certificate_1067, certificate_1067_valid⟩, ⟨⟨certificate_1068, certificate_1068_valid⟩, ⟨⟨certificate_1069, certificate_1069_valid⟩, ⟨⟨certificate_1070, certificate_1070_valid⟩, ⟨⟨certificate_1071, certificate_1071_valid⟩, ⟨⟨certificate_1072, certificate_1072_valid⟩, ⟨⟨certificate_1073, certificate_1073_valid⟩, ⟨⟨certificate_1074, certificate_1074_valid⟩, ⟨⟨certificate_1075, certificate_1075_valid⟩, ⟨⟨certificate_1076, certificate_1076_valid⟩, ⟨⟨certificate_1077, certificate_1077_valid⟩, ⟨⟨certificate_1078, certificate_1078_valid⟩, ⟨⟨certificate_1079, certificate_1079_valid⟩, ⟨⟨certificate_1080, certificate_1080_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_3 : List (List (List ℕ)) := [[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,3,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2,1,2]],[[],[],[],[1,2,2,1]],[[],[],[],[1,3],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2,1,1,2]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]]]

theorem patterns_14_8_3_verified : ∀ D ∈ patterns_14_8_3, PatternVerified 14 8 D := by

  simp only [patterns_14_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1081, certificate_1081_valid⟩, ⟨⟨certificate_1082, certificate_1082_valid⟩, ⟨⟨certificate_1083, certificate_1083_valid⟩, ⟨⟨certificate_1084, certificate_1084_valid⟩, ⟨⟨certificate_1085, certificate_1085_valid⟩, ⟨⟨certificate_1086, certificate_1086_valid⟩, ⟨⟨certificate_1087, certificate_1087_valid⟩, ⟨⟨certificate_1088, certificate_1088_valid⟩, ⟨⟨certificate_1089, certificate_1089_valid⟩, ⟨⟨certificate_1090, certificate_1090_valid⟩, ⟨⟨certificate_1091, certificate_1091_valid⟩, ⟨⟨certificate_1092, certificate_1092_valid⟩, ⟨⟨certificate_1093, certificate_1093_valid⟩, ⟨⟨certificate_1094, certificate_1094_valid⟩, ⟨⟨certificate_1095, certificate_1095_valid⟩, ⟨⟨certificate_1096, certificate_1096_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_4 : List (List (List ℕ)) := [[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,3,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2,1,2]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[2,2]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1,1,1]]]

theorem patterns_14_8_4_verified : ∀ D ∈ patterns_14_8_4, PatternVerified 14 8 D := by

  simp only [patterns_14_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1097, certificate_1097_valid⟩, ⟨⟨certificate_1098, certificate_1098_valid⟩, ⟨⟨certificate_1099, certificate_1099_valid⟩, ⟨⟨certificate_1100, certificate_1100_valid⟩, ⟨⟨certificate_1101, certificate_1101_valid⟩, ⟨⟨certificate_1102, certificate_1102_valid⟩, ⟨⟨certificate_1103, certificate_1103_valid⟩, ⟨⟨certificate_1104, certificate_1104_valid⟩, ⟨⟨certificate_1105, certificate_1105_valid⟩, ⟨⟨certificate_1106, certificate_1106_valid⟩, ⟨⟨certificate_1107, certificate_1107_valid⟩, ⟨⟨certificate_1108, certificate_1108_valid⟩, ⟨⟨certificate_1109, certificate_1109_valid⟩, ⟨⟨certificate_1110, certificate_1110_valid⟩, ⟨⟨certificate_1111, certificate_1111_valid⟩, ⟨⟨certificate_1112, certificate_1112_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_5 : List (List (List ℕ)) := [[[],[],[1,1,1,1,2]],[[],[],[1,1,1,2,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2,1],[2]],[[],[],[2],[2],[2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[2,2]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,2,1]]]

theorem patterns_14_8_5_verified : ∀ D ∈ patterns_14_8_5, PatternVerified 14 8 D := by

  simp only [patterns_14_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1113, certificate_1113_valid⟩, ⟨⟨certificate_1114, certificate_1114_valid⟩, ⟨⟨certificate_1115, certificate_1115_valid⟩, ⟨⟨certificate_1116, certificate_1116_valid⟩, ⟨⟨certificate_1117, certificate_1117_valid⟩, ⟨⟨certificate_1118, certificate_1118_valid⟩, ⟨⟨certificate_1119, certificate_1119_valid⟩, ⟨⟨certificate_1120, certificate_1120_valid⟩, ⟨⟨certificate_1121, certificate_1121_valid⟩, ⟨⟨certificate_1122, certificate_1122_valid⟩, ⟨⟨certificate_1123, certificate_1123_valid⟩, ⟨⟨certificate_1124, certificate_1124_valid⟩, ⟨⟨certificate_1125, certificate_1125_valid⟩, ⟨⟨certificate_1126, certificate_1126_valid⟩, ⟨⟨certificate_1127, certificate_1127_valid⟩, ⟨⟨certificate_1128, certificate_1128_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_6 : List (List (List ℕ)) := [[[],[1],[1,2],[2]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,2,1]],[[],[1,1],[2],[2]],[[],[1,1,1],[1,2]],[[],[1,1,1,1],[2]],[[],[1,1,1,1,1,1]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,2,1]],[[1],[1],[2],[2]],[[1],[1,1],[1,1]]]

theorem patterns_14_8_6_verified : ∀ D ∈ patterns_14_8_6, PatternVerified 14 8 D := by

  simp only [patterns_14_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1129, certificate_1129_valid⟩, ⟨⟨certificate_1130, certificate_1130_valid⟩, ⟨⟨certificate_1131, certificate_1131_valid⟩, ⟨⟨certificate_1132, certificate_1132_valid⟩, ⟨⟨certificate_1133, certificate_1133_valid⟩, ⟨⟨certificate_1134, certificate_1134_valid⟩, ⟨⟨certificate_1135, certificate_1135_valid⟩, ⟨⟨certificate_1136, certificate_1136_valid⟩, ⟨⟨certificate_1137, certificate_1137_valid⟩, ⟨⟨certificate_1138, certificate_1138_valid⟩, ⟨⟨certificate_1139, certificate_1139_valid⟩, ⟨⟨certificate_1140, certificate_1140_valid⟩, ⟨⟨certificate_1141, certificate_1141_valid⟩, ⟨⟨certificate_1142, certificate_1142_valid⟩, ⟨⟨certificate_1143, certificate_1143_valid⟩, ⟨⟨certificate_1144, certificate_1144_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8_7 : List (List (List ℕ)) := [[[1],[1,1],[1,2]],[[1],[1,1,1],[2]],[[1],[1,1,1,1,1]],[[1,1],[1,1],[2]],[[1,1],[1,1,1,1]],[[1,1,1],[1,1,1]]]

theorem patterns_14_8_7_verified : ∀ D ∈ patterns_14_8_7, PatternVerified 14 8 D := by

  simp only [patterns_14_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1145, certificate_1145_valid⟩, ⟨⟨certificate_1146, certificate_1146_valid⟩, ⟨⟨certificate_1147, certificate_1147_valid⟩, ⟨⟨certificate_1148, certificate_1148_valid⟩, ⟨⟨certificate_1149, certificate_1149_valid⟩, ⟨⟨certificate_1150, certificate_1150_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_8 : List (List (List ℕ)) := patterns_14_8_0 ++ (patterns_14_8_1 ++ (patterns_14_8_2 ++ (patterns_14_8_3 ++ (patterns_14_8_4 ++ (patterns_14_8_5 ++ (patterns_14_8_6 ++ (patterns_14_8_7 ++ ([]))))))))

theorem patterns_14_8_verified : ∀ D ∈ patterns_14_8, PatternVerified 14 8 D := by

  simp only [patterns_14_8, List.forall_mem_append]

  exact ⟨patterns_14_8_0_verified, ⟨patterns_14_8_1_verified, ⟨patterns_14_8_2_verified, ⟨patterns_14_8_3_verified, ⟨patterns_14_8_4_verified, ⟨patterns_14_8_5_verified, ⟨patterns_14_8_6_verified, ⟨patterns_14_8_7_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_8_coverage : patternChoices 8 6 [] = patterns_14_8 := by decide +kernel

theorem finite_patterns_14_8 : ∀ D ∈ patternChoices 8 (14-8) [], PatternVerified 14 8 D := by

  rw [patterns_14_8_coverage]

  exact patterns_14_8_verified

end CycleClique

end OAI
