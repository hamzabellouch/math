import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates036
import OAI.Combinatorics.Ramsey.CycleClique.Certificates037
import OAI.Combinatorics.Ramsey.CycleClique.Certificates038
import OAI.Combinatorics.Ramsey.CycleClique.Certificates039
import OAI.Combinatorics.Ramsey.CycleClique.Certificates040
import OAI.Combinatorics.Ramsey.CycleClique.Certificates041
import OAI.Combinatorics.Ramsey.CycleClique.Certificates042
import OAI.Combinatorics.Ramsey.CycleClique.Certificates043
import OAI.Combinatorics.Ramsey.CycleClique.Certificates044
import OAI.Combinatorics.Ramsey.CycleClique.Certificates045
import OAI.Combinatorics.Ramsey.CycleClique.Certificates046
import OAI.Combinatorics.Ramsey.CycleClique.Certificates047
import OAI.Combinatorics.Ramsey.CycleClique.Certificates048
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

noncomputable def patterns_15_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[],[7]],[[],[],[],[],[],[8]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[1,6]],[[],[],[],[],[1,7]]]

theorem patterns_15_7_0_verified : ∀ D ∈ patterns_15_7_0, PatternVerified 15 7 D := by

  simp only [patterns_15_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1151, certificate_1151_valid⟩, ⟨⟨certificate_1152, certificate_1152_valid⟩, ⟨⟨certificate_1153, certificate_1153_valid⟩, ⟨⟨certificate_1154, certificate_1154_valid⟩, ⟨⟨certificate_1155, certificate_1155_valid⟩, ⟨⟨certificate_1156, certificate_1156_valid⟩, ⟨⟨certificate_1157, certificate_1157_valid⟩, ⟨⟨certificate_1158, certificate_1158_valid⟩, ⟨⟨certificate_1159, certificate_1159_valid⟩, ⟨⟨certificate_1160, certificate_1160_valid⟩, ⟨⟨certificate_1161, certificate_1161_valid⟩, ⟨⟨certificate_1162, certificate_1162_valid⟩, ⟨⟨certificate_1163, certificate_1163_valid⟩, ⟨⟨certificate_1164, certificate_1164_valid⟩, ⟨⟨certificate_1165, certificate_1165_valid⟩, ⟨⟨certificate_1166, certificate_1166_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_1 : List (List (List ℕ)) := [[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[],[2,4]],[[],[],[],[],[2,5]],[[],[],[],[],[2,6]],[[],[],[],[],[3,3]],[[],[],[],[],[3,4]],[[],[],[],[],[3,5]],[[],[],[],[],[4,4]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1],[6]],[[],[],[],[1],[7]]]

theorem patterns_15_7_1_verified : ∀ D ∈ patterns_15_7_1, PatternVerified 15 7 D := by

  simp only [patterns_15_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1167, certificate_1167_valid⟩, ⟨⟨certificate_1168, certificate_1168_valid⟩, ⟨⟨certificate_1169, certificate_1169_valid⟩, ⟨⟨certificate_1170, certificate_1170_valid⟩, ⟨⟨certificate_1171, certificate_1171_valid⟩, ⟨⟨certificate_1172, certificate_1172_valid⟩, ⟨⟨certificate_1173, certificate_1173_valid⟩, ⟨⟨certificate_1174, certificate_1174_valid⟩, ⟨⟨certificate_1175, certificate_1175_valid⟩, ⟨⟨certificate_1176, certificate_1176_valid⟩, ⟨⟨certificate_1177, certificate_1177_valid⟩, ⟨⟨certificate_1178, certificate_1178_valid⟩, ⟨⟨certificate_1179, certificate_1179_valid⟩, ⟨⟨certificate_1180, certificate_1180_valid⟩, ⟨⟨certificate_1181, certificate_1181_valid⟩, ⟨⟨certificate_1182, certificate_1182_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_2 : List (List (List ℕ)) := [[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,1,5]],[[],[],[],[1,1,6]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,2,4]],[[],[],[],[1,2,5]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,3,3]],[[],[],[],[1,3,4]],[[],[],[],[1,4,1]]]

theorem patterns_15_7_2_verified : ∀ D ∈ patterns_15_7_2, PatternVerified 15 7 D := by

  simp only [patterns_15_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1183, certificate_1183_valid⟩, ⟨⟨certificate_1184, certificate_1184_valid⟩, ⟨⟨certificate_1185, certificate_1185_valid⟩, ⟨⟨certificate_1186, certificate_1186_valid⟩, ⟨⟨certificate_1187, certificate_1187_valid⟩, ⟨⟨certificate_1188, certificate_1188_valid⟩, ⟨⟨certificate_1189, certificate_1189_valid⟩, ⟨⟨certificate_1190, certificate_1190_valid⟩, ⟨⟨certificate_1191, certificate_1191_valid⟩, ⟨⟨certificate_1192, certificate_1192_valid⟩, ⟨⟨certificate_1193, certificate_1193_valid⟩, ⟨⟨certificate_1194, certificate_1194_valid⟩, ⟨⟨certificate_1195, certificate_1195_valid⟩, ⟨⟨certificate_1196, certificate_1196_valid⟩, ⟨⟨certificate_1197, certificate_1197_valid⟩, ⟨⟨certificate_1198, certificate_1198_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_3 : List (List (List ℕ)) := [[[],[],[],[1,4,2]],[[],[],[],[1,4,3]],[[],[],[],[1,5,1]],[[],[],[],[1,5,2]],[[],[],[],[1,6,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2],[5]],[[],[],[],[2],[6]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,1,4]],[[],[],[],[2,1,5]],[[],[],[],[2,2,2]],[[],[],[],[2,2,3]]]

theorem patterns_15_7_3_verified : ∀ D ∈ patterns_15_7_3, PatternVerified 15 7 D := by

  simp only [patterns_15_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1199, certificate_1199_valid⟩, ⟨⟨certificate_1200, certificate_1200_valid⟩, ⟨⟨certificate_1201, certificate_1201_valid⟩, ⟨⟨certificate_1202, certificate_1202_valid⟩, ⟨⟨certificate_1203, certificate_1203_valid⟩, ⟨⟨certificate_1204, certificate_1204_valid⟩, ⟨⟨certificate_1205, certificate_1205_valid⟩, ⟨⟨certificate_1206, certificate_1206_valid⟩, ⟨⟨certificate_1207, certificate_1207_valid⟩, ⟨⟨certificate_1208, certificate_1208_valid⟩, ⟨⟨certificate_1209, certificate_1209_valid⟩, ⟨⟨certificate_1210, certificate_1210_valid⟩, ⟨⟨certificate_1211, certificate_1211_valid⟩, ⟨⟨certificate_1212, certificate_1212_valid⟩, ⟨⟨certificate_1213, certificate_1213_valid⟩, ⟨⟨certificate_1214, certificate_1214_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_4 : List (List (List ℕ)) := [[[],[],[],[2,2,4]],[[],[],[],[2,3,2]],[[],[],[],[2,3,3]],[[],[],[],[2,4,2]],[[],[],[],[3],[3]],[[],[],[],[3],[4]],[[],[],[],[3],[5]],[[],[],[],[3,1,3]],[[],[],[],[3,1,4]],[[],[],[],[3,2,3]],[[],[],[],[4],[4]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[1,5]]]

theorem patterns_15_7_4_verified : ∀ D ∈ patterns_15_7_4, PatternVerified 15 7 D := by

  simp only [patterns_15_7_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1215, certificate_1215_valid⟩, ⟨⟨certificate_1216, certificate_1216_valid⟩, ⟨⟨certificate_1217, certificate_1217_valid⟩, ⟨⟨certificate_1218, certificate_1218_valid⟩, ⟨⟨certificate_1219, certificate_1219_valid⟩, ⟨⟨certificate_1220, certificate_1220_valid⟩, ⟨⟨certificate_1221, certificate_1221_valid⟩, ⟨⟨certificate_1222, certificate_1222_valid⟩, ⟨⟨certificate_1223, certificate_1223_valid⟩, ⟨⟨certificate_1224, certificate_1224_valid⟩, ⟨⟨certificate_1225, certificate_1225_valid⟩, ⟨⟨certificate_1226, certificate_1226_valid⟩, ⟨⟨certificate_1227, certificate_1227_valid⟩, ⟨⟨certificate_1228, certificate_1228_valid⟩, ⟨⟨certificate_1229, certificate_1229_valid⟩, ⟨⟨certificate_1230, certificate_1230_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_5 : List (List (List ℕ)) := [[[],[],[1],[1,6]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1],[2,4]],[[],[],[1],[2,5]],[[],[],[1],[3,3]],[[],[],[1],[3,4]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1],[5]],[[],[],[1,1],[6]],[[],[],[1,1,1,1]],[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,1,4]]]

theorem patterns_15_7_5_verified : ∀ D ∈ patterns_15_7_5, PatternVerified 15 7 D := by

  simp only [patterns_15_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1231, certificate_1231_valid⟩, ⟨⟨certificate_1232, certificate_1232_valid⟩, ⟨⟨certificate_1233, certificate_1233_valid⟩, ⟨⟨certificate_1234, certificate_1234_valid⟩, ⟨⟨certificate_1235, certificate_1235_valid⟩, ⟨⟨certificate_1236, certificate_1236_valid⟩, ⟨⟨certificate_1237, certificate_1237_valid⟩, ⟨⟨certificate_1238, certificate_1238_valid⟩, ⟨⟨certificate_1239, certificate_1239_valid⟩, ⟨⟨certificate_1240, certificate_1240_valid⟩, ⟨⟨certificate_1241, certificate_1241_valid⟩, ⟨⟨certificate_1242, certificate_1242_valid⟩, ⟨⟨certificate_1243, certificate_1243_valid⟩, ⟨⟨certificate_1244, certificate_1244_valid⟩, ⟨⟨certificate_1245, certificate_1245_valid⟩, ⟨⟨certificate_1246, certificate_1246_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_6 : List (List (List ℕ)) := [[[],[],[1,1,1,5]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,2,3]],[[],[],[1,1,2,4]],[[],[],[1,1,3,1]],[[],[],[1,1,3,2]],[[],[],[1,1,3,3]],[[],[],[1,1,4,1]],[[],[],[1,1,4,2]],[[],[],[1,1,5,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2],[4]],[[],[],[1,2],[5]],[[],[],[1,2,1,2]]]

theorem patterns_15_7_6_verified : ∀ D ∈ patterns_15_7_6, PatternVerified 15 7 D := by

  simp only [patterns_15_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1247, certificate_1247_valid⟩, ⟨⟨certificate_1248, certificate_1248_valid⟩, ⟨⟨certificate_1249, certificate_1249_valid⟩, ⟨⟨certificate_1250, certificate_1250_valid⟩, ⟨⟨certificate_1251, certificate_1251_valid⟩, ⟨⟨certificate_1252, certificate_1252_valid⟩, ⟨⟨certificate_1253, certificate_1253_valid⟩, ⟨⟨certificate_1254, certificate_1254_valid⟩, ⟨⟨certificate_1255, certificate_1255_valid⟩, ⟨⟨certificate_1256, certificate_1256_valid⟩, ⟨⟨certificate_1257, certificate_1257_valid⟩, ⟨⟨certificate_1258, certificate_1258_valid⟩, ⟨⟨certificate_1259, certificate_1259_valid⟩, ⟨⟨certificate_1260, certificate_1260_valid⟩, ⟨⟨certificate_1261, certificate_1261_valid⟩, ⟨⟨certificate_1262, certificate_1262_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_7 : List (List (List ℕ)) := [[[],[],[1,2,1,3]],[[],[],[1,2,1,4]],[[],[],[1,2,2,1]],[[],[],[1,2,2,2]],[[],[],[1,2,2,3]],[[],[],[1,2,3,1]],[[],[],[1,2,3,2]],[[],[],[1,2,4,1]],[[],[],[1,3],[2]],[[],[],[1,3],[3]],[[],[],[1,3],[4]],[[],[],[1,3,1,2]],[[],[],[1,3,1,3]],[[],[],[1,3,2,2]],[[],[],[1,3,3,1]],[[],[],[1,4],[2]]]

theorem patterns_15_7_7_verified : ∀ D ∈ patterns_15_7_7, PatternVerified 15 7 D := by

  simp only [patterns_15_7_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1263, certificate_1263_valid⟩, ⟨⟨certificate_1264, certificate_1264_valid⟩, ⟨⟨certificate_1265, certificate_1265_valid⟩, ⟨⟨certificate_1266, certificate_1266_valid⟩, ⟨⟨certificate_1267, certificate_1267_valid⟩, ⟨⟨certificate_1268, certificate_1268_valid⟩, ⟨⟨certificate_1269, certificate_1269_valid⟩, ⟨⟨certificate_1270, certificate_1270_valid⟩, ⟨⟨certificate_1271, certificate_1271_valid⟩, ⟨⟨certificate_1272, certificate_1272_valid⟩, ⟨⟨certificate_1273, certificate_1273_valid⟩, ⟨⟨certificate_1274, certificate_1274_valid⟩, ⟨⟨certificate_1275, certificate_1275_valid⟩, ⟨⟨certificate_1276, certificate_1276_valid⟩, ⟨⟨certificate_1277, certificate_1277_valid⟩, ⟨⟨certificate_1278, certificate_1278_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_8 : List (List (List ℕ)) := [[[],[],[1,4],[3]],[[],[],[1,4,1,2]],[[],[],[1,5],[2]],[[],[],[2],[2,2]],[[],[],[2],[2,3]],[[],[],[2],[2,4]],[[],[],[2],[3,3]],[[],[],[2,1,1,2]],[[],[],[2,1,1,3]],[[],[],[2,1,1,4]],[[],[],[2,1,2,2]],[[],[],[2,1,2,3]],[[],[],[2,1,3,2]],[[],[],[2,2],[3]],[[],[],[2,2],[4]],[[],[],[2,2,1,3]]]

theorem patterns_15_7_8_verified : ∀ D ∈ patterns_15_7_8, PatternVerified 15 7 D := by

  simp only [patterns_15_7_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1279, certificate_1279_valid⟩, ⟨⟨certificate_1280, certificate_1280_valid⟩, ⟨⟨certificate_1281, certificate_1281_valid⟩, ⟨⟨certificate_1282, certificate_1282_valid⟩, ⟨⟨certificate_1283, certificate_1283_valid⟩, ⟨⟨certificate_1284, certificate_1284_valid⟩, ⟨⟨certificate_1285, certificate_1285_valid⟩, ⟨⟨certificate_1286, certificate_1286_valid⟩, ⟨⟨certificate_1287, certificate_1287_valid⟩, ⟨⟨certificate_1288, certificate_1288_valid⟩, ⟨⟨certificate_1289, certificate_1289_valid⟩, ⟨⟨certificate_1290, certificate_1290_valid⟩, ⟨⟨certificate_1291, certificate_1291_valid⟩, ⟨⟨certificate_1292, certificate_1292_valid⟩, ⟨⟨certificate_1293, certificate_1293_valid⟩, ⟨⟨certificate_1294, certificate_1294_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_9 : List (List (List ℕ)) := [[[],[],[2,2,2,2]],[[],[],[2,3],[3]],[[],[],[3,1,1,3]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]],[[],[1],[1],[5]],[[],[1],[1],[6]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,1,4]],[[],[1],[1,1,5]],[[],[1],[1,2,1]],[[],[1],[1,2,2]]]

theorem patterns_15_7_9_verified : ∀ D ∈ patterns_15_7_9, PatternVerified 15 7 D := by

  simp only [patterns_15_7_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1295, certificate_1295_valid⟩, ⟨⟨certificate_1296, certificate_1296_valid⟩, ⟨⟨certificate_1297, certificate_1297_valid⟩, ⟨⟨certificate_1298, certificate_1298_valid⟩, ⟨⟨certificate_1299, certificate_1299_valid⟩, ⟨⟨certificate_1300, certificate_1300_valid⟩, ⟨⟨certificate_1301, certificate_1301_valid⟩, ⟨⟨certificate_1302, certificate_1302_valid⟩, ⟨⟨certificate_1303, certificate_1303_valid⟩, ⟨⟨certificate_1304, certificate_1304_valid⟩, ⟨⟨certificate_1305, certificate_1305_valid⟩, ⟨⟨certificate_1306, certificate_1306_valid⟩, ⟨⟨certificate_1307, certificate_1307_valid⟩, ⟨⟨certificate_1308, certificate_1308_valid⟩, ⟨⟨certificate_1309, certificate_1309_valid⟩, ⟨⟨certificate_1310, certificate_1310_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_10 : List (List (List ℕ)) := [[[],[1],[1,2,3]],[[],[1],[1,2,4]],[[],[1],[1,3,1]],[[],[1],[1,3,2]],[[],[1],[1,3,3]],[[],[1],[1,4,1]],[[],[1],[1,4,2]],[[],[1],[1,5,1]],[[],[1],[2],[2]],[[],[1],[2],[3]],[[],[1],[2],[4]],[[],[1],[2],[5]],[[],[1],[2,1,2]],[[],[1],[2,1,3]],[[],[1],[2,1,4]],[[],[1],[2,2,2]]]

theorem patterns_15_7_10_verified : ∀ D ∈ patterns_15_7_10, PatternVerified 15 7 D := by

  simp only [patterns_15_7_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1311, certificate_1311_valid⟩, ⟨⟨certificate_1312, certificate_1312_valid⟩, ⟨⟨certificate_1313, certificate_1313_valid⟩, ⟨⟨certificate_1314, certificate_1314_valid⟩, ⟨⟨certificate_1315, certificate_1315_valid⟩, ⟨⟨certificate_1316, certificate_1316_valid⟩, ⟨⟨certificate_1317, certificate_1317_valid⟩, ⟨⟨certificate_1318, certificate_1318_valid⟩, ⟨⟨certificate_1319, certificate_1319_valid⟩, ⟨⟨certificate_1320, certificate_1320_valid⟩, ⟨⟨certificate_1321, certificate_1321_valid⟩, ⟨⟨certificate_1322, certificate_1322_valid⟩, ⟨⟨certificate_1323, certificate_1323_valid⟩, ⟨⟨certificate_1324, certificate_1324_valid⟩, ⟨⟨certificate_1325, certificate_1325_valid⟩, ⟨⟨certificate_1326, certificate_1326_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_11 : List (List (List ℕ)) := [[[],[1],[2,2,3]],[[],[1],[2,3,2]],[[],[1],[3],[3]],[[],[1],[3],[4]],[[],[1],[3,1,3]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[1,4]],[[],[1,1],[1,5]],[[],[1,1],[2,2]],[[],[1,1],[2,3]],[[],[1,1],[2,4]],[[],[1,1],[3,3]],[[],[1,1,1],[2]],[[],[1,1,1],[3]]]

theorem patterns_15_7_11_verified : ∀ D ∈ patterns_15_7_11, PatternVerified 15 7 D := by

  simp only [patterns_15_7_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1327, certificate_1327_valid⟩, ⟨⟨certificate_1328, certificate_1328_valid⟩, ⟨⟨certificate_1329, certificate_1329_valid⟩, ⟨⟨certificate_1330, certificate_1330_valid⟩, ⟨⟨certificate_1331, certificate_1331_valid⟩, ⟨⟨certificate_1332, certificate_1332_valid⟩, ⟨⟨certificate_1333, certificate_1333_valid⟩, ⟨⟨certificate_1334, certificate_1334_valid⟩, ⟨⟨certificate_1335, certificate_1335_valid⟩, ⟨⟨certificate_1336, certificate_1336_valid⟩, ⟨⟨certificate_1337, certificate_1337_valid⟩, ⟨⟨certificate_1338, certificate_1338_valid⟩, ⟨⟨certificate_1339, certificate_1339_valid⟩, ⟨⟨certificate_1340, certificate_1340_valid⟩, ⟨⟨certificate_1341, certificate_1341_valid⟩, ⟨⟨certificate_1342, certificate_1342_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_12 : List (List (List ℕ)) := [[[],[1,1,1],[4]],[[],[1,1,1],[5]],[[],[1,1,1,1,1]],[[],[1,1,1,1,2]],[[],[1,1,1,1,3]],[[],[1,1,1,1,4]],[[],[1,1,1,2,1]],[[],[1,1,1,2,2]],[[],[1,1,1,2,3]],[[],[1,1,1,3,1]],[[],[1,1,1,3,2]],[[],[1,1,1,4,1]],[[],[1,1,2],[2]],[[],[1,1,2],[3]],[[],[1,1,2],[4]],[[],[1,1,2,1,1]]]

theorem patterns_15_7_12_verified : ∀ D ∈ patterns_15_7_12, PatternVerified 15 7 D := by

  simp only [patterns_15_7_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1343, certificate_1343_valid⟩, ⟨⟨certificate_1344, certificate_1344_valid⟩, ⟨⟨certificate_1345, certificate_1345_valid⟩, ⟨⟨certificate_1346, certificate_1346_valid⟩, ⟨⟨certificate_1347, certificate_1347_valid⟩, ⟨⟨certificate_1348, certificate_1348_valid⟩, ⟨⟨certificate_1349, certificate_1349_valid⟩, ⟨⟨certificate_1350, certificate_1350_valid⟩, ⟨⟨certificate_1351, certificate_1351_valid⟩, ⟨⟨certificate_1352, certificate_1352_valid⟩, ⟨⟨certificate_1353, certificate_1353_valid⟩, ⟨⟨certificate_1354, certificate_1354_valid⟩, ⟨⟨certificate_1355, certificate_1355_valid⟩, ⟨⟨certificate_1356, certificate_1356_valid⟩, ⟨⟨certificate_1357, certificate_1357_valid⟩, ⟨⟨certificate_1358, certificate_1358_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_13 : List (List (List ℕ)) := [[[],[1,1,2,1,2]],[[],[1,1,2,1,3]],[[],[1,1,2,2,1]],[[],[1,1,2,2,2]],[[],[1,1,2,3,1]],[[],[1,1,3],[2]],[[],[1,1,3],[3]],[[],[1,1,3,1,1]],[[],[1,1,3,1,2]],[[],[1,1,3,2,1]],[[],[1,1,4],[2]],[[],[1,1,4,1,1]],[[],[1,2],[1,2]],[[],[1,2],[1,3]],[[],[1,2],[1,4]],[[],[1,2],[2,2]]]

theorem patterns_15_7_13_verified : ∀ D ∈ patterns_15_7_13, PatternVerified 15 7 D := by

  simp only [patterns_15_7_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1359, certificate_1359_valid⟩, ⟨⟨certificate_1360, certificate_1360_valid⟩, ⟨⟨certificate_1361, certificate_1361_valid⟩, ⟨⟨certificate_1362, certificate_1362_valid⟩, ⟨⟨certificate_1363, certificate_1363_valid⟩, ⟨⟨certificate_1364, certificate_1364_valid⟩, ⟨⟨certificate_1365, certificate_1365_valid⟩, ⟨⟨certificate_1366, certificate_1366_valid⟩, ⟨⟨certificate_1367, certificate_1367_valid⟩, ⟨⟨certificate_1368, certificate_1368_valid⟩, ⟨⟨certificate_1369, certificate_1369_valid⟩, ⟨⟨certificate_1370, certificate_1370_valid⟩, ⟨⟨certificate_1371, certificate_1371_valid⟩, ⟨⟨certificate_1372, certificate_1372_valid⟩, ⟨⟨certificate_1373, certificate_1373_valid⟩, ⟨⟨certificate_1374, certificate_1374_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_14 : List (List (List ℕ)) := [[[],[1,2],[2,3]],[[],[1,2,1],[2]],[[],[1,2,1],[3]],[[],[1,2,1],[4]],[[],[1,2,1,1,2]],[[],[1,2,1,1,3]],[[],[1,2,1,2,1]],[[],[1,2,1,2,2]],[[],[1,2,1,3,1]],[[],[1,2,2],[2]],[[],[1,2,2],[3]],[[],[1,2,2,1,2]],[[],[1,2,2,2,1]],[[],[1,2,3],[2]],[[],[1,3],[1,3]],[[],[1,3],[2,2]]]

theorem patterns_15_7_14_verified : ∀ D ∈ patterns_15_7_14, PatternVerified 15 7 D := by

  simp only [patterns_15_7_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1375, certificate_1375_valid⟩, ⟨⟨certificate_1376, certificate_1376_valid⟩, ⟨⟨certificate_1377, certificate_1377_valid⟩, ⟨⟨certificate_1378, certificate_1378_valid⟩, ⟨⟨certificate_1379, certificate_1379_valid⟩, ⟨⟨certificate_1380, certificate_1380_valid⟩, ⟨⟨certificate_1381, certificate_1381_valid⟩, ⟨⟨certificate_1382, certificate_1382_valid⟩, ⟨⟨certificate_1383, certificate_1383_valid⟩, ⟨⟨certificate_1384, certificate_1384_valid⟩, ⟨⟨certificate_1385, certificate_1385_valid⟩, ⟨⟨certificate_1386, certificate_1386_valid⟩, ⟨⟨certificate_1387, certificate_1387_valid⟩, ⟨⟨certificate_1388, certificate_1388_valid⟩, ⟨⟨certificate_1389, certificate_1389_valid⟩, ⟨⟨certificate_1390, certificate_1390_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_15 : List (List (List ℕ)) := [[[],[1,3,1],[2]],[[],[1,3,1],[3]],[[],[1,3,1,1,2]],[[],[1,3,2],[2]],[[],[1,4,1],[2]],[[],[2],[2],[2]],[[],[2],[2],[3]],[[],[2],[2],[4]],[[],[2],[2,1,2]],[[],[2],[2,1,3]],[[],[2],[2,2,2]],[[],[2],[3],[3]],[[],[2,1,1,1,2]],[[],[2,1,1,1,3]],[[],[2,1,1,2,2]],[[],[2,1,2],[3]]]

theorem patterns_15_7_15_verified : ∀ D ∈ patterns_15_7_15, PatternVerified 15 7 D := by

  simp only [patterns_15_7_15, List.forall_mem_cons]

  exact ⟨⟨certificate_1391, certificate_1391_valid⟩, ⟨⟨certificate_1392, certificate_1392_valid⟩, ⟨⟨certificate_1393, certificate_1393_valid⟩, ⟨⟨certificate_1394, certificate_1394_valid⟩, ⟨⟨certificate_1395, certificate_1395_valid⟩, ⟨⟨certificate_1396, certificate_1396_valid⟩, ⟨⟨certificate_1397, certificate_1397_valid⟩, ⟨⟨certificate_1398, certificate_1398_valid⟩, ⟨⟨certificate_1399, certificate_1399_valid⟩, ⟨⟨certificate_1400, certificate_1400_valid⟩, ⟨⟨certificate_1401, certificate_1401_valid⟩, ⟨⟨certificate_1402, certificate_1402_valid⟩, ⟨⟨certificate_1403, certificate_1403_valid⟩, ⟨⟨certificate_1404, certificate_1404_valid⟩, ⟨⟨certificate_1405, certificate_1405_valid⟩, ⟨⟨certificate_1406, certificate_1406_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_16 : List (List (List ℕ)) := [[[],[2,1,2,1,2]],[[],[2,2],[2,2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[1,4]],[[1],[1],[1,5]],[[1],[1],[2,2]],[[1],[1],[2,3]],[[1],[1],[2,4]],[[1],[1],[3,3]],[[1],[1,1],[2]],[[1],[1,1],[3]],[[1],[1,1],[4]],[[1],[1,1],[5]],[[1],[1,1,1,1]]]

theorem patterns_15_7_16_verified : ∀ D ∈ patterns_15_7_16, PatternVerified 15 7 D := by

  simp only [patterns_15_7_16, List.forall_mem_cons]

  exact ⟨⟨certificate_1407, certificate_1407_valid⟩, ⟨⟨certificate_1408, certificate_1408_valid⟩, ⟨⟨certificate_1409, certificate_1409_valid⟩, ⟨⟨certificate_1410, certificate_1410_valid⟩, ⟨⟨certificate_1411, certificate_1411_valid⟩, ⟨⟨certificate_1412, certificate_1412_valid⟩, ⟨⟨certificate_1413, certificate_1413_valid⟩, ⟨⟨certificate_1414, certificate_1414_valid⟩, ⟨⟨certificate_1415, certificate_1415_valid⟩, ⟨⟨certificate_1416, certificate_1416_valid⟩, ⟨⟨certificate_1417, certificate_1417_valid⟩, ⟨⟨certificate_1418, certificate_1418_valid⟩, ⟨⟨certificate_1419, certificate_1419_valid⟩, ⟨⟨certificate_1420, certificate_1420_valid⟩, ⟨⟨certificate_1421, certificate_1421_valid⟩, ⟨⟨certificate_1422, certificate_1422_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_17 : List (List (List ℕ)) := [[[1],[1,1,1,2]],[[1],[1,1,1,3]],[[1],[1,1,1,4]],[[1],[1,1,2,1]],[[1],[1,1,2,2]],[[1],[1,1,2,3]],[[1],[1,1,3,1]],[[1],[1,1,3,2]],[[1],[1,1,4,1]],[[1],[1,2],[2]],[[1],[1,2],[3]],[[1],[1,2],[4]],[[1],[1,2,1,2]],[[1],[1,2,1,3]],[[1],[1,2,2,1]],[[1],[1,2,2,2]]]

theorem patterns_15_7_17_verified : ∀ D ∈ patterns_15_7_17, PatternVerified 15 7 D := by

  simp only [patterns_15_7_17, List.forall_mem_cons]

  exact ⟨⟨certificate_1423, certificate_1423_valid⟩, ⟨⟨certificate_1424, certificate_1424_valid⟩, ⟨⟨certificate_1425, certificate_1425_valid⟩, ⟨⟨certificate_1426, certificate_1426_valid⟩, ⟨⟨certificate_1427, certificate_1427_valid⟩, ⟨⟨certificate_1428, certificate_1428_valid⟩, ⟨⟨certificate_1429, certificate_1429_valid⟩, ⟨⟨certificate_1430, certificate_1430_valid⟩, ⟨⟨certificate_1431, certificate_1431_valid⟩, ⟨⟨certificate_1432, certificate_1432_valid⟩, ⟨⟨certificate_1433, certificate_1433_valid⟩, ⟨⟨certificate_1434, certificate_1434_valid⟩, ⟨⟨certificate_1435, certificate_1435_valid⟩, ⟨⟨certificate_1436, certificate_1436_valid⟩, ⟨⟨certificate_1437, certificate_1437_valid⟩, ⟨⟨certificate_1438, certificate_1438_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_18 : List (List (List ℕ)) := [[[1],[1,2,3,1]],[[1],[1,3],[2]],[[1],[1,3],[3]],[[1],[1,3,1,2]],[[1],[1,4],[2]],[[1],[2],[2,2]],[[1],[2],[2,3]],[[1],[2,1,1,2]],[[1],[2,1,1,3]],[[1],[2,1,2,2]],[[1],[2,2],[3]],[[1,1],[1,1,1]],[[1,1],[1,1,2]],[[1,1],[1,1,3]],[[1,1],[1,1,4]],[[1,1],[1,2,1]]]

theorem patterns_15_7_18_verified : ∀ D ∈ patterns_15_7_18, PatternVerified 15 7 D := by

  simp only [patterns_15_7_18, List.forall_mem_cons]

  exact ⟨⟨certificate_1439, certificate_1439_valid⟩, ⟨⟨certificate_1440, certificate_1440_valid⟩, ⟨⟨certificate_1441, certificate_1441_valid⟩, ⟨⟨certificate_1442, certificate_1442_valid⟩, ⟨⟨certificate_1443, certificate_1443_valid⟩, ⟨⟨certificate_1444, certificate_1444_valid⟩, ⟨⟨certificate_1445, certificate_1445_valid⟩, ⟨⟨certificate_1446, certificate_1446_valid⟩, ⟨⟨certificate_1447, certificate_1447_valid⟩, ⟨⟨certificate_1448, certificate_1448_valid⟩, ⟨⟨certificate_1449, certificate_1449_valid⟩, ⟨⟨certificate_1450, certificate_1450_valid⟩, ⟨⟨certificate_1451, certificate_1451_valid⟩, ⟨⟨certificate_1452, certificate_1452_valid⟩, ⟨⟨certificate_1453, certificate_1453_valid⟩, ⟨⟨certificate_1454, certificate_1454_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_19 : List (List (List ℕ)) := [[[1,1],[1,2,2]],[[1,1],[1,2,3]],[[1,1],[1,3,1]],[[1,1],[1,3,2]],[[1,1],[1,4,1]],[[1,1],[2],[2]],[[1,1],[2],[3]],[[1,1],[2],[4]],[[1,1],[2,1,2]],[[1,1],[2,1,3]],[[1,1],[2,2,2]],[[1,1],[3],[3]],[[1,1,1],[1,2]],[[1,1,1],[1,3]],[[1,1,1],[1,4]],[[1,1,1],[2,2]]]

theorem patterns_15_7_19_verified : ∀ D ∈ patterns_15_7_19, PatternVerified 15 7 D := by

  simp only [patterns_15_7_19, List.forall_mem_cons]

  exact ⟨⟨certificate_1455, certificate_1455_valid⟩, ⟨⟨certificate_1456, certificate_1456_valid⟩, ⟨⟨certificate_1457, certificate_1457_valid⟩, ⟨⟨certificate_1458, certificate_1458_valid⟩, ⟨⟨certificate_1459, certificate_1459_valid⟩, ⟨⟨certificate_1460, certificate_1460_valid⟩, ⟨⟨certificate_1461, certificate_1461_valid⟩, ⟨⟨certificate_1462, certificate_1462_valid⟩, ⟨⟨certificate_1463, certificate_1463_valid⟩, ⟨⟨certificate_1464, certificate_1464_valid⟩, ⟨⟨certificate_1465, certificate_1465_valid⟩, ⟨⟨certificate_1466, certificate_1466_valid⟩, ⟨⟨certificate_1467, certificate_1467_valid⟩, ⟨⟨certificate_1468, certificate_1468_valid⟩, ⟨⟨certificate_1469, certificate_1469_valid⟩, ⟨⟨certificate_1470, certificate_1470_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_20 : List (List (List ℕ)) := [[[1,1,1],[2,3]],[[1,1,1,1],[2]],[[1,1,1,1],[3]],[[1,1,1,1],[4]],[[1,1,1,1,1,1]],[[1,1,1,1,1,2]],[[1,1,1,1,1,3]],[[1,1,1,1,2,1]],[[1,1,1,1,2,2]],[[1,1,1,1,3,1]],[[1,1,1,2],[2]],[[1,1,1,2],[3]],[[1,1,1,2,1,1]],[[1,1,1,2,1,2]],[[1,1,1,2,2,1]],[[1,1,1,3],[2]]]

theorem patterns_15_7_20_verified : ∀ D ∈ patterns_15_7_20, PatternVerified 15 7 D := by

  simp only [patterns_15_7_20, List.forall_mem_cons]

  exact ⟨⟨certificate_1471, certificate_1471_valid⟩, ⟨⟨certificate_1472, certificate_1472_valid⟩, ⟨⟨certificate_1473, certificate_1473_valid⟩, ⟨⟨certificate_1474, certificate_1474_valid⟩, ⟨⟨certificate_1475, certificate_1475_valid⟩, ⟨⟨certificate_1476, certificate_1476_valid⟩, ⟨⟨certificate_1477, certificate_1477_valid⟩, ⟨⟨certificate_1478, certificate_1478_valid⟩, ⟨⟨certificate_1479, certificate_1479_valid⟩, ⟨⟨certificate_1480, certificate_1480_valid⟩, ⟨⟨certificate_1481, certificate_1481_valid⟩, ⟨⟨certificate_1482, certificate_1482_valid⟩, ⟨⟨certificate_1483, certificate_1483_valid⟩, ⟨⟨certificate_1484, certificate_1484_valid⟩, ⟨⟨certificate_1485, certificate_1485_valid⟩, ⟨⟨certificate_1486, certificate_1486_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_21 : List (List (List ℕ)) := [[[1,1,1,3,1,1]],[[1,1,2],[1,2]],[[1,1,2],[1,3]],[[1,1,2],[2,2]],[[1,1,2,1],[2]],[[1,1,2,1],[3]],[[1,1,2,1,1,2]],[[1,1,2,1,2,1]],[[1,1,2,2],[2]],[[1,1,2,2,1,1]],[[1,1,3],[1,2]],[[1,1,3,1],[2]],[[1,2],[1,2,1]],[[1,2],[1,2,2]],[[1,2],[1,3,1]],[[1,2],[2],[2]]]

theorem patterns_15_7_21_verified : ∀ D ∈ patterns_15_7_21, PatternVerified 15 7 D := by

  simp only [patterns_15_7_21, List.forall_mem_cons]

  exact ⟨⟨certificate_1487, certificate_1487_valid⟩, ⟨⟨certificate_1488, certificate_1488_valid⟩, ⟨⟨certificate_1489, certificate_1489_valid⟩, ⟨⟨certificate_1490, certificate_1490_valid⟩, ⟨⟨certificate_1491, certificate_1491_valid⟩, ⟨⟨certificate_1492, certificate_1492_valid⟩, ⟨⟨certificate_1493, certificate_1493_valid⟩, ⟨⟨certificate_1494, certificate_1494_valid⟩, ⟨⟨certificate_1495, certificate_1495_valid⟩, ⟨⟨certificate_1496, certificate_1496_valid⟩, ⟨⟨certificate_1497, certificate_1497_valid⟩, ⟨⟨certificate_1498, certificate_1498_valid⟩, ⟨⟨certificate_1499, certificate_1499_valid⟩, ⟨⟨certificate_1500, certificate_1500_valid⟩, ⟨⟨certificate_1501, certificate_1501_valid⟩, ⟨⟨certificate_1502, certificate_1502_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7_22 : List (List (List ℕ)) := [[[1,2],[2],[3]],[[1,2],[2,1,2]],[[1,2,1],[1,3]],[[1,2,1],[2,2]],[[1,2,1,1,1,2]],[[1,2,1,1,2,1]],[[1,2,1,2],[2]],[[1,2,2,1],[2]],[[1,3],[2],[2]],[[2],[2],[2,2]],[[2],[2,1,1,2]],[[2,1,1,1,1,2]]]

theorem patterns_15_7_22_verified : ∀ D ∈ patterns_15_7_22, PatternVerified 15 7 D := by

  simp only [patterns_15_7_22, List.forall_mem_cons]

  exact ⟨⟨certificate_1503, certificate_1503_valid⟩, ⟨⟨certificate_1504, certificate_1504_valid⟩, ⟨⟨certificate_1505, certificate_1505_valid⟩, ⟨⟨certificate_1506, certificate_1506_valid⟩, ⟨⟨certificate_1507, certificate_1507_valid⟩, ⟨⟨certificate_1508, certificate_1508_valid⟩, ⟨⟨certificate_1509, certificate_1509_valid⟩, ⟨⟨certificate_1510, certificate_1510_valid⟩, ⟨⟨certificate_1511, certificate_1511_valid⟩, ⟨⟨certificate_1512, certificate_1512_valid⟩, ⟨⟨certificate_1513, certificate_1513_valid⟩, ⟨⟨certificate_1514, certificate_1514_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_7 : List (List (List ℕ)) := patterns_15_7_0 ++ (patterns_15_7_1 ++ (patterns_15_7_2 ++ (patterns_15_7_3 ++ (patterns_15_7_4 ++ (patterns_15_7_5 ++ (patterns_15_7_6 ++ (patterns_15_7_7 ++ (patterns_15_7_8 ++ (patterns_15_7_9 ++ (patterns_15_7_10 ++ (patterns_15_7_11 ++ (patterns_15_7_12 ++ (patterns_15_7_13 ++ (patterns_15_7_14 ++ (patterns_15_7_15 ++ (patterns_15_7_16 ++ (patterns_15_7_17 ++ (patterns_15_7_18 ++ (patterns_15_7_19 ++ (patterns_15_7_20 ++ (patterns_15_7_21 ++ (patterns_15_7_22 ++ ([])))))))))))))))))))))))

theorem patterns_15_7_verified : ∀ D ∈ patterns_15_7, PatternVerified 15 7 D := by

  simp only [patterns_15_7, List.forall_mem_append]

  exact ⟨patterns_15_7_0_verified, ⟨patterns_15_7_1_verified, ⟨patterns_15_7_2_verified, ⟨patterns_15_7_3_verified, ⟨patterns_15_7_4_verified, ⟨patterns_15_7_5_verified, ⟨patterns_15_7_6_verified, ⟨patterns_15_7_7_verified, ⟨patterns_15_7_8_verified, ⟨patterns_15_7_9_verified, ⟨patterns_15_7_10_verified, ⟨patterns_15_7_11_verified, ⟨patterns_15_7_12_verified, ⟨patterns_15_7_13_verified, ⟨patterns_15_7_14_verified, ⟨patterns_15_7_15_verified, ⟨patterns_15_7_16_verified, ⟨patterns_15_7_17_verified, ⟨patterns_15_7_18_verified, ⟨patterns_15_7_19_verified, ⟨patterns_15_7_20_verified, ⟨patterns_15_7_21_verified, ⟨patterns_15_7_22_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_7_coverage : patternChoices 7 8 [] = patterns_15_7 := by decide +kernel

theorem finite_patterns_15_7 : ∀ D ∈ patternChoices 7 (15-7) [], PatternVerified 15 7 D := by

  rw [patterns_15_7_coverage]

  exact patterns_15_7_verified

end CycleClique

end OAI
