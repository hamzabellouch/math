import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block25
import OAI.Analysis.MutuallyUnbiased.GramRows.Block26
import OAI.Analysis.MutuallyUnbiased.GramRows.Block27
import OAI.Analysis.MutuallyUnbiased.GramRows.Block28
import OAI.Analysis.MutuallyUnbiased.GramRows.Block29
import OAI.Analysis.MutuallyUnbiased.GramRows.Block30
import OAI.Analysis.MutuallyUnbiased.GramRows.Block33
import OAI.Analysis.MutuallyUnbiased.GramRows.Block34

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1182, row1183, row1184, row1185, row1186, row1187, row1188, row1189, row1190, row1191, row1192, row1193, row904, row905, row906, row907, row908, row909, row1194, row1195, row1196, row1197, row1198, row1199, row913, row914, row915, row916, row917, row918]

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1182 x
  · exact rowEval1183 x
  · exact rowEval1184 x
  · exact rowEval1185 x
  · exact rowEval1186 x
  · exact rowEval1187 x
  · exact rowEval1188 x
  · exact rowEval1189 x
  · exact rowEval1190 x
  · exact rowEval1191 x
  · exact rowEval1192 x
  · exact rowEval1193 x
  · exact rowEval904 x
  · exact rowEval905 x
  · exact rowEval906 x
  · exact rowEval907 x
  · exact rowEval908 x
  · exact rowEval909 x
  · exact rowEval1194 x
  · exact rowEval1195 x
  · exact rowEval1196 x
  · exact rowEval1197 x
  · exact rowEval1198 x
  · exact rowEval1199 x
  · exact rowEval913 x
  · exact rowEval914 x
  · exact rowEval915 x
  · exact rowEval916 x
  · exact rowEval917 x
  · exact rowEval918 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

def rows7_1 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1200, row1201, row1202, row1203, row1204, row1205, row1206, row1207, row1208, row1209, row1210, row1211, row934, row935, row936, row937, row938, row939, row1212, row1213, row1214, row1215, row1216, row1217, row943, row944, row945, row946, row947, row948]

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1200 x
  · exact rowEval1201 x
  · exact rowEval1202 x
  · exact rowEval1203 x
  · exact rowEval1204 x
  · exact rowEval1205 x
  · exact rowEval1206 x
  · exact rowEval1207 x
  · exact rowEval1208 x
  · exact rowEval1209 x
  · exact rowEval1210 x
  · exact rowEval1211 x
  · exact rowEval934 x
  · exact rowEval935 x
  · exact rowEval936 x
  · exact rowEval937 x
  · exact rowEval938 x
  · exact rowEval939 x
  · exact rowEval1212 x
  · exact rowEval1213 x
  · exact rowEval1214 x
  · exact rowEval1215 x
  · exact rowEval1216 x
  · exact rowEval1217 x
  · exact rowEval943 x
  · exact rowEval944 x
  · exact rowEval945 x
  · exact rowEval946 x
  · exact rowEval947 x
  · exact rowEval948 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

def rows7_2 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1218, row1219, row1220, row1221, row1222, row1223, row1224, row1225, row1226, row1227, row1228, row1229, row964, row965, row966, row967, row968, row969, row1230, row1231, row1232, row1233, row1234, row1235, row973, row974, row975, row976, row977, row978]

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1218 x
  · exact rowEval1219 x
  · exact rowEval1220 x
  · exact rowEval1221 x
  · exact rowEval1222 x
  · exact rowEval1223 x
  · exact rowEval1224 x
  · exact rowEval1225 x
  · exact rowEval1226 x
  · exact rowEval1227 x
  · exact rowEval1228 x
  · exact rowEval1229 x
  · exact rowEval964 x
  · exact rowEval965 x
  · exact rowEval966 x
  · exact rowEval967 x
  · exact rowEval968 x
  · exact rowEval969 x
  · exact rowEval1230 x
  · exact rowEval1231 x
  · exact rowEval1232 x
  · exact rowEval1233 x
  · exact rowEval1234 x
  · exact rowEval1235 x
  · exact rowEval973 x
  · exact rowEval974 x
  · exact rowEval975 x
  · exact rowEval976 x
  · exact rowEval977 x
  · exact rowEval978 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

def rows7_3 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1236, row1237, row1238, row1239, row1240, row1241, row1242, row1243, row1244, row1245, row1246, row1247, row994, row995, row996, row997, row998, row999, row1248, row1249, row1250, row1251, row1252, row1253, row1003, row1004, row1005, row1006, row1007, row1008]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1236 x
  · exact rowEval1237 x
  · exact rowEval1238 x
  · exact rowEval1239 x
  · exact rowEval1240 x
  · exact rowEval1241 x
  · exact rowEval1242 x
  · exact rowEval1243 x
  · exact rowEval1244 x
  · exact rowEval1245 x
  · exact rowEval1246 x
  · exact rowEval1247 x
  · exact rowEval994 x
  · exact rowEval995 x
  · exact rowEval996 x
  · exact rowEval997 x
  · exact rowEval998 x
  · exact rowEval999 x
  · exact rowEval1248 x
  · exact rowEval1249 x
  · exact rowEval1250 x
  · exact rowEval1251 x
  · exact rowEval1252 x
  · exact rowEval1253 x
  · exact rowEval1003 x
  · exact rowEval1004 x
  · exact rowEval1005 x
  · exact rowEval1006 x
  · exact rowEval1007 x
  · exact rowEval1008 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

def rows7_4 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1254, row1255, row1256, row1257, row1258, row1259, row1260, row1261, row1262, row1263, row1264, row1265, row1024, row1025, row1026, row1027, row1028, row1029, row1266, row1267, row1268, row1269, row1270, row1271, row1033, row1034, row1035, row1036, row1037, row1038]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1254 x
  · exact rowEval1255 x
  · exact rowEval1256 x
  · exact rowEval1257 x
  · exact rowEval1258 x
  · exact rowEval1259 x
  · exact rowEval1260 x
  · exact rowEval1261 x
  · exact rowEval1262 x
  · exact rowEval1263 x
  · exact rowEval1264 x
  · exact rowEval1265 x
  · exact rowEval1024 x
  · exact rowEval1025 x
  · exact rowEval1026 x
  · exact rowEval1027 x
  · exact rowEval1028 x
  · exact rowEval1029 x
  · exact rowEval1266 x
  · exact rowEval1267 x
  · exact rowEval1268 x
  · exact rowEval1269 x
  · exact rowEval1270 x
  · exact rowEval1271 x
  · exact rowEval1033 x
  · exact rowEval1034 x
  · exact rowEval1035 x
  · exact rowEval1036 x
  · exact rowEval1037 x
  · exact rowEval1038 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

def rows7_5 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1272, row1273, row1274, row1275, row1276, row1277, row1278, row1279, row1280, row1281, row1282, row1283, row1054, row1055, row1056, row1057, row1058, row1059, row1284, row1285, row1286, row1287, row1288, row1289, row1063, row1064, row1065, row1066, row1067, row1068]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1272 x
  · exact rowEval1273 x
  · exact rowEval1274 x
  · exact rowEval1275 x
  · exact rowEval1276 x
  · exact rowEval1277 x
  · exact rowEval1278 x
  · exact rowEval1279 x
  · exact rowEval1280 x
  · exact rowEval1281 x
  · exact rowEval1282 x
  · exact rowEval1283 x
  · exact rowEval1054 x
  · exact rowEval1055 x
  · exact rowEval1056 x
  · exact rowEval1057 x
  · exact rowEval1058 x
  · exact rowEval1059 x
  · exact rowEval1284 x
  · exact rowEval1285 x
  · exact rowEval1286 x
  · exact rowEval1287 x
  · exact rowEval1288 x
  · exact rowEval1289 x
  · exact rowEval1063 x
  · exact rowEval1064 x
  · exact rowEval1065 x
  · exact rowEval1066 x
  · exact rowEval1067 x
  · exact rowEval1068 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

def rows7_6 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1290, row1291, row1292, row1293, row1294, row1295, row1296, row1297, row1298, row1299, row1300, row1301, row1302, row1303, row1304, row1305, row1306, row1307, row1308, row1309, row1310, row1311, row1312, row1313, row1314, row1315, row1316, row1317, row1318, row1319]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1290 x
  · exact rowEval1291 x
  · exact rowEval1292 x
  · exact rowEval1293 x
  · exact rowEval1294 x
  · exact rowEval1295 x
  · exact rowEval1296 x
  · exact rowEval1297 x
  · exact rowEval1298 x
  · exact rowEval1299 x
  · exact rowEval1300 x
  · exact rowEval1301 x
  · exact rowEval1302 x
  · exact rowEval1303 x
  · exact rowEval1304 x
  · exact rowEval1305 x
  · exact rowEval1306 x
  · exact rowEval1307 x
  · exact rowEval1308 x
  · exact rowEval1309 x
  · exact rowEval1310 x
  · exact rowEval1311 x
  · exact rowEval1312 x
  · exact rowEval1313 x
  · exact rowEval1314 x
  · exact rowEval1315 x
  · exact rowEval1316 x
  · exact rowEval1317 x
  · exact rowEval1318 x
  · exact rowEval1319 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

def rows7_7 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1320, row1321, row1322, row1323, row1324, row1325, row1326, row1327, row1328, row1329, row1330, row1331, row1332, row1333, row1334, row1335, row1336, row1337, row1338, row1339, row1340, row1341, row1342, row1343, row1344, row1345, row1346, row1347, row1348, row1349]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block1.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form7.terms k).tag (GramFunctions.Block1.form7.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1320 x
  · exact rowEval1321 x
  · exact rowEval1322 x
  · exact rowEval1323 x
  · exact rowEval1324 x
  · exact rowEval1325 x
  · exact rowEval1326 x
  · exact rowEval1327 x
  · exact rowEval1328 x
  · exact rowEval1329 x
  · exact rowEval1330 x
  · exact rowEval1331 x
  · exact rowEval1332 x
  · exact rowEval1333 x
  · exact rowEval1334 x
  · exact rowEval1335 x
  · exact rowEval1336 x
  · exact rowEval1337 x
  · exact rowEval1338 x
  · exact rowEval1339 x
  · exact rowEval1340 x
  · exact rowEval1341 x
  · exact rowEval1342 x
  · exact rowEval1343 x
  · exact rowEval1344 x
  · exact rowEval1345 x
  · exact rowEval1346 x
  · exact rowEval1347 x
  · exact rowEval1348 x
  · exact rowEval1349 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block1.form7.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form7 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block1

end OAI
