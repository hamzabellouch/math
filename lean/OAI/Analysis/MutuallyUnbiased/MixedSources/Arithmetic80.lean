import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1280 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue2410 x + ((2 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1280 : Integer.Sparse Master := [(Sum.inr 1192, 1), (Sum.inr 2410, 1), (Sum.inr 2538, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1280 : Integer.Sparse.reindex keyMap MixedData.row1280 = numericRow1280 := by decide +kernel

theorem numericCheck1280 (x : Master → ℝ) : Integer.Sparse.eval numericRow1280 x =
    (1 : ℝ) * reducedSource1280 x := by
  norm_num [numericRow1280, reducedSource1280, Integer.Sparse.eval, Sparse.eval, nodeValue1192, nodeValue2410, nodeValue2538, nodeValue2685, nodeValue2687, nodeValue4082]

noncomputable def reducedSource1281 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue2411 x + ((2 : ℝ) * Sparse.eval nodeValue2539 x + ((2 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))

def numericRow1281 : Integer.Sparse Master := [(Sum.inr 1193, 1), (Sum.inr 2539, 2), (Sum.inr 2686, 2), (Sum.inr 4089, -1)]

theorem reindexCheck1281 : Integer.Sparse.reindex keyMap MixedData.row1281 = numericRow1281 := by decide +kernel

theorem numericCheck1281 (x : Master → ℝ) : Integer.Sparse.eval numericRow1281 x =
    (1 : ℝ) * reducedSource1281 x := by
  norm_num [numericRow1281, reducedSource1281, Integer.Sparse.eval, Sparse.eval, nodeValue1193, nodeValue2411, nodeValue2539, nodeValue2686, nodeValue4089]

noncomputable def reducedSource1282 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1099 x + ((2 : ℝ) * Sparse.eval nodeValue1104 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue2411 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))

def numericRow1282 : Integer.Sparse Master := [(Sum.inr 1099, 2), (Sum.inr 1104, 2), (Sum.inr 1193, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1282 : Integer.Sparse.reindex keyMap MixedData.row1282 = numericRow1282 := by decide +kernel

theorem numericCheck1282 (x : Master → ℝ) : Integer.Sparse.eval numericRow1282 x =
    (1 : ℝ) * reducedSource1282 x := by
  norm_num [numericRow1282, reducedSource1282, Integer.Sparse.eval, Sparse.eval, nodeValue1099, nodeValue1104, nodeValue1193, nodeValue2411, nodeValue4089]

noncomputable def reducedSource1283 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1204 x + ((2 : ℝ) * Sparse.eval nodeValue2467 x + ((1 : ℝ) * Sparse.eval nodeValue2540 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1283 : Integer.Sparse Master := [(Sum.inr 1204, 1), (Sum.inr 2467, 2), (Sum.inr 2704, 1), (Sum.inr 2706, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1283 : Integer.Sparse.reindex keyMap MixedData.row1283 = numericRow1283 := by decide +kernel

theorem numericCheck1283 (x : Master → ℝ) : Integer.Sparse.eval numericRow1283 x =
    (1 : ℝ) * reducedSource1283 x := by
  norm_num [numericRow1283, reducedSource1283, Integer.Sparse.eval, Sparse.eval, nodeValue1204, nodeValue2467, nodeValue2540, nodeValue2704, nodeValue2706, nodeValue4080]

noncomputable def reducedSource1284 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue2468 x + ((1 : ℝ) * Sparse.eval nodeValue2541 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))

def numericRow1284 : Integer.Sparse Master := [(Sum.inr 1205, 1), (Sum.inr 2541, 1), (Sum.inr 2705, 2), (Sum.inr 4088, -1)]

theorem reindexCheck1284 : Integer.Sparse.reindex keyMap MixedData.row1284 = numericRow1284 := by decide +kernel

theorem numericCheck1284 (x : Master → ℝ) : Integer.Sparse.eval numericRow1284 x =
    (1 : ℝ) * reducedSource1284 x := by
  norm_num [numericRow1284, reducedSource1284, Integer.Sparse.eval, Sparse.eval, nodeValue1205, nodeValue2468, nodeValue2541, nodeValue2705, nodeValue4088]

noncomputable def reducedSource1285 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1106 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((1 : ℝ) * Sparse.eval nodeValue1124 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((1 : ℝ) * Sparse.eval nodeValue2468 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1285 : Integer.Sparse Master := [(Sum.inr 1106, 1), (Sum.inr 1110, 2), (Sum.inr 1124, 1), (Sum.inr 1205, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1285 : Integer.Sparse.reindex keyMap MixedData.row1285 = numericRow1285 := by decide +kernel

theorem numericCheck1285 (x : Master → ℝ) : Integer.Sparse.eval numericRow1285 x =
    (1 : ℝ) * reducedSource1285 x := by
  norm_num [numericRow1285, reducedSource1285, Integer.Sparse.eval, Sparse.eval, nodeValue1106, nodeValue1110, nodeValue1124, nodeValue1205, nodeValue2468, nodeValue4088]

noncomputable def reducedSource1286 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1062 x + ((2 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1286 : Integer.Sparse Master := [(Sum.inr 1062, 1), (Sum.inr 2038, 2), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1286 : Integer.Sparse.reindex keyMap MixedData.row1286 = numericRow1286 := by decide +kernel

theorem numericCheck1286 (x : Master → ℝ) : Integer.Sparse.eval numericRow1286 x =
    (1 : ℝ) * reducedSource1286 x := by
  norm_num [numericRow1286, reducedSource1286, Integer.Sparse.eval, Sparse.eval, nodeValue1062, nodeValue2038, nodeValue2137, nodeValue2276, nodeValue2280, nodeValue4082]

noncomputable def reducedSource1287 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1287 : Integer.Sparse Master := [(Sum.inr 992, 1), (Sum.inr 1928, 1), (Sum.inr 1993, 1), (Sum.inr 2122, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1287 : Integer.Sparse.reindex keyMap MixedData.row1287 = numericRow1287 := by decide +kernel

theorem numericCheck1287 (x : Master → ℝ) : Integer.Sparse.eval numericRow1287 x =
    (1 : ℝ) * reducedSource1287 x := by
  norm_num [numericRow1287, reducedSource1287, Integer.Sparse.eval, Sparse.eval, nodeValue992, nodeValue1928, nodeValue1993, nodeValue2122, nodeValue2215, nodeValue2217, nodeValue4082]

noncomputable def reducedSource1288 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1929 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1288 : Integer.Sparse Master := [(Sum.inr 993, 1), (Sum.inr 1929, 1), (Sum.inr 1994, 1), (Sum.inr 2123, 1), (Sum.inr 2216, 2), (Sum.inr 4080, -1)]

theorem reindexCheck1288 : Integer.Sparse.reindex keyMap MixedData.row1288 = numericRow1288 := by decide +kernel

theorem numericCheck1288 (x : Master → ℝ) : Integer.Sparse.eval numericRow1288 x =
    (1 : ℝ) * reducedSource1288 x := by
  norm_num [numericRow1288, reducedSource1288, Integer.Sparse.eval, Sparse.eval, nodeValue993, nodeValue1929, nodeValue1994, nodeValue2123, nodeValue2216, nodeValue4080]

noncomputable def reducedSource1289 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1025 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1289 : Integer.Sparse Master := [(Sum.inr 1025, 1), (Sum.inr 2011, 1), (Sum.inr 2093, 2), (Sum.inr 2242, 1), (Sum.inr 2246, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1289 : Integer.Sparse.reindex keyMap MixedData.row1289 = numericRow1289 := by decide +kernel

theorem numericCheck1289 (x : Master → ℝ) : Integer.Sparse.eval numericRow1289 x =
    (1 : ℝ) * reducedSource1289 x := by
  norm_num [numericRow1289, reducedSource1289, Integer.Sparse.eval, Sparse.eval, nodeValue1025, nodeValue2011, nodeValue2093, nodeValue2242, nodeValue2246, nodeValue4080]

noncomputable def reducedSource1290 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue973 x + ((1 : ℝ) * Sparse.eval nodeValue1900 x + ((2 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1290 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 1900, 1), (Sum.inr 2072, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1290 : Integer.Sparse.reindex keyMap MixedData.row1290 = numericRow1290 := by decide +kernel

theorem numericCheck1290 (x : Master → ℝ) : Integer.Sparse.eval numericRow1290 x =
    (1 : ℝ) * reducedSource1290 x := by
  norm_num [numericRow1290, reducedSource1290, Integer.Sparse.eval, Sparse.eval, nodeValue973, nodeValue1900, nodeValue2072, nodeValue2190, nodeValue2192, nodeValue4080]

noncomputable def reducedSource1291 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue974 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue2073 x + ((2 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

def numericRow1291 : Integer.Sparse Master := [(Sum.inr 1901, 1), (Sum.inr 2073, 2), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

theorem reindexCheck1291 : Integer.Sparse.reindex keyMap MixedData.row1291 = numericRow1291 := by decide +kernel

theorem numericCheck1291 (x : Master → ℝ) : Integer.Sparse.eval numericRow1291 x =
    (1 : ℝ) * reducedSource1291 x := by
  norm_num [numericRow1291, reducedSource1291, Integer.Sparse.eval, Sparse.eval, nodeValue974, nodeValue1901, nodeValue2073, nodeValue2191, nodeValue4079]

noncomputable def reducedSource1292 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1048 x + ((2 : ℝ) * Sparse.eval nodeValue2027 x + ((1 : ℝ) * Sparse.eval nodeValue2114 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1292 : Integer.Sparse Master := [(Sum.inr 1048, 1), (Sum.inr 2027, 2), (Sum.inr 2114, 1), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1292 : Integer.Sparse.reindex keyMap MixedData.row1292 = numericRow1292 := by decide +kernel

theorem numericCheck1292 (x : Master → ℝ) : Integer.Sparse.eval numericRow1292 x =
    (1 : ℝ) * reducedSource1292 x := by
  norm_num [numericRow1292, reducedSource1292, Integer.Sparse.eval, Sparse.eval, nodeValue1048, nodeValue2027, nodeValue2114, nodeValue2261, nodeValue2267, nodeValue4081]

noncomputable def reducedSource1293 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4162 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4328 x + ((2 : ℝ) * Sparse.eval nodeValue4334 x + ((2 : ℝ) * Sparse.eval nodeValue4336 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + 0))))))))))))))))))))

def numericRow1293 : Integer.Sparse Master := [(Sum.inr 613, -1), (Sum.inr 932, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -1), (Sum.inr 1087, -1), (Sum.inr 1525, -1), (Sum.inr 1681, -2), (Sum.inr 1707, -2), (Sum.inr 1725, -1), (Sum.inr 1739, -1), (Sum.inr 2028, -2), (Sum.inr 2115, -1), (Sum.inr 2215, -2), (Sum.inr 2266, -1), (Sum.inr 2276, -1), (Sum.inr 2278, -1), (Sum.inr 4154, 8), (Sum.inr 4160, 4), (Sum.inr 4162, 4), (Sum.inr 4328, 8), (Sum.inr 4334, 8), (Sum.inr 4336, 8), (Sum.inr 4368, 8), (Sum.inr 4373, 4), (Sum.inr 4375, 4), (Sum.inr 4459, 8), (Sum.inr 4464, 4)]

theorem reindexCheck1293 : Integer.Sparse.reindex keyMap MixedData.row1293 = numericRow1293 := by decide +kernel

theorem numericCheck1293 (x : Master → ℝ) : Integer.Sparse.eval numericRow1293 x =
    (4 : ℝ) * reducedSource1293 x := by
  norm_num [numericRow1293, reducedSource1293, Integer.Sparse.eval, Sparse.eval, nodeValue4154, nodeValue4160, nodeValue4162, nodeValue4185, nodeValue4328, nodeValue4334, nodeValue4336, nodeValue4354, nodeValue4368, nodeValue4373, nodeValue4375, nodeValue4457, nodeValue4459, nodeValue4460, nodeValue4464, nodeValue4498, nodeValue4503, nodeValue4810, nodeValue4874, nodeValue4894, nodeValue4896]
  ring

noncomputable def reducedSource1294 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue634 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue648 x + ((2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue1330 x + ((2 : ℝ) * Sparse.eval nodeValue1332 x + ((2 : ℝ) * Sparse.eval nodeValue1334 x + ((2 : ℝ) * Sparse.eval nodeValue1343 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1442 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow1294 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, 160), (Sum.inl 2, 140), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 1, 110), (Sum.inr 631, 2880), (Sum.inr 634, 1440), (Sum.inr 636, 1440), (Sum.inr 1321, 2880), (Sum.inr 1323, 1440), (Sum.inr 1325, 1440), (Sum.inr 1330, 2880), (Sum.inr 1332, 2880), (Sum.inr 1334, 2880), (Sum.inr 1406, 2880), (Sum.inr 1408, 1440)]

theorem reindexCheck1294 : Integer.Sparse.reindex keyMap MixedData.row1294 = numericRow1294 := by decide +kernel

theorem numericCheck1294 (x : Master → ℝ) : Integer.Sparse.eval numericRow1294 x =
    (1440 : ℝ) * reducedSource1294 x := by
  norm_num [numericRow1294, reducedSource1294, Integer.Sparse.eval, Sparse.eval, nodeValue631, nodeValue634, nodeValue636, nodeValue648, nodeValue1321, nodeValue1323, nodeValue1325, nodeValue1330, nodeValue1332, nodeValue1334, nodeValue1343, nodeValue1406, nodeValue1408, nodeValue1414, nodeValue1416, nodeValue1442, nodeValue1448, nodeValue3187, nodeValue3206, nodeValue3225, nodeValue3230]
  ring

noncomputable def reducedSource1295 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1529 x + ((2 : ℝ) * Sparse.eval nodeValue1667 x + ((2 : ℝ) * Sparse.eval nodeValue1679 x + ((2 : ℝ) * Sparse.eval nodeValue1681 x + ((2 : ℝ) * Sparse.eval nodeValue1685 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((2 : ℝ) * Sparse.eval nodeValue1712 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + 0))))))))))))))))))))

def numericRow1295 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1523, 1), (Sum.inr 1525, 1), (Sum.inr 1529, 1), (Sum.inr 1667, 2), (Sum.inr 1679, 2), (Sum.inr 1681, 2), (Sum.inr 1685, 2), (Sum.inr 1707, 2), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 1739, 1), (Sum.inr 1743, 1), (Sum.inr 1745, 1), (Sum.inr 2215, 2), (Sum.inr 2276, 1), (Sum.inr 2278, 1)]

theorem reindexCheck1295 : Integer.Sparse.reindex keyMap MixedData.row1295 = numericRow1295 := by decide +kernel

theorem numericCheck1295 (x : Master → ℝ) : Integer.Sparse.eval numericRow1295 x =
    (1 : ℝ) * reducedSource1295 x := by
  norm_num [numericRow1295, reducedSource1295, Integer.Sparse.eval, Sparse.eval, nodeValue1511, nodeValue1523, nodeValue1525, nodeValue1529, nodeValue1667, nodeValue1679, nodeValue1681, nodeValue1685, nodeValue1707, nodeValue1712, nodeValue1714, nodeValue1725, nodeValue1727, nodeValue1735, nodeValue1739, nodeValue1743, nodeValue1745, nodeValue2215, nodeValue2264, nodeValue2276, nodeValue2278]

end MUB6.Certificate.MixedSourceBridge

end OAI
