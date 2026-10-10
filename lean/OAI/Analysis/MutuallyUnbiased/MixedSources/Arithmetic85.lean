import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1360 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((2 : ℝ) * Sparse.eval nodeValue784 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1360 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 784, 2), (Sum.inr 803, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1360 : Integer.Sparse.reindex keyMap MixedData.row1360 = numericRow1360 := by decide +kernel

theorem numericCheck1360 (x : Master → ℝ) : Integer.Sparse.eval numericRow1360 x =
    (1 : ℝ) * reducedSource1360 x := by
  norm_num [numericRow1360, reducedSource1360, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue784, nodeValue803, nodeValue1705, nodeValue4069]

noncomputable def reducedSource1361 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1361 : Integer.Sparse Master := [(Sum.inr 803, 1), (Sum.inr 1642, 1), (Sum.inr 1713, 1), (Sum.inr 1724, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1361 : Integer.Sparse.reindex keyMap MixedData.row1361 = numericRow1361 := by decide +kernel

theorem numericCheck1361 (x : Master → ℝ) : Integer.Sparse.eval numericRow1361 x =
    (1 : ℝ) * reducedSource1361 x := by
  norm_num [numericRow1361, reducedSource1361, Integer.Sparse.eval, Sparse.eval, nodeValue803, nodeValue1642, nodeValue1705, nodeValue1713, nodeValue1724, nodeValue4069]

noncomputable def reducedSource1362 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((2 : ℝ) * Sparse.eval nodeValue1635 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1362 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 1635, 2), (Sum.inr 1707, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1362 : Integer.Sparse.reindex keyMap MixedData.row1362 = numericRow1362 := by decide +kernel

theorem numericCheck1362 (x : Master → ℝ) : Integer.Sparse.eval numericRow1362 x =
    (1 : ℝ) * reducedSource1362 x := by
  norm_num [numericRow1362, reducedSource1362, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue1635, nodeValue1705, nodeValue1707, nodeValue4069]

noncomputable def reducedSource1363 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue580 x + ((1 : ℝ) * Sparse.eval nodeValue944 x + ((2 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1363 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 944, 1), (Sum.inr 1021, 2), (Sum.inr 1039, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1363 : Integer.Sparse.reindex keyMap MixedData.row1363 = numericRow1363 := by decide +kernel

theorem numericCheck1363 (x : Master → ℝ) : Integer.Sparse.eval numericRow1363 x =
    (1 : ℝ) * reducedSource1363 x := by
  norm_num [numericRow1363, reducedSource1363, Integer.Sparse.eval, Sparse.eval, nodeValue580, nodeValue944, nodeValue1021, nodeValue1039, nodeValue1044, nodeValue4083]

noncomputable def reducedSource1364 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1364 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1330, 1), (Sum.inr 1335, 1), (Sum.inr 1383, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1364 : Integer.Sparse.reindex keyMap MixedData.row1364 = numericRow1364 := by decide +kernel

theorem numericCheck1364 (x : Master → ℝ) : Integer.Sparse.eval numericRow1364 x =
    (1 : ℝ) * reducedSource1364 x := by
  norm_num [numericRow1364, reducedSource1364, Integer.Sparse.eval, Sparse.eval, nodeValue1327, nodeValue1328, nodeValue1330, nodeValue1335, nodeValue1383, nodeValue2924, nodeValue4091]

noncomputable def reducedSource1365 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3281 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1365 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 2457, 1), (Sum.inr 3278, 1), (Sum.inr 3281, 1), (Sum.inr 3293, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1365 : Integer.Sparse.reindex keyMap MixedData.row1365 = numericRow1365 := by decide +kernel

theorem numericCheck1365 (x : Master → ℝ) : Integer.Sparse.eval numericRow1365 x =
    (1 : ℝ) * reducedSource1365 x := by
  norm_num [numericRow1365, reducedSource1365, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue2457, nodeValue3278, nodeValue3281, nodeValue3293, nodeValue4069]

noncomputable def reducedSource1366 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue822 x + ((1 : ℝ) * Sparse.eval nodeValue1654 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1366 : Integer.Sparse Master := [(Sum.inr 822, 1), (Sum.inr 1654, 1), (Sum.inr 1713, 2), (Sum.inr 1737, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1366 : Integer.Sparse.reindex keyMap MixedData.row1366 = numericRow1366 := by decide +kernel

theorem numericCheck1366 (x : Master → ℝ) : Integer.Sparse.eval numericRow1366 x =
    (1 : ℝ) * reducedSource1366 x := by
  norm_num [numericRow1366, reducedSource1366, Integer.Sparse.eval, Sparse.eval, nodeValue822, nodeValue1654, nodeValue1713, nodeValue1737, nodeValue4069]

noncomputable def reducedSource1367 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1125 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1133 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1367 : Integer.Sparse Master := [(Sum.inr 1125, 1), (Sum.inr 1128, 1), (Sum.inr 1133, 2), (Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1367 : Integer.Sparse.reindex keyMap MixedData.row1367 = numericRow1367 := by decide +kernel

theorem numericCheck1367 (x : Master → ℝ) : Integer.Sparse.eval numericRow1367 x =
    (1 : ℝ) * reducedSource1367 x := by
  norm_num [numericRow1367, reducedSource1367, Integer.Sparse.eval, Sparse.eval, nodeValue1125, nodeValue1128, nodeValue1133, nodeValue1234, nodeValue2509, nodeValue4084]

noncomputable def reducedSource1368 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue1169 x + ((3 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1368 : Integer.Sparse Master := [(Sum.inr 651, 1), (Sum.inr 1169, 1), (Sum.inr 1270, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1368 : Integer.Sparse.reindex keyMap MixedData.row1368 = numericRow1368 := by decide +kernel

theorem numericCheck1368 (x : Master → ℝ) : Integer.Sparse.eval numericRow1368 x =
    (1 : ℝ) * reducedSource1368 x := by
  norm_num [numericRow1368, reducedSource1368, Integer.Sparse.eval, Sparse.eval, nodeValue651, nodeValue1169, nodeValue1270, nodeValue1293, nodeValue4091]

noncomputable def reducedSource1369 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1654 x + ((2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1658 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1369 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1656, 2), (Sum.inr 1658, 1), (Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1369 : Integer.Sparse.reindex keyMap MixedData.row1369 = numericRow1369 := by decide +kernel

theorem numericCheck1369 (x : Master → ℝ) : Integer.Sparse.eval numericRow1369 x =
    (1 : ℝ) * reducedSource1369 x := by
  norm_num [numericRow1369, reducedSource1369, Integer.Sparse.eval, Sparse.eval, nodeValue1654, nodeValue1656, nodeValue1658, nodeValue1737, nodeValue2702, nodeValue4069]

noncomputable def reducedSource1370 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1370 : Integer.Sparse Master := [(Sum.inr 1710, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1370 : Integer.Sparse.reindex keyMap MixedData.row1370 = numericRow1370 := by decide +kernel

theorem numericCheck1370 (x : Master → ℝ) : Integer.Sparse.eval numericRow1370 x =
    (1 : ℝ) * reducedSource1370 x := by
  norm_num [numericRow1370, reducedSource1370, Integer.Sparse.eval, Sparse.eval, nodeValue1710, nodeValue2702, nodeValue2737, nodeValue3308, nodeValue4069]

noncomputable def reducedSource1371 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1371 : Integer.Sparse Master := [(Sum.inr 1602, 1), (Sum.inr 2457, 1), (Sum.inr 2466, 1), (Sum.inr 2502, 1), (Sum.inr 2702, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1371 : Integer.Sparse.reindex keyMap MixedData.row1371 = numericRow1371 := by decide +kernel

theorem numericCheck1371 (x : Master → ℝ) : Integer.Sparse.eval numericRow1371 x =
    (1 : ℝ) * reducedSource1371 x := by
  norm_num [numericRow1371, reducedSource1371, Integer.Sparse.eval, Sparse.eval, nodeValue1602, nodeValue2457, nodeValue2466, nodeValue2502, nodeValue2702, nodeValue3293, nodeValue4069]

noncomputable def reducedSource1372 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1372 : Integer.Sparse Master := [(Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 3288, 1), (Sum.inr 3293, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1372 : Integer.Sparse.reindex keyMap MixedData.row1372 = numericRow1372 := by decide +kernel

theorem numericCheck1372 (x : Master → ℝ) : Integer.Sparse.eval numericRow1372 x =
    (1 : ℝ) * reducedSource1372 x := by
  norm_num [numericRow1372, reducedSource1372, Integer.Sparse.eval, Sparse.eval, nodeValue1737, nodeValue2702, nodeValue3288, nodeValue3293, nodeValue3308, nodeValue4069]

noncomputable def reducedSource1373 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1373 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 1132, 1), (Sum.inr 1134, 1), (Sum.inr 1141, 1), (Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1373 : Integer.Sparse.reindex keyMap MixedData.row1373 = numericRow1373 := by decide +kernel

theorem numericCheck1373 (x : Master → ℝ) : Integer.Sparse.eval numericRow1373 x =
    (1 : ℝ) * reducedSource1373 x := by
  norm_num [numericRow1373, reducedSource1373, Integer.Sparse.eval, Sparse.eval, nodeValue1127, nodeValue1132, nodeValue1134, nodeValue1141, nodeValue1237, nodeValue2512, nodeValue4092]

noncomputable def reducedSource1374 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1374 : Integer.Sparse Master := [(Sum.inr 640, 1), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 2), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1374 : Integer.Sparse.reindex keyMap MixedData.row1374 = numericRow1374 := by decide +kernel

theorem numericCheck1374 (x : Master → ℝ) : Integer.Sparse.eval numericRow1374 x =
    (1 : ℝ) * reducedSource1374 x := by
  norm_num [numericRow1374, reducedSource1374, Integer.Sparse.eval, Sparse.eval, nodeValue640, nodeValue1158, nodeValue1240, nodeValue1262, nodeValue1293, nodeValue4091]

noncomputable def reducedSource1375 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1375 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1645, 1), (Sum.inr 1646, 1), (Sum.inr 1649, 1), (Sum.inr 1724, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1375 : Integer.Sparse.reindex keyMap MixedData.row1375 = numericRow1375 := by decide +kernel

theorem numericCheck1375 (x : Master → ℝ) : Integer.Sparse.eval numericRow1375 x =
    (1 : ℝ) * reducedSource1375 x := by
  norm_num [numericRow1375, reducedSource1375, Integer.Sparse.eval, Sparse.eval, nodeValue1642, nodeValue1645, nodeValue1646, nodeValue1649, nodeValue1724, nodeValue3294, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
