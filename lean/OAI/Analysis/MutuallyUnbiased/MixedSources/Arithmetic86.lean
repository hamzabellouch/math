import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1376 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1603 x + ((1 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1376 : Integer.Sparse Master := [(Sum.inr 1603, 1), (Sum.inr 1605, 1), (Sum.inr 1623, 1), (Sum.inr 1728, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1376 : Integer.Sparse.reindex keyMap MixedData.row1376 = numericRow1376 := by decide +kernel

theorem numericCheck1376 (x : Master → ℝ) : Integer.Sparse.eval numericRow1376 x =
    (1 : ℝ) * reducedSource1376 x := by
  norm_num [numericRow1376, reducedSource1376, Integer.Sparse.eval, Sparse.eval, nodeValue1598, nodeValue1603, nodeValue1605, nodeValue1623, nodeValue1728, nodeValue3294, nodeValue4069]

noncomputable def reducedSource1377 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1728 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1377 : Integer.Sparse Master := [(Sum.inr 1728, 1), (Sum.inr 3294, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1377 : Integer.Sparse.reindex keyMap MixedData.row1377 = numericRow1377 := by decide +kernel

theorem numericCheck1377 (x : Master → ℝ) : Integer.Sparse.eval numericRow1377 x =
    (1 : ℝ) * reducedSource1377 x := by
  norm_num [numericRow1377, reducedSource1377, Integer.Sparse.eval, Sparse.eval, nodeValue1728, nodeValue3294, nodeValue3305, nodeValue3306, nodeValue3309, nodeValue4069]

noncomputable def reducedSource1378 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1378 : Integer.Sparse Master := [(Sum.inr 1623, 1), (Sum.inr 3246, 1), (Sum.inr 3282, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1378 : Integer.Sparse.reindex keyMap MixedData.row1378 = numericRow1378 := by decide +kernel

theorem numericCheck1378 (x : Master → ℝ) : Integer.Sparse.eval numericRow1378 x =
    (1 : ℝ) * reducedSource1378 x := by
  norm_num [numericRow1378, reducedSource1378, Integer.Sparse.eval, Sparse.eval, nodeValue1623, nodeValue3246, nodeValue3282, nodeValue3294, nodeValue3296, nodeValue3299, nodeValue4069]

noncomputable def reducedSource1379 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1379 : Integer.Sparse Master := [(Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3299, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1379 : Integer.Sparse.reindex keyMap MixedData.row1379 = numericRow1379 := by decide +kernel

theorem numericCheck1379 (x : Master → ℝ) : Integer.Sparse.eval numericRow1379 x =
    (1 : ℝ) * reducedSource1379 x := by
  norm_num [numericRow1379, reducedSource1379, Integer.Sparse.eval, Sparse.eval, nodeValue1724, nodeValue3290, nodeValue3293, nodeValue3294, nodeValue3299, nodeValue3309, nodeValue4069]

noncomputable def reducedSource1380 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1380 : Integer.Sparse Master := [(Sum.inr 1605, 1), (Sum.inr 3240, 1), (Sum.inr 3278, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1380 : Integer.Sparse.reindex keyMap MixedData.row1380 = numericRow1380 := by decide +kernel

theorem numericCheck1380 (x : Master → ℝ) : Integer.Sparse.eval numericRow1380 x =
    (1 : ℝ) * reducedSource1380 x := by
  norm_num [numericRow1380, reducedSource1380, Integer.Sparse.eval, Sparse.eval, nodeValue1605, nodeValue3240, nodeValue3278, nodeValue3287, nodeValue3293, nodeValue3294, nodeValue4069]

noncomputable def reducedSource1381 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue3022 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1381 : Integer.Sparse Master := [(Sum.inr 1645, 1), (Sum.inr 3022, 1), (Sum.inr 3285, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1381 : Integer.Sparse.reindex keyMap MixedData.row1381 = numericRow1381 := by decide +kernel

theorem numericCheck1381 (x : Master → ℝ) : Integer.Sparse.eval numericRow1381 x =
    (1 : ℝ) * reducedSource1381 x := by
  norm_num [numericRow1381, reducedSource1381, Integer.Sparse.eval, Sparse.eval, nodeValue1645, nodeValue3022, nodeValue3285, nodeValue3294, nodeValue3296, nodeValue3305, nodeValue4069]

noncomputable def reducedSource1382 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1257 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2760 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1382 : Integer.Sparse Master := [(Sum.inr 1257, 1), (Sum.inr 2565, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 2748, 1), (Sum.inr 2760, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1382 : Integer.Sparse.reindex keyMap MixedData.row1382 = numericRow1382 := by decide +kernel

theorem numericCheck1382 (x : Master → ℝ) : Integer.Sparse.eval numericRow1382 x =
    (1 : ℝ) * reducedSource1382 x := by
  norm_num [numericRow1382, reducedSource1382, Integer.Sparse.eval, Sparse.eval, nodeValue1257, nodeValue2565, nodeValue2629, nodeValue2672, nodeValue2748, nodeValue2760, nodeValue4088]

noncomputable def reducedSource1383 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1383 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 1137, 1), (Sum.inr 1138, 1), (Sum.inr 1141, 1), (Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1383 : Integer.Sparse.reindex keyMap MixedData.row1383 = numericRow1383 := by decide +kernel

theorem numericCheck1383 (x : Master → ℝ) : Integer.Sparse.eval numericRow1383 x =
    (1 : ℝ) * reducedSource1383 x := by
  norm_num [numericRow1383, reducedSource1383, Integer.Sparse.eval, Sparse.eval, nodeValue1130, nodeValue1137, nodeValue1138, nodeValue1141, nodeValue1241, nodeValue2515, nodeValue4092]

noncomputable def reducedSource1384 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1384 : Integer.Sparse Master := [(Sum.inr 638, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 1291, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1384 : Integer.Sparse.reindex keyMap MixedData.row1384 = numericRow1384 := by decide +kernel

theorem numericCheck1384 (x : Master → ℝ) : Integer.Sparse.eval numericRow1384 x =
    (1 : ℝ) * reducedSource1384 x := by
  norm_num [numericRow1384, reducedSource1384, Integer.Sparse.eval, Sparse.eval, nodeValue638, nodeValue1156, nodeValue1236, nodeValue1261, nodeValue1291, nodeValue1294, nodeValue4092]

noncomputable def reducedSource1385 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1635 x + ((1 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1385 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1637, 1), (Sum.inr 1640, 1), (Sum.inr 1645, 1), (Sum.inr 1707, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1385 : Integer.Sparse.reindex keyMap MixedData.row1385 = numericRow1385 := by decide +kernel

theorem numericCheck1385 (x : Master → ℝ) : Integer.Sparse.eval numericRow1385 x =
    (1 : ℝ) * reducedSource1385 x := by
  norm_num [numericRow1385, reducedSource1385, Integer.Sparse.eval, Sparse.eval, nodeValue1635, nodeValue1637, nodeValue1640, nodeValue1645, nodeValue1707, nodeValue3296, nodeValue4069]

noncomputable def reducedSource1386 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1623 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1386 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1610, 1), (Sum.inr 1612, 1), (Sum.inr 1623, 1), (Sum.inr 1739, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1386 : Integer.Sparse.reindex keyMap MixedData.row1386 = numericRow1386 := by decide +kernel

theorem numericCheck1386 (x : Master → ℝ) : Integer.Sparse.eval numericRow1386 x =
    (1 : ℝ) * reducedSource1386 x := by
  norm_num [numericRow1386, reducedSource1386, Integer.Sparse.eval, Sparse.eval, nodeValue1607, nodeValue1610, nodeValue1612, nodeValue1623, nodeValue1739, nodeValue3296, nodeValue4069]

noncomputable def reducedSource1387 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1387 : Integer.Sparse Master := [(Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 3296, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1387 : Integer.Sparse.reindex keyMap MixedData.row1387 = numericRow1387 := by decide +kernel

theorem numericCheck1387 (x : Master → ℝ) : Integer.Sparse.eval numericRow1387 x =
    (1 : ℝ) * reducedSource1387 x := by
  norm_num [numericRow1387, reducedSource1387, Integer.Sparse.eval, Sparse.eval, nodeValue1739, nodeValue2737, nodeValue3296, nodeValue3305, nodeValue3308, nodeValue4069]

noncomputable def reducedSource1388 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1388 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 3296, 2), (Sum.inr 3299, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1388 : Integer.Sparse.reindex keyMap MixedData.row1388 = numericRow1388 := by decide +kernel

theorem numericCheck1388 (x : Master → ℝ) : Integer.Sparse.eval numericRow1388 x =
    (1 : ℝ) * reducedSource1388 x := by
  norm_num [numericRow1388, reducedSource1388, Integer.Sparse.eval, Sparse.eval, nodeValue1707, nodeValue3288, nodeValue3296, nodeValue3299, nodeValue3308, nodeValue4069]

noncomputable def reducedSource1389 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((2 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1389 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1113, 2), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1389 : Integer.Sparse.reindex keyMap MixedData.row1389 = numericRow1389 := by decide +kernel

theorem numericCheck1389 (x : Master → ℝ) : Integer.Sparse.eval numericRow1389 x =
    (1 : ℝ) * reducedSource1389 x := by
  norm_num [numericRow1389, reducedSource1389, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue1113, nodeValue1126, nodeValue1212, nodeValue2479, nodeValue4092]

noncomputable def reducedSource1390 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue623 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1390 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 1233, 1), (Sum.inr 1236, 2), (Sum.inr 4092, -1)]

theorem reindexCheck1390 : Integer.Sparse.reindex keyMap MixedData.row1390 = numericRow1390 := by decide +kernel

theorem numericCheck1390 (x : Master → ℝ) : Integer.Sparse.eval numericRow1390 x =
    (1 : ℝ) * reducedSource1390 x := by
  norm_num [numericRow1390, reducedSource1390, Integer.Sparse.eval, Sparse.eval, nodeValue623, nodeValue1126, nodeValue1212, nodeValue1233, nodeValue1236, nodeValue4092]

noncomputable def reducedSource1391 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((3 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1391 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 1135, 1), (Sum.inr 1216, 3), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1391 : Integer.Sparse.reindex keyMap MixedData.row1391 = numericRow1391 := by decide +kernel

theorem numericCheck1391 (x : Master → ℝ) : Integer.Sparse.eval numericRow1391 x =
    (1 : ℝ) * reducedSource1391 x := by
  norm_num [numericRow1391, reducedSource1391, Integer.Sparse.eval, Sparse.eval, nodeValue629, nodeValue1135, nodeValue1216, nodeValue1235, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
