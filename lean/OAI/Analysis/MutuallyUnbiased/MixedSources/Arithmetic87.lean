import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1392 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((2 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1392 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1117, 2), (Sum.inr 1135, 1), (Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1392 : Integer.Sparse.reindex keyMap MixedData.row1392 = numericRow1392 := by decide +kernel

theorem numericCheck1392 (x : Master → ℝ) : Integer.Sparse.eval numericRow1392 x =
    (1 : ℝ) * reducedSource1392 x := by
  norm_num [numericRow1392, reducedSource1392, Integer.Sparse.eval, Sparse.eval, nodeValue1116, nodeValue1117, nodeValue1135, nodeValue1216, nodeValue2483, nodeValue4091]

noncomputable def reducedSource1393 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1393 : Integer.Sparse Master := [(Sum.inr 1607, 2), (Sum.inr 1609, 1), (Sum.inr 1616, 1), (Sum.inr 1737, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1393 : Integer.Sparse.reindex keyMap MixedData.row1393 = numericRow1393 := by decide +kernel

theorem numericCheck1393 (x : Master → ℝ) : Integer.Sparse.eval numericRow1393 x =
    (1 : ℝ) * reducedSource1393 x := by
  norm_num [numericRow1393, reducedSource1393, Integer.Sparse.eval, Sparse.eval, nodeValue1607, nodeValue1609, nodeValue1616, nodeValue1737, nodeValue3288, nodeValue4069]

noncomputable def reducedSource1394 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1592 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1394 : Integer.Sparse Master := [(Sum.inr 1594, 1), (Sum.inr 1597, 2), (Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1394 : Integer.Sparse.reindex keyMap MixedData.row1394 = numericRow1394 := by decide +kernel

theorem numericCheck1394 (x : Master → ℝ) : Integer.Sparse.eval numericRow1394 x =
    (1 : ℝ) * reducedSource1394 x := by
  norm_num [numericRow1394, reducedSource1394, Integer.Sparse.eval, Sparse.eval, nodeValue1592, nodeValue1594, nodeValue1597, nodeValue1707, nodeValue3288, nodeValue4069]

noncomputable def reducedSource1395 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1395 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 3238, 1), (Sum.inr 3285, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1395 : Integer.Sparse.reindex keyMap MixedData.row1395 = numericRow1395 := by decide +kernel

theorem numericCheck1395 (x : Master → ℝ) : Integer.Sparse.eval numericRow1395 x =
    (1 : ℝ) * reducedSource1395 x := by
  norm_num [numericRow1395, reducedSource1395, Integer.Sparse.eval, Sparse.eval, nodeValue1597, nodeValue3238, nodeValue3285, nodeValue3288, nodeValue3290, nodeValue3293, nodeValue4069]

noncomputable def reducedSource1396 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1396 : Integer.Sparse Master := [(Sum.inr 1616, 1), (Sum.inr 3241, 1), (Sum.inr 3288, 1), (Sum.inr 3290, 2), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1396 : Integer.Sparse.reindex keyMap MixedData.row1396 = numericRow1396 := by decide +kernel

theorem numericCheck1396 (x : Master → ℝ) : Integer.Sparse.eval numericRow1396 x =
    (1 : ℝ) * reducedSource1396 x := by
  norm_num [numericRow1396, reducedSource1396, Integer.Sparse.eval, Sparse.eval, nodeValue1616, nodeValue3241, nodeValue3288, nodeValue3290, nodeValue3299, nodeValue4069]

noncomputable def reducedSource1397 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1114 x + ((1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1397 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1114, 1), (Sum.inr 1117, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1397 : Integer.Sparse.reindex keyMap MixedData.row1397 = numericRow1397 := by decide +kernel

theorem numericCheck1397 (x : Master → ℝ) : Integer.Sparse.eval numericRow1397 x =
    (1 : ℝ) * reducedSource1397 x := by
  norm_num [numericRow1397, reducedSource1397, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue1114, nodeValue1117, nodeValue1129, nodeValue1213, nodeValue2480, nodeValue4091]

noncomputable def reducedSource1398 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1398 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 1129, 1), (Sum.inr 1213, 2), (Sum.inr 1235, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1398 : Integer.Sparse.reindex keyMap MixedData.row1398 = numericRow1398 := by decide +kernel

theorem numericCheck1398 (x : Master → ℝ) : Integer.Sparse.eval numericRow1398 x =
    (1 : ℝ) * reducedSource1398 x := by
  norm_num [numericRow1398, reducedSource1398, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue1129, nodeValue1213, nodeValue1235, nodeValue1240, nodeValue4091]

noncomputable def reducedSource1399 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1597 x + ((1 : ℝ) * Sparse.eval nodeValue1598 x + ((1 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1616 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue3290 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1399 : Integer.Sparse Master := [(Sum.inr 1597, 1), (Sum.inr 1601, 1), (Sum.inr 1616, 1), (Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1399 : Integer.Sparse.reindex keyMap MixedData.row1399 = numericRow1399 := by decide +kernel

theorem numericCheck1399 (x : Master → ℝ) : Integer.Sparse.eval numericRow1399 x =
    (1 : ℝ) * reducedSource1399 x := by
  norm_num [numericRow1399, reducedSource1399, Integer.Sparse.eval, Sparse.eval, nodeValue1597, nodeValue1598, nodeValue1601, nodeValue1616, nodeValue1724, nodeValue3290, nodeValue4069]

noncomputable def reducedSource1400 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

def numericRow1400 : Integer.Sparse Master := [(Sum.inr 1210, 1), (Sum.inr 2477, 1), (Sum.inr 2613, 1), (Sum.inr 2694, 1), (Sum.inr 2708, 1), (Sum.inr 2718, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1400 : Integer.Sparse.reindex keyMap MixedData.row1400 = numericRow1400 := by decide +kernel

theorem numericCheck1400 (x : Master → ℝ) : Integer.Sparse.eval numericRow1400 x =
    (1 : ℝ) * reducedSource1400 x := by
  norm_num [numericRow1400, reducedSource1400, Integer.Sparse.eval, Sparse.eval, nodeValue1210, nodeValue2477, nodeValue2613, nodeValue2694, nodeValue2708, nodeValue2718, nodeValue4090]

noncomputable def reducedSource1401 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((2 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))))

def numericRow1401 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 2383, 1), (Sum.inr 2607, 1), (Sum.inr 2662, 2), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

theorem reindexCheck1401 : Integer.Sparse.reindex keyMap MixedData.row1401 = numericRow1401 := by decide +kernel

theorem numericCheck1401 (x : Master → ℝ) : Integer.Sparse.eval numericRow1401 x =
    (1 : ℝ) * reducedSource1401 x := by
  norm_num [numericRow1401, reducedSource1401, Integer.Sparse.eval, Sparse.eval, nodeValue1180, nodeValue2383, nodeValue2607, nodeValue2662, nodeValue2671, nodeValue4087]

noncomputable def reducedSource1402 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue1256 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))

def numericRow1402 : Integer.Sparse Master := [(Sum.inr 1180, 3), (Sum.inr 1187, 1), (Sum.inr 1256, 1), (Sum.inr 2671, 1), (Sum.inr 4087, -1)]

theorem reindexCheck1402 : Integer.Sparse.reindex keyMap MixedData.row1402 = numericRow1402 := by decide +kernel

theorem numericCheck1402 (x : Master → ℝ) : Integer.Sparse.eval numericRow1402 x =
    (1 : ℝ) * reducedSource1402 x := by
  norm_num [numericRow1402, reducedSource1402, Integer.Sparse.eval, Sparse.eval, nodeValue1180, nodeValue1187, nodeValue1256, nodeValue2671, nodeValue4087]

noncomputable def reducedSource1403 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1403 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 2382, 1), (Sum.inr 2606, 1), (Sum.inr 2661, 1), (Sum.inr 2669, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1403 : Integer.Sparse.reindex keyMap MixedData.row1403 = numericRow1403 := by decide +kernel

theorem numericCheck1403 (x : Master → ℝ) : Integer.Sparse.eval numericRow1403 x =
    (1 : ℝ) * reducedSource1403 x := by
  norm_num [numericRow1403, reducedSource1403, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue2382, nodeValue2606, nodeValue2661, nodeValue2669, nodeValue2672, nodeValue4088]

noncomputable def reducedSource1404 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1404 : Integer.Sparse Master := [(Sum.inr 1656, 2), (Sum.inr 1659, 1), (Sum.inr 1661, 1), (Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1404 : Integer.Sparse.reindex keyMap MixedData.row1404 = numericRow1404 := by decide +kernel

theorem numericCheck1404 (x : Master → ℝ) : Integer.Sparse.eval numericRow1404 x =
    (1 : ℝ) * reducedSource1404 x := by
  norm_num [numericRow1404, reducedSource1404, Integer.Sparse.eval, Sparse.eval, nodeValue1656, nodeValue1659, nodeValue1661, nodeValue1739, nodeValue2737, nodeValue4069]

noncomputable def reducedSource1405 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1650 x + ((2 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1405 : Integer.Sparse Master := [(Sum.inr 1650, 1), (Sum.inr 2502, 2), (Sum.inr 2521, 1), (Sum.inr 2737, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1405 : Integer.Sparse.reindex keyMap MixedData.row1405 = numericRow1405 := by decide +kernel

theorem numericCheck1405 (x : Master → ℝ) : Integer.Sparse.eval numericRow1405 x =
    (1 : ℝ) * reducedSource1405 x := by
  norm_num [numericRow1405, reducedSource1405, Integer.Sparse.eval, Sparse.eval, nodeValue1650, nodeValue2502, nodeValue2521, nodeValue2737, nodeValue3305, nodeValue4069]

noncomputable def reducedSource1406 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1406 : Integer.Sparse Master := [(Sum.inr 1646, 2), (Sum.inr 1651, 1), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1406 : Integer.Sparse.reindex keyMap MixedData.row1406 = numericRow1406 := by decide +kernel

theorem numericCheck1406 (x : Master → ℝ) : Integer.Sparse.eval numericRow1406 x =
    (1 : ℝ) * reducedSource1406 x := by
  norm_num [numericRow1406, reducedSource1406, Integer.Sparse.eval, Sparse.eval, nodeValue1646, nodeValue1651, nodeValue1653, nodeValue1728, nodeValue3306, nodeValue4069]

noncomputable def reducedSource1407 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((2 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1407 : Integer.Sparse Master := [(Sum.inr 1653, 1), (Sum.inr 3049, 1), (Sum.inr 3287, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1407 : Integer.Sparse.reindex keyMap MixedData.row1407 = numericRow1407 := by decide +kernel

theorem numericCheck1407 (x : Master → ℝ) : Integer.Sparse.eval numericRow1407 x =
    (1 : ℝ) * reducedSource1407 x := by
  norm_num [numericRow1407, reducedSource1407, Integer.Sparse.eval, Sparse.eval, nodeValue1653, nodeValue3049, nodeValue3287, nodeValue3305, nodeValue3306, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
