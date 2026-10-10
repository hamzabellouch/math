import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1552 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1638 x + ((1 : ℝ) * Sparse.eval nodeValue1644 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1552 : Integer.Sparse Master := [(Sum.inr 1636, 2), (Sum.inr 1638, 1), (Sum.inr 1644, 1), (Sum.inr 1706, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1552 : Integer.Sparse.reindex keyMap MixedData.row1552 = numericRow1552 := by decide +kernel

theorem numericCheck1552 (x : Master → ℝ) : Integer.Sparse.eval numericRow1552 x =
    (1 : ℝ) * reducedSource1552 x := by
  norm_num [numericRow1552, reducedSource1552, Integer.Sparse.eval, Sparse.eval, nodeValue1636, nodeValue1638, nodeValue1644, nodeValue1706, nodeValue3289, nodeValue4068]

noncomputable def reducedSource1553 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1593 x + ((1 : ℝ) * Sparse.eval nodeValue1595 x + ((2 : ℝ) * Sparse.eval nodeValue1600 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1553 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1600, 2), (Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1553 : Integer.Sparse.reindex keyMap MixedData.row1553 = numericRow1553 := by decide +kernel

theorem numericCheck1553 (x : Master → ℝ) : Integer.Sparse.eval numericRow1553 x =
    (1 : ℝ) * reducedSource1553 x := by
  norm_num [numericRow1553, reducedSource1553, Integer.Sparse.eval, Sparse.eval, nodeValue1593, nodeValue1595, nodeValue1600, nodeValue1708, nodeValue3289, nodeValue4068]

noncomputable def reducedSource1554 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3307 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1554 : Integer.Sparse Master := [(Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1554 : Integer.Sparse.reindex keyMap MixedData.row1554 = numericRow1554 := by decide +kernel

theorem numericCheck1554 (x : Master → ℝ) : Integer.Sparse.eval numericRow1554 x =
    (1 : ℝ) * reducedSource1554 x := by
  norm_num [numericRow1554, reducedSource1554, Integer.Sparse.eval, Sparse.eval, nodeValue1708, nodeValue3289, nodeValue3303, nodeValue3304, nodeValue3307, nodeValue4068]

noncomputable def reducedSource1555 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1600 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1555 : Integer.Sparse Master := [(Sum.inr 1600, 1), (Sum.inr 3239, 1), (Sum.inr 3286, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1555 : Integer.Sparse.reindex keyMap MixedData.row1555 = numericRow1555 := by decide +kernel

theorem numericCheck1555 (x : Master → ℝ) : Integer.Sparse.eval numericRow1555 x =
    (1 : ℝ) * reducedSource1555 x := by
  norm_num [numericRow1555, reducedSource1555, Integer.Sparse.eval, Sparse.eval, nodeValue1600, nodeValue3239, nodeValue3286, nodeValue3289, nodeValue3292, nodeValue4068]

noncomputable def reducedSource1556 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3292 x + ((1 : ℝ) * Sparse.eval nodeValue3307 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1556 : Integer.Sparse Master := [(Sum.inr 1706, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 2), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1556 : Integer.Sparse.reindex keyMap MixedData.row1556 = numericRow1556 := by decide +kernel

theorem numericCheck1556 (x : Master → ℝ) : Integer.Sparse.eval numericRow1556 x =
    (1 : ℝ) * reducedSource1556 x := by
  norm_num [numericRow1556, reducedSource1556, Integer.Sparse.eval, Sparse.eval, nodeValue1706, nodeValue3289, nodeValue3292, nodeValue3307, nodeValue4068]

noncomputable def reducedSource1557 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue3072 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1557 : Integer.Sparse Master := [(Sum.inr 1648, 1), (Sum.inr 3072, 1), (Sum.inr 3286, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1557 : Integer.Sparse.reindex keyMap MixedData.row1557 = numericRow1557 := by decide +kernel

theorem numericCheck1557 (x : Master → ℝ) : Integer.Sparse.eval numericRow1557 x =
    (1 : ℝ) * reducedSource1557 x := by
  norm_num [numericRow1557, reducedSource1557, Integer.Sparse.eval, Sparse.eval, nodeValue1648, nodeValue3072, nodeValue3286, nodeValue3303, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1558 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1641 x + ((1 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))))

def numericRow1558 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1639, 1), (Sum.inr 1641, 1), (Sum.inr 1648, 1), (Sum.inr 1708, 1), (Sum.inr 3303, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1558 : Integer.Sparse.reindex keyMap MixedData.row1558 = numericRow1558 := by decide +kernel

theorem numericCheck1558 (x : Master → ℝ) : Integer.Sparse.eval numericRow1558 x =
    (1 : ℝ) * reducedSource1558 x := by
  norm_num [numericRow1558, reducedSource1558, Integer.Sparse.eval, Sparse.eval, nodeValue1636, nodeValue1639, nodeValue1641, nodeValue1648, nodeValue1708, nodeValue3303, nodeValue4068]

noncomputable def reducedSource1559 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4164 x + ((3 : ℝ) * Sparse.eval nodeValue4165 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((3 : ℝ) * Sparse.eval nodeValue4537 x + ((1 : ℝ) * Sparse.eval nodeValue4550 x + ((1 : ℝ) * Sparse.eval nodeValue4569 x + ((3 : ℝ) * Sparse.eval nodeValue4570 x + ((3 : ℝ) * Sparse.eval nodeValue4618 x + ((6 : ℝ) * Sparse.eval nodeValue4619 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))

def numericRow1559 : Integer.Sparse Master := [(Sum.inl 0, 34), (Sum.inl 6, 5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 170), (Sum.inr 592, -720), (Sum.inr 593, -2160), (Sum.inr 610, -720), (Sum.inr 1122, -2160), (Sum.inr 1135, -720), (Sum.inr 1187, -720), (Sum.inr 1188, -2160), (Sum.inr 1293, -2160), (Sum.inr 1294, -4320), (Sum.inr 1497, -720), (Sum.inr 1498, -2160), (Sum.inr 1524, -720), (Sum.inr 3053, -720), (Sum.inr 3244, -720), (Sum.inr 3245, -2160), (Sum.inr 3253, -2160), (Sum.inr 3269, -720), (Sum.inr 3304, -2160), (Sum.inr 3305, -4320), (Sum.inr 3308, -2160), (Sum.inr 3619, -720), (Sum.inr 3623, -2160)]

theorem reindexCheck1559 : Integer.Sparse.reindex keyMap MixedData.row1559 = numericRow1559 := by decide +kernel

theorem numericCheck1559 (x : Master → ℝ) : Integer.Sparse.eval numericRow1559 x =
    (2880 : ℝ) * reducedSource1559 x := by
  norm_num [numericRow1559, reducedSource1559, Integer.Sparse.eval, Sparse.eval, nodeValue4164, nodeValue4165, nodeValue4182, nodeValue4537, nodeValue4550, nodeValue4569, nodeValue4570, nodeValue4618, nodeValue4619, nodeValue4623, nodeValue5166, nodeValue5301, nodeValue5306]; ring

noncomputable def reducedSource1560 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue592 x + ((3 : ℝ) * Sparse.eval nodeValue593 x + ((1 : ℝ) * Sparse.eval nodeValue610 x + ((3 : ℝ) * Sparse.eval nodeValue1122 x + ((1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((3 : ℝ) * Sparse.eval nodeValue1188 x + ((3 : ℝ) * Sparse.eval nodeValue1293 x + ((6 : ℝ) * Sparse.eval nodeValue1294 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue2953 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((3 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))

def numericRow1560 : Integer.Sparse Master := [(Sum.inl 0, -34), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -170), (Sum.inr 592, 720), (Sum.inr 593, 2160), (Sum.inr 610, 720), (Sum.inr 1122, 2160), (Sum.inr 1135, 720), (Sum.inr 1187, 720), (Sum.inr 1188, 2160), (Sum.inr 1293, 2160), (Sum.inr 1294, 4320), (Sum.inr 3053, 720)]

theorem reindexCheck1560 : Integer.Sparse.reindex keyMap MixedData.row1560 = numericRow1560 := by decide +kernel

theorem numericCheck1560 (x : Master → ℝ) : Integer.Sparse.eval numericRow1560 x =
    (720 : ℝ) * reducedSource1560 x := by
  norm_num [numericRow1560, reducedSource1560, Integer.Sparse.eval, Sparse.eval, nodeValue592, nodeValue593, nodeValue610, nodeValue1122, nodeValue1135, nodeValue1187, nodeValue1188, nodeValue1293, nodeValue1294, nodeValue1305, nodeValue2953, nodeValue3053, nodeValue3120]; ring

noncomputable def reducedSource1561 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4169 x + ((1 : ℝ) * Sparse.eval nodeValue4170 x + ((3 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4540 x + ((3 : ℝ) * Sparse.eval nodeValue4542 x + ((3 : ℝ) * Sparse.eval nodeValue4599 x + ((3 : ℝ) * Sparse.eval nodeValue4600 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue4603 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + 0))))))))))))

def numericRow1561 : Integer.Sparse Master := [(Sum.inr 1235, -1), (Sum.inr 1240, -3), (Sum.inr 2589, -1), (Sum.inr 2764, -3), (Sum.inr 3292, -1), (Sum.inr 3299, -3), (Sum.inr 3563, -1), (Sum.inr 3581, -3), (Sum.inr 4169, 4), (Sum.inr 4170, 4), (Sum.inr 4173, 12), (Sum.inr 4540, 4), (Sum.inr 4542, 12), (Sum.inr 4599, 12), (Sum.inr 4600, 12), (Sum.inr 4603, 24)]

theorem reindexCheck1561 : Integer.Sparse.reindex keyMap MixedData.row1561 = numericRow1561 := by decide +kernel

theorem numericCheck1561 (x : Master → ℝ) : Integer.Sparse.eval numericRow1561 x =
    (4 : ℝ) * reducedSource1561 x := by
  norm_num [numericRow1561, reducedSource1561, Integer.Sparse.eval, Sparse.eval, nodeValue4169, nodeValue4170, nodeValue4173, nodeValue4540, nodeValue4542, nodeValue4599, nodeValue4600, nodeValue4601, nodeValue4603, nodeValue4606, nodeValue5162, nodeValue5273, nodeValue5290]; ring

noncomputable def reducedSource1562 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue598 x + ((3 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue1125 x + ((3 : ℝ) * Sparse.eval nodeValue1127 x + ((3 : ℝ) * Sparse.eval nodeValue1233 x + ((3 : ℝ) * Sparse.eval nodeValue1234 x + ((6 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((3 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue2957 x + ((3 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))

def numericRow1562 : Integer.Sparse Master := [(Sum.inl 0, -80), (Sum.inl 5, 40), (Sum.inl 6, -15), (Sum.inl 2, 25), (Sum.inl 7, 240), (Sum.inl 35, 160), (Sum.inl 3, 240), (Sum.inl 1, -100), (Sum.inr 597, 2160), (Sum.inr 598, 2160), (Sum.inr 601, 6480), (Sum.inr 1125, 2160), (Sum.inr 1127, 6480), (Sum.inr 1233, 6480), (Sum.inr 1234, 6480), (Sum.inr 1237, 12960)]

theorem reindexCheck1562 : Integer.Sparse.reindex keyMap MixedData.row1562 = numericRow1562 := by decide +kernel

theorem numericCheck1562 (x : Master → ℝ) : Integer.Sparse.eval numericRow1562 x =
    (2160 : ℝ) * reducedSource1562 x := by
  norm_num [numericRow1562, reducedSource1562, Integer.Sparse.eval, Sparse.eval, nodeValue597, nodeValue598, nodeValue601, nodeValue1125, nodeValue1127, nodeValue1233, nodeValue1234, nodeValue1237, nodeValue1265, nodeValue1266, nodeValue2957, nodeValue3099, nodeValue3111]; ring

noncomputable def reducedSource1563 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1502 x + ((1 : ℝ) * Sparse.eval nodeValue1503 x + ((3 : ℝ) * Sparse.eval nodeValue1508 x + ((1 : ℝ) * Sparse.eval nodeValue2688 x + ((3 : ℝ) * Sparse.eval nodeValue2702 x + ((3 : ℝ) * Sparse.eval nodeValue3257 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((6 : ℝ) * Sparse.eval nodeValue3294 x + ((3 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((3 : ℝ) * Sparse.eval nodeValue3581 x + 0))))))))))))

def numericRow1563 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1503, 1), (Sum.inr 1508, 3), (Sum.inr 2688, 1), (Sum.inr 2702, 3), (Sum.inr 3257, 3), (Sum.inr 3289, 3), (Sum.inr 3292, 1), (Sum.inr 3294, 6), (Sum.inr 3299, 3), (Sum.inr 3563, 1), (Sum.inr 3581, 3)]

theorem reindexCheck1563 : Integer.Sparse.reindex keyMap MixedData.row1563 = numericRow1563 := by decide +kernel

theorem numericCheck1563 (x : Master → ℝ) : Integer.Sparse.eval numericRow1563 x =
    (1 : ℝ) * reducedSource1563 x := by
  norm_num [numericRow1563, reducedSource1563, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1503, nodeValue1508, nodeValue2688, nodeValue2702, nodeValue3257, nodeValue3289, nodeValue3292, nodeValue3294, nodeValue3299, nodeValue3546, nodeValue3563, nodeValue3581]

noncomputable def reducedSource1564 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue637 x + ((3 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1564 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 640, 3), (Sum.inr 651, 1), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1564 : Integer.Sparse.reindex keyMap MixedData.row1564 = numericRow1564 := by decide +kernel

theorem numericCheck1564 (x : Master → ℝ) : Integer.Sparse.eval numericRow1564 x =
    (1 : ℝ) * reducedSource1564 x := by
  norm_num [numericRow1564, reducedSource1564, Integer.Sparse.eval, Sparse.eval, nodeValue637, nodeValue640, nodeValue651, nodeValue1293, nodeValue4091]

noncomputable def reducedSource1565 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((3 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((3 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue1256 x + ((3 : ℝ) * Sparse.eval nodeValue1260 x + ((3 : ℝ) * Sparse.eval nodeValue1286 x + ((6 : ℝ) * Sparse.eval nodeValue1291 x + ((3 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((1 : ℝ) * Sparse.eval nodeValue1435 x + ((3 : ℝ) * Sparse.eval nodeValue1441 x + 0))))))))))))

def numericRow1565 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 35, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 52, -160), (Sum.inl 1, 115), (Sum.inr 1034, 1440), (Sum.inr 1073, 4320), (Sum.inr 1228, 4320), (Sum.inr 1235, 1440), (Sum.inr 1256, 1440), (Sum.inr 1260, 4320), (Sum.inr 1286, 4320), (Sum.inr 1291, 8640), (Sum.inr 1435, 1440)]

theorem reindexCheck1565 : Integer.Sparse.reindex keyMap MixedData.row1565 = numericRow1565 := by decide +kernel

theorem numericCheck1565 (x : Master → ℝ) : Integer.Sparse.eval numericRow1565 x =
    (1440 : ℝ) * reducedSource1565 x := by
  norm_num [numericRow1565, reducedSource1565, Integer.Sparse.eval, Sparse.eval, nodeValue1034, nodeValue1073, nodeValue1081, nodeValue1228, nodeValue1235, nodeValue1256, nodeValue1260, nodeValue1286, nodeValue1291, nodeValue1299, nodeValue1405, nodeValue1435, nodeValue1441]; ring

noncomputable def reducedSource1566 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1644 x + ((3 : ℝ) * Sparse.eval nodeValue1648 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1566 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 1648, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1566 : Integer.Sparse.reindex keyMap MixedData.row1566 = numericRow1566 := by decide +kernel

theorem numericCheck1566 (x : Master → ℝ) : Integer.Sparse.eval numericRow1566 x =
    (1 : ℝ) * reducedSource1566 x := by
  norm_num [numericRow1566, reducedSource1566, Integer.Sparse.eval, Sparse.eval, nodeValue1644, nodeValue1648, nodeValue1726, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1567 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4171 x + ((2 : ℝ) * Sparse.eval nodeValue4172 x + ((2 : ℝ) * Sparse.eval nodeValue4175 x + ((2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4623 x + ((4 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))

def numericRow1567 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 15), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 1, -110), (Sum.inr 599, -1440), (Sum.inr 600, -2880), (Sum.inr 603, -2880), (Sum.inr 1126, -2880), (Sum.inr 1129, -2880), (Sum.inr 1235, -2880), (Sum.inr 1236, -5760), (Sum.inr 1240, -2880), (Sum.inr 1506, -1440), (Sum.inr 1507, -2880), (Sum.inr 1517, -2880), (Sum.inr 3256, -2880), (Sum.inr 3263, -2880), (Sum.inr 3292, -2880), (Sum.inr 3293, -5760), (Sum.inr 3299, -2880), (Sum.inr 3307, -2880), (Sum.inr 3308, -2880), (Sum.inr 3309, -5760), (Sum.inr 3602, -1440), (Sum.inr 3622, -2880)]

theorem reindexCheck1567 : Integer.Sparse.reindex keyMap MixedData.row1567 = numericRow1567 := by decide +kernel

theorem numericCheck1567 (x : Master → ℝ) : Integer.Sparse.eval numericRow1567 x =
    (5760 : ℝ) * reducedSource1567 x := by
  norm_num [numericRow1567, reducedSource1567, Integer.Sparse.eval, Sparse.eval, nodeValue4171, nodeValue4172, nodeValue4175, nodeValue4541, nodeValue4544, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4622, nodeValue4623, nodeValue4624, nodeValue5167, nodeValue5292, nodeValue5307]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
