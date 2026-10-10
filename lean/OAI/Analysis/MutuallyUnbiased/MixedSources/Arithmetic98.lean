import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1568 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue599 x + ((2 : ℝ) * Sparse.eval nodeValue600 x + ((2 : ℝ) * Sparse.eval nodeValue603 x + ((2 : ℝ) * Sparse.eval nodeValue1126 x + ((2 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1235 x + ((4 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1300 x + ((4 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + 0)))))))))))))

def numericRow1568 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, 110), (Sum.inr 599, 1440), (Sum.inr 600, 2880), (Sum.inr 603, 2880), (Sum.inr 1126, 2880), (Sum.inr 1129, 2880), (Sum.inr 1235, 2880), (Sum.inr 1236, 5760), (Sum.inr 1240, 2880)]

theorem reindexCheck1568 : Integer.Sparse.reindex keyMap MixedData.row1568 = numericRow1568 := by decide +kernel

theorem numericCheck1568 (x : Master → ℝ) : Integer.Sparse.eval numericRow1568 x =
    (1440 : ℝ) * reducedSource1568 x := by
  norm_num [numericRow1568, reducedSource1568, Integer.Sparse.eval, Sparse.eval, nodeValue599, nodeValue600, nodeValue603, nodeValue1126, nodeValue1129, nodeValue1235, nodeValue1236, nodeValue1240, nodeValue1299, nodeValue1300, nodeValue1301, nodeValue2958, nodeValue3100, nodeValue3122]
  ring

noncomputable def reducedSource1569 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4456 x + ((4 : ℝ) * Sparse.eval nodeValue4495 x + ((4 : ℝ) * Sparse.eval nodeValue4497 x + ((4 : ℝ) * Sparse.eval nodeValue4599 x + ((4 : ℝ) * Sparse.eval nodeValue4601 x + ((4 : ℝ) * Sparse.eval nodeValue4616 x + ((4 : ℝ) * Sparse.eval nodeValue4618 x + ((4 : ℝ) * Sparse.eval nodeValue4622 x + 0)))))))

def numericRow1569 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -70), (Sum.inr 1039, -2160), (Sum.inr 1079, -4320), (Sum.inr 1235, -4320), (Sum.inr 1293, -4320), (Sum.inr 1706, -2160), (Sum.inr 1708, -4320), (Sum.inr 3292, -4320), (Sum.inr 3304, -4320), (Sum.inr 3307, -4320), (Sum.inr 4599, 17280), (Sum.inr 4616, 17280)]

theorem reindexCheck1569 : Integer.Sparse.reindex keyMap MixedData.row1569 = numericRow1569 := by decide +kernel

theorem numericCheck1569 (x : Master → ℝ) : Integer.Sparse.eval numericRow1569 x =
    (4320 : ℝ) * reducedSource1569 x := by
  norm_num [numericRow1569, reducedSource1569, Integer.Sparse.eval, Sparse.eval, nodeValue4456, nodeValue4495, nodeValue4497, nodeValue4599, nodeValue4601, nodeValue4616, nodeValue4618, nodeValue4622]
  ring

noncomputable def reducedSource1570 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1570 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 2503, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 2), (Sum.inr 2728, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1570 : Integer.Sparse.reindex keyMap MixedData.row1570 = numericRow1570 := by decide +kernel

theorem numericCheck1570 (x : Master → ℝ) : Integer.Sparse.eval numericRow1570 x =
    (1 : ℝ) * reducedSource1570 x := by
  norm_num [numericRow1570, reducedSource1570, Integer.Sparse.eval, Sparse.eval, nodeValue1228, nodeValue2503, nodeValue2703, nodeValue2718, nodeValue2728, nodeValue4090]

noncomputable def reducedSource1571 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4149 x + ((3 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4169 x + ((3 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4550 x + ((3 : ℝ) * Sparse.eval nodeValue4589 x + ((6 : ℝ) * Sparse.eval nodeValue4590 x + ((3 : ℝ) * Sparse.eval nodeValue4599 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0))))))))))))

def numericRow1571 : Integer.Sparse Master := [(Sum.inr 1129, -3), (Sum.inr 1135, -1), (Sum.inr 1240, -3), (Sum.inr 1293, -1), (Sum.inr 2721, -3), (Sum.inr 3263, -3), (Sum.inr 3269, -1), (Sum.inr 3299, -3), (Sum.inr 3304, -1), (Sum.inr 3532, -3), (Sum.inr 4149, 4), (Sum.inr 4150, 12), (Sum.inr 4169, 4), (Sum.inr 4589, 12), (Sum.inr 4590, 24), (Sum.inr 4599, 12)]

theorem reindexCheck1571 : Integer.Sparse.reindex keyMap MixedData.row1571 = numericRow1571 := by decide +kernel

theorem numericCheck1571 (x : Master → ℝ) : Integer.Sparse.eval numericRow1571 x =
    (4 : ℝ) * reducedSource1571 x := by
  norm_num [numericRow1571, reducedSource1571, Integer.Sparse.eval, Sparse.eval, nodeValue4149, nodeValue4150, nodeValue4169, nodeValue4544, nodeValue4550, nodeValue4589, nodeValue4590, nodeValue4599, nodeValue4606, nodeValue4618, nodeValue5100, nodeValue5257, nodeValue5273]
  ring

noncomputable def reducedSource1572 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((3 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue1161 x + ((3 : ℝ) * Sparse.eval nodeValue1162 x + ((3 : ℝ) * Sparse.eval nodeValue1212 x + ((6 : ℝ) * Sparse.eval nodeValue1213 x + ((3 : ℝ) * Sparse.eval nodeValue1233 x + ((3 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2999 x + ((3 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))

def numericRow1572 : Integer.Sparse Master := [(Sum.inl 0, -203), (Sum.inl 9, 320), (Sum.inl 58, -20), (Sum.inl 2, 155), (Sum.inl 69, 480), (Sum.inl 70, 160), (Sum.inl 71, 960), (Sum.inl 3, 1200), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 1, -970), (Sum.inr 577, 4320), (Sum.inr 578, 12960), (Sum.inr 597, 4320), (Sum.inr 1212, 12960), (Sum.inr 1213, 25920), (Sum.inr 1233, 12960)]

theorem reindexCheck1572 : Integer.Sparse.reindex keyMap MixedData.row1572 = numericRow1572 := by decide +kernel

theorem numericCheck1572 (x : Master → ℝ) : Integer.Sparse.eval numericRow1572 x =
    (4320 : ℝ) * reducedSource1572 x := by
  norm_num [numericRow1572, reducedSource1572, Integer.Sparse.eval, Sparse.eval, nodeValue577, nodeValue578, nodeValue597, nodeValue1161, nodeValue1162, nodeValue1212, nodeValue1213, nodeValue1233, nodeValue1266, nodeValue1298, nodeValue2999, nodeValue3087, nodeValue3111]
  ring

noncomputable def reducedSource1573 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1502 x + ((3 : ℝ) * Sparse.eval nodeValue1504 x + ((3 : ℝ) * Sparse.eval nodeValue3263 x + ((1 : ℝ) * Sparse.eval nodeValue3269 x + ((3 : ℝ) * Sparse.eval nodeValue3288 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((6 : ℝ) * Sparse.eval nodeValue3290 x + ((3 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3469 x + ((3 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + 0))))))))))))

def numericRow1573 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1502, 1), (Sum.inr 1504, 3), (Sum.inr 3263, 3), (Sum.inr 3269, 1), (Sum.inr 3288, 3), (Sum.inr 3289, 3), (Sum.inr 3290, 6), (Sum.inr 3299, 3), (Sum.inr 3304, 1), (Sum.inr 3532, 3)]

theorem reindexCheck1573 : Integer.Sparse.reindex keyMap MixedData.row1573 = numericRow1573 := by decide +kernel

theorem numericCheck1573 (x : Master → ℝ) : Integer.Sparse.eval numericRow1573 x =
    (1 : ℝ) * reducedSource1573 x := by
  norm_num [numericRow1573, reducedSource1573, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1502, nodeValue1504, nodeValue3263, nodeValue3269, nodeValue3288, nodeValue3289, nodeValue3290, nodeValue3299, nodeValue3304, nodeValue3469, nodeValue3532, nodeValue3546]

noncomputable def reducedSource1574 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue637 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1574 : Integer.Sparse Master := [(Sum.inr 625, 3), (Sum.inr 629, 1), (Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1574 : Integer.Sparse.reindex keyMap MixedData.row1574 = numericRow1574 := by decide +kernel

theorem numericCheck1574 (x : Master → ℝ) : Integer.Sparse.eval numericRow1574 x =
    (1 : ℝ) * reducedSource1574 x := by
  norm_num [numericRow1574, reducedSource1574, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue629, nodeValue637, nodeValue1235, nodeValue4091]

noncomputable def reducedSource1575 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4139 x + ((1 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((3 : ℝ) * Sparse.eval nodeValue4513 x + ((1 : ℝ) * Sparse.eval nodeValue4516 x + ((3 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue4602 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((3 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + 0))))))))))))

def numericRow1575 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, -90), (Sum.inr 567, -4320), (Sum.inr 571, -1440), (Sum.inr 599, -1440), (Sum.inr 1097, -4320), (Sum.inr 1100, -1440), (Sum.inr 1200, -4320), (Sum.inr 1235, -1440), (Sum.inr 1236, -8640), (Sum.inr 1240, -4320), (Sum.inr 1488, -4320), (Sum.inr 1491, -1440), (Sum.inr 1506, -1440), (Sum.inr 2880, -1440), (Sum.inr 3232, -4320), (Sum.inr 3234, -1440), (Sum.inr 3281, -4320), (Sum.inr 3292, -1440), (Sum.inr 3293, -8640), (Sum.inr 3299, -4320), (Sum.inr 3307, -4320), (Sum.inr 3617, -1440), (Sum.inr 3622, -4320)]

theorem reindexCheck1575 : Integer.Sparse.reindex keyMap MixedData.row1575 = numericRow1575 := by decide +kernel

theorem numericCheck1575 (x : Master → ℝ) : Integer.Sparse.eval numericRow1575 x =
    (5760 : ℝ) * reducedSource1575 x := by
  norm_num [numericRow1575, reducedSource1575, Integer.Sparse.eval, Sparse.eval, nodeValue4139, nodeValue4143, nodeValue4171, nodeValue4513, nodeValue4516, nodeValue4581, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4622, nodeValue5202, nodeValue5283, nodeValue5292]
  ring

noncomputable def reducedSource1576 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue567 x + ((1 : ℝ) * Sparse.eval nodeValue571 x + ((1 : ℝ) * Sparse.eval nodeValue599 x + ((3 : ℝ) * Sparse.eval nodeValue1097 x + ((1 : ℝ) * Sparse.eval nodeValue1100 x + ((3 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((6 : ℝ) * Sparse.eval nodeValue1236 x + ((3 : ℝ) * Sparse.eval nodeValue1240 x + ((3 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + 0))))))))))))

def numericRow1576 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 6, 15), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 1, 90), (Sum.inr 567, 4320), (Sum.inr 571, 1440), (Sum.inr 599, 1440), (Sum.inr 1097, 4320), (Sum.inr 1100, 1440), (Sum.inr 1200, 4320), (Sum.inr 1235, 1440), (Sum.inr 1236, 8640), (Sum.inr 1240, 4320), (Sum.inr 2880, 1440)]

theorem reindexCheck1576 : Integer.Sparse.reindex keyMap MixedData.row1576 = numericRow1576 := by decide +kernel

theorem numericCheck1576 (x : Master → ℝ) : Integer.Sparse.eval numericRow1576 x =
    (1440 : ℝ) * reducedSource1576 x := by
  norm_num [numericRow1576, reducedSource1576, Integer.Sparse.eval, Sparse.eval, nodeValue567, nodeValue571, nodeValue599, nodeValue1097, nodeValue1100, nodeValue1200, nodeValue1235, nodeValue1236, nodeValue1240, nodeValue1299, nodeValue2880, nodeValue3076, nodeValue3100]
  ring

noncomputable def reducedSource1577 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1577 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 2398, 1), (Sum.inr 2669, 2), (Sum.inr 2676, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1577 : Integer.Sparse.reindex keyMap MixedData.row1577 = numericRow1577 := by decide +kernel

theorem numericCheck1577 (x : Master → ℝ) : Integer.Sparse.eval numericRow1577 x =
    (1 : ℝ) * reducedSource1577 x := by
  norm_num [numericRow1577, reducedSource1577, Integer.Sparse.eval, Sparse.eval, nodeValue1183, nodeValue2398, nodeValue2669, nodeValue2676, nodeValue2684, nodeValue4088]

noncomputable def reducedSource1578 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue2402 x + ((4 : ℝ) * Sparse.eval nodeValue2671 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))

def numericRow1578 : Integer.Sparse Master := [(Sum.inr 1187, 1), (Sum.inr 2671, 4), (Sum.inr 4087, -1)]

theorem reindexCheck1578 : Integer.Sparse.reindex keyMap MixedData.row1578 = numericRow1578 := by decide +kernel

theorem numericCheck1578 (x : Master → ℝ) : Integer.Sparse.eval numericRow1578 x =
    (1 : ℝ) * reducedSource1578 x := by
  norm_num [numericRow1578, reducedSource1578, Integer.Sparse.eval, Sparse.eval, nodeValue1187, nodeValue2402, nodeValue2671, nodeValue4087]

noncomputable def reducedSource1579 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1100 x + ((1 : ℝ) * Sparse.eval nodeValue1187 x + ((1 : ℝ) * Sparse.eval nodeValue2402 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))

def numericRow1579 : Integer.Sparse Master := [(Sum.inr 1100, 4), (Sum.inr 1187, 1), (Sum.inr 4087, -1)]

theorem reindexCheck1579 : Integer.Sparse.reindex keyMap MixedData.row1579 = numericRow1579 := by decide +kernel

theorem numericCheck1579 (x : Master → ℝ) : Integer.Sparse.eval numericRow1579 x =
    (1 : ℝ) * reducedSource1579 x := by
  norm_num [numericRow1579, reducedSource1579, Integer.Sparse.eval, Sparse.eval, nodeValue1100, nodeValue1187, nodeValue2402, nodeValue4087]

noncomputable def reducedSource1580 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue2127 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1580 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 2127, 1), (Sum.inr 2214, 1), (Sum.inr 2250, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1580 : Integer.Sparse.reindex keyMap MixedData.row1580 = numericRow1580 := by decide +kernel

theorem numericCheck1580 (x : Master → ℝ) : Integer.Sparse.eval numericRow1580 x =
    (1 : ℝ) * reducedSource1580 x := by
  norm_num [numericRow1580, reducedSource1580, Integer.Sparse.eval, Sparse.eval, nodeValue1052, nodeValue2127, nodeValue2214, nodeValue2250, nodeValue2275, nodeValue4080]

noncomputable def reducedSource1581 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1581 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 2098, 1), (Sum.inr 2202, 1), (Sum.inr 2240, 1), (Sum.inr 2250, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1581 : Integer.Sparse.reindex keyMap MixedData.row1581 = numericRow1581 := by decide +kernel

theorem numericCheck1581 (x : Master → ℝ) : Integer.Sparse.eval numericRow1581 x =
    (1 : ℝ) * reducedSource1581 x := by
  norm_num [numericRow1581, reducedSource1581, Integer.Sparse.eval, Sparse.eval, nodeValue1032, nodeValue2098, nodeValue2202, nodeValue2240, nodeValue2250, nodeValue2260, nodeValue4080]

noncomputable def reducedSource1582 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2100 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((3 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

def numericRow1582 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 2100, 1), (Sum.inr 2241, 3), (Sum.inr 4079, -1)]

theorem reindexCheck1582 : Integer.Sparse.reindex keyMap MixedData.row1582 = numericRow1582 := by decide +kernel

theorem numericCheck1582 (x : Master → ℝ) : Integer.Sparse.eval numericRow1582 x =
    (1 : ℝ) * reducedSource1582 x := by
  norm_num [numericRow1582, reducedSource1582, Integer.Sparse.eval, Sparse.eval, nodeValue1034, nodeValue2100, nodeValue2204, nodeValue2241, nodeValue4079]

noncomputable def reducedSource1583 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue732 x + ((1 : ℝ) * Sparse.eval nodeValue736 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue1644 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1583 : Integer.Sparse Master := [(Sum.inr 732, 3), (Sum.inr 736, 1), (Sum.inr 1644, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1583 : Integer.Sparse.reindex keyMap MixedData.row1583 = numericRow1583 := by decide +kernel

theorem numericCheck1583 (x : Master → ℝ) : Integer.Sparse.eval numericRow1583 x =
    (1 : ℝ) * reducedSource1583 x := by
  norm_num [numericRow1583, reducedSource1583, Integer.Sparse.eval, Sparse.eval, nodeValue732, nodeValue736, nodeValue805, nodeValue1644, nodeValue4068]

end MUB6.Certificate.MixedSourceBridge

end OAI
