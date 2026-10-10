import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1536 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4068 x + ((1 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4105 x + ((2 : ℝ) * Sparse.eval nodeValue4107 x + ((1 : ℝ) * Sparse.eval nodeValue4125 x + ((1 : ℝ) * Sparse.eval nodeValue4199 x + ((2 : ℝ) * Sparse.eval nodeValue4201 x + ((1 : ℝ) * Sparse.eval nodeValue4216 x + ((1 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4237 x + ((2 : ℝ) * Sparse.eval nodeValue4239 x + ((2 : ℝ) * Sparse.eval nodeValue4249 x + ((2 : ℝ) * Sparse.eval nodeValue4253 x + ((2 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4263 x + ((4 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + 0)))))))))))))))))))

def numericRow1536 : Integer.Sparse Master := [(Sum.inr 537, -1), (Sum.inr 542, -1), (Sum.inr 544, -2), (Sum.inr 662, -1), (Sum.inr 681, -1), (Sum.inr 682, -2), (Sum.inr 702, -1), (Sum.inr 704, -2), (Sum.inr 732, -1), (Sum.inr 737, -1), (Sum.inr 739, -2), (Sum.inr 760, -1), (Sum.inr 761, -2), (Sum.inr 783, -2), (Sum.inr 787, -2), (Sum.inr 790, -2), (Sum.inr 798, -1), (Sum.inr 803, -2), (Sum.inr 840, -1), (Sum.inr 841, -2), (Sum.inr 847, -2), (Sum.inr 848, -2), (Sum.inr 998, -1), (Sum.inr 1073, -1), (Sum.inr 1079, -2), (Sum.inr 1600, -1), (Sum.inr 1648, -1), (Sum.inr 1708, -2), (Sum.inr 4068, 4)]

theorem reindexCheck1536 : Integer.Sparse.reindex keyMap MixedData.row1536 = numericRow1536 := by decide +kernel

theorem numericCheck1536 (x : Master → ℝ) : Integer.Sparse.eval numericRow1536 x =
    (4 : ℝ) * reducedSource1536 x := by
  norm_num [numericRow1536, reducedSource1536, Integer.Sparse.eval, Sparse.eval, nodeValue4068, nodeValue4100, nodeValue4105, nodeValue4107, nodeValue4125, nodeValue4199, nodeValue4201, nodeValue4216, nodeValue4232, nodeValue4237, nodeValue4239, nodeValue4249, nodeValue4253, nodeValue4256, nodeValue4263, nodeValue4267, nodeValue4417, nodeValue4489, nodeValue4495, nodeValue4497]
  ring

noncomputable def reducedSource1537 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue662 x + ((1 : ℝ) * Sparse.eval nodeValue681 x + ((2 : ℝ) * Sparse.eval nodeValue682 x + ((1 : ℝ) * Sparse.eval nodeValue687 x + ((1 : ℝ) * Sparse.eval nodeValue760 x + ((2 : ℝ) * Sparse.eval nodeValue761 x + ((1 : ℝ) * Sparse.eval nodeValue766 x + ((1 : ℝ) * Sparse.eval nodeValue798 x + ((2 : ℝ) * Sparse.eval nodeValue803 x + ((1 : ℝ) * Sparse.eval nodeValue805 x + ((1 : ℝ) * Sparse.eval nodeValue840 x + ((2 : ℝ) * Sparse.eval nodeValue841 x + ((2 : ℝ) * Sparse.eval nodeValue847 x + ((2 : ℝ) * Sparse.eval nodeValue848 x + ((4 : ℝ) * Sparse.eval nodeValue850 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))))))))))))))))

def numericRow1537 : Integer.Sparse Master := [(Sum.inr 662, 1), (Sum.inr 681, 1), (Sum.inr 682, 2), (Sum.inr 760, 1), (Sum.inr 761, 2), (Sum.inr 798, 1), (Sum.inr 803, 2), (Sum.inr 840, 1), (Sum.inr 841, 2), (Sum.inr 847, 2), (Sum.inr 848, 2), (Sum.inr 998, 1), (Sum.inr 1073, 1), (Sum.inr 1079, 2), (Sum.inr 4068, 1)]

theorem reindexCheck1537 : Integer.Sparse.reindex keyMap MixedData.row1537 = numericRow1537 := by decide +kernel

theorem numericCheck1537 (x : Master → ℝ) : Integer.Sparse.eval numericRow1537 x =
    (1 : ℝ) * reducedSource1537 x := by
  norm_num [numericRow1537, reducedSource1537, Integer.Sparse.eval, Sparse.eval, nodeValue662, nodeValue681, nodeValue682, nodeValue687, nodeValue760, nodeValue761, nodeValue766, nodeValue798, nodeValue803, nodeValue805, nodeValue840, nodeValue841, nodeValue847, nodeValue848, nodeValue850, nodeValue998, nodeValue1073, nodeValue1079, nodeValue1081, nodeValue4068]

noncomputable def reducedSource1538 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue732 x + ((1 : ℝ) * Sparse.eval nodeValue737 x + ((2 : ℝ) * Sparse.eval nodeValue739 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue1648 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1538 : Integer.Sparse Master := [(Sum.inr 732, 1), (Sum.inr 737, 1), (Sum.inr 739, 2), (Sum.inr 1648, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1538 : Integer.Sparse.reindex keyMap MixedData.row1538 = numericRow1538 := by decide +kernel

theorem numericCheck1538 (x : Master → ℝ) : Integer.Sparse.eval numericRow1538 x =
    (1 : ℝ) * reducedSource1538 x := by
  norm_num [numericRow1538, reducedSource1538, Integer.Sparse.eval, Sparse.eval, nodeValue732, nodeValue737, nodeValue739, nodeValue810, nodeValue1648, nodeValue4068]

noncomputable def reducedSource1539 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4113 x + ((1 : ℝ) * Sparse.eval nodeValue4118 x + ((2 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4126 x + ((1 : ℝ) * Sparse.eval nodeValue4209 x + ((2 : ℝ) * Sparse.eval nodeValue4210 x + ((1 : ℝ) * Sparse.eval nodeValue4217 x + ((2 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4267 x + ((4 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4275 x + ((2 : ℝ) * Sparse.eval nodeValue4283 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + 0)))))))))))))))))))

def numericRow1539 : Integer.Sparse Master := [(Sum.inr 550, -1), (Sum.inr 554, -2), (Sum.inr 557, -1), (Sum.inr 658, -1), (Sum.inr 668, -2), (Sum.inr 677, -1), (Sum.inr 713, -2), (Sum.inr 719, -1), (Sum.inr 751, -2), (Sum.inr 756, -1), (Sum.inr 783, -2), (Sum.inr 786, -1), (Sum.inr 803, -2), (Sum.inr 807, -4), (Sum.inr 811, -4), (Sum.inr 822, -1), (Sum.inr 824, -4), (Sum.inr 827, -2), (Sum.inr 980, -1), (Sum.inr 1041, -2), (Sum.inr 1044, -1), (Sum.inr 1616, -1), (Sum.inr 1724, -2), (Sum.inr 1737, -1), (Sum.inr 4069, 4)]

theorem reindexCheck1539 : Integer.Sparse.reindex keyMap MixedData.row1539 = numericRow1539 := by decide +kernel

theorem numericCheck1539 (x : Master → ℝ) : Integer.Sparse.eval numericRow1539 x =
    (4 : ℝ) * reducedSource1539 x := by
  norm_num [numericRow1539, reducedSource1539, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4113, nodeValue4118, nodeValue4119, nodeValue4126, nodeValue4209, nodeValue4210, nodeValue4217, nodeValue4249, nodeValue4252, nodeValue4264, nodeValue4265, nodeValue4267, nodeValue4268, nodeValue4275, nodeValue4283, nodeValue4399, nodeValue4458, nodeValue4461, nodeValue4502]
  ring

noncomputable def reducedSource1540 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4057 x + ((1 : ℝ) * Sparse.eval nodeValue4058 x + ((2 : ℝ) * Sparse.eval nodeValue4059 x + ((2 : ℝ) * Sparse.eval nodeValue4063 x + ((2 : ℝ) * Sparse.eval nodeValue4064 x + ((4 : ℝ) * Sparse.eval nodeValue4065 x + ((2 : ℝ) * Sparse.eval nodeValue4068 x + ((6 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((2 : ℝ) * Sparse.eval nodeValue4071 x + ((2 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

def numericRow1540 : Integer.Sparse Master := [(Sum.inr 4057, 2), (Sum.inr 4058, 1), (Sum.inr 4059, 2), (Sum.inr 4063, 2), (Sum.inr 4064, 2), (Sum.inr 4065, 4), (Sum.inr 4068, 2), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4071, 2), (Sum.inr 4080, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2)]

theorem reindexCheck1540 : Integer.Sparse.reindex keyMap MixedData.row1540 = numericRow1540 := by decide +kernel

theorem numericCheck1540 (x : Master → ℝ) : Integer.Sparse.eval numericRow1540 x =
    (1 : ℝ) * reducedSource1540 x := by
  norm_num [numericRow1540, reducedSource1540, Integer.Sparse.eval, Sparse.eval, nodeValue4057, nodeValue4058, nodeValue4059, nodeValue4063, nodeValue4064, nodeValue4065, nodeValue4068, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4080, nodeValue4083, nodeValue4084]

noncomputable def reducedSource1541 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((3 : ℝ) * Sparse.eval nodeValue3072 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1541 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 3057, 1), (Sum.inr 3072, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1541 : Integer.Sparse.reindex keyMap MixedData.row1541 = numericRow1541 := by decide +kernel

theorem numericCheck1541 (x : Master → ℝ) : Integer.Sparse.eval numericRow1541 x =
    (1 : ℝ) * reducedSource1541 x := by
  norm_num [numericRow1541, reducedSource1541, Integer.Sparse.eval, Sparse.eval, nodeValue1700, nodeValue3057, nodeValue3072, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1542 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((3 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1542 : Integer.Sparse Master := [(Sum.inr 1700, 1), (Sum.inr 1708, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1542 : Integer.Sparse.reindex keyMap MixedData.row1542 = numericRow1542 := by decide +kernel

theorem numericCheck1542 (x : Master → ℝ) : Integer.Sparse.eval numericRow1542 x =
    (1 : ℝ) * reducedSource1542 x := by
  norm_num [numericRow1542, reducedSource1542, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue1700, nodeValue1708, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1543 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue597 x + ((1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue1056 x + ((3 : ℝ) * Sparse.eval nodeValue1079 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1543 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 1056, 1), (Sum.inr 1079, 3), (Sum.inr 4084, -1)]

theorem reindexCheck1543 : Integer.Sparse.reindex keyMap MixedData.row1543 = numericRow1543 := by decide +kernel

theorem numericCheck1543 (x : Master → ℝ) : Integer.Sparse.eval numericRow1543 x =
    (1 : ℝ) * reducedSource1543 x := by
  norm_num [numericRow1543, reducedSource1543, Integer.Sparse.eval, Sparse.eval, nodeValue597, nodeValue1038, nodeValue1056, nodeValue1079, nodeValue4084]

noncomputable def reducedSource1544 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((3 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1544 : Integer.Sparse Master := [(Sum.inr 3286, 3), (Sum.inr 3292, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1544 : Integer.Sparse.reindex keyMap MixedData.row1544 = numericRow1544 := by decide +kernel

theorem numericCheck1544 (x : Master → ℝ) : Integer.Sparse.eval numericRow1544 x =
    (1 : ℝ) * reducedSource1544 x := by
  norm_num [numericRow1544, reducedSource1544, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue3286, nodeValue3292, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1545 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((3 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1545 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 1706, 3), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1545 : Integer.Sparse.reindex keyMap MixedData.row1545 = numericRow1545 := by decide +kernel

theorem numericCheck1545 (x : Master → ℝ) : Integer.Sparse.eval numericRow1545 x =
    (1 : ℝ) * reducedSource1545 x := by
  norm_num [numericRow1545, reducedSource1545, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue1699, nodeValue1706, nodeValue3292, nodeValue4068]

noncomputable def reducedSource1546 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1319 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1546 : Integer.Sparse Master := [(Sum.inr 1316, 3), (Sum.inr 1319, 1), (Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1546 : Integer.Sparse.reindex keyMap MixedData.row1546 = numericRow1546 := by decide +kernel

theorem numericCheck1546 (x : Master → ℝ) : Integer.Sparse.eval numericRow1546 x =
    (1 : ℝ) * reducedSource1546 x := by
  norm_num [numericRow1546, reducedSource1546, Integer.Sparse.eval, Sparse.eval, nodeValue1316, nodeValue1319, nodeValue1366, nodeValue2880, nodeValue4091]

noncomputable def reducedSource1547 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((3 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3244 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1547 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 3239, 3), (Sum.inr 3244, 1), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1547 : Integer.Sparse.reindex keyMap MixedData.row1547 = numericRow1547 := by decide +kernel

theorem numericCheck1547 (x : Master → ℝ) : Integer.Sparse.eval numericRow1547 x =
    (1 : ℝ) * reducedSource1547 x := by
  norm_num [numericRow1547, reducedSource1547, Integer.Sparse.eval, Sparse.eval, nodeValue1699, nodeValue3239, nodeValue3244, nodeValue3292, nodeValue4068]

noncomputable def reducedSource1548 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1256 x + ((1 : ℝ) * Sparse.eval nodeValue2628 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((3 : ℝ) * Sparse.eval nodeValue2747 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))

def numericRow1548 : Integer.Sparse Master := [(Sum.inr 1256, 1), (Sum.inr 2628, 1), (Sum.inr 2671, 1), (Sum.inr 2747, 3), (Sum.inr 4087, -1)]

theorem reindexCheck1548 : Integer.Sparse.reindex keyMap MixedData.row1548 = numericRow1548 := by decide +kernel

theorem numericCheck1548 (x : Master → ℝ) : Integer.Sparse.eval numericRow1548 x =
    (1 : ℝ) * reducedSource1548 x := by
  norm_num [numericRow1548, reducedSource1548, Integer.Sparse.eval, Sparse.eval, nodeValue1256, nodeValue2628, nodeValue2671, nodeValue2747, nodeValue4087]

noncomputable def reducedSource1549 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1644 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((3 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1549 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 3057, 1), (Sum.inr 3289, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1549 : Integer.Sparse.reindex keyMap MixedData.row1549 = numericRow1549 := by decide +kernel

theorem numericCheck1549 (x : Master → ℝ) : Integer.Sparse.eval numericRow1549 x =
    (1 : ℝ) * reducedSource1549 x := by
  norm_num [numericRow1549, reducedSource1549, Integer.Sparse.eval, Sparse.eval, nodeValue1644, nodeValue3057, nodeValue3289, nodeValue3304, nodeValue4068]

noncomputable def reducedSource1550 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1127 x + ((2 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1550 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1127, 1), (Sum.inr 1130, 2), (Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1550 : Integer.Sparse.reindex keyMap MixedData.row1550 = numericRow1550 := by decide +kernel

theorem numericCheck1550 (x : Master → ℝ) : Integer.Sparse.eval numericRow1550 x =
    (1 : ℝ) * reducedSource1550 x := by
  norm_num [numericRow1550, reducedSource1550, Integer.Sparse.eval, Sparse.eval, nodeValue1126, nodeValue1127, nodeValue1130, nodeValue1233, nodeValue2508, nodeValue4092]

noncomputable def reducedSource1551 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue637 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((3 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1551 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 1260, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1551 : Integer.Sparse.reindex keyMap MixedData.row1551 = numericRow1551 := by decide +kernel

theorem numericCheck1551 (x : Master → ℝ) : Integer.Sparse.eval numericRow1551 x =
    (1 : ℝ) * reducedSource1551 x := by
  norm_num [numericRow1551, reducedSource1551, Integer.Sparse.eval, Sparse.eval, nodeValue637, nodeValue1235, nodeValue1260, nodeValue1293, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
