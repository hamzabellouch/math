import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1216 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue776 x + ((1 : ℝ) * Sparse.eval nodeValue778 x + ((3 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1216 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 783, 3), (Sum.inr 4068, -1)]

theorem reindexCheck1216 : Integer.Sparse.reindex keyMap MixedData.row1216 = numericRow1216 := by decide +kernel

theorem numericCheck1216 (x : Master → ℝ) : Integer.Sparse.eval numericRow1216 x =
    (1 : ℝ) * reducedSource1216 x := by
  norm_num [numericRow1216, reducedSource1216, Integer.Sparse.eval, Sparse.eval, nodeValue776, nodeValue778, nodeValue783, nodeValue1698, nodeValue4068]

noncomputable def reducedSource1217 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue1593 x + ((2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1217 : Integer.Sparse Master := [(Sum.inr 787, 1), (Sum.inr 1593, 1), (Sum.inr 1639, 2), (Sum.inr 1700, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1217 : Integer.Sparse.reindex keyMap MixedData.row1217 = numericRow1217 := by decide +kernel

theorem numericCheck1217 (x : Master → ℝ) : Integer.Sparse.eval numericRow1217 x =
    (1 : ℝ) * reducedSource1217 x := by
  norm_num [numericRow1217, reducedSource1217, Integer.Sparse.eval, Sparse.eval, nodeValue787, nodeValue1593, nodeValue1639, nodeValue1700, nodeValue1708, nodeValue4068]

noncomputable def reducedSource1218 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue542 x + ((1 : ℝ) * Sparse.eval nodeValue702 x + ((1 : ℝ) * Sparse.eval nodeValue737 x + ((2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1218 : Integer.Sparse Master := [(Sum.inr 542, 1), (Sum.inr 702, 1), (Sum.inr 737, 1), (Sum.inr 787, 2), (Sum.inr 4068, -1)]

theorem reindexCheck1218 : Integer.Sparse.reindex keyMap MixedData.row1218 = numericRow1218 := by decide +kernel

theorem numericCheck1218 (x : Master → ℝ) : Integer.Sparse.eval numericRow1218 x =
    (1 : ℝ) * reducedSource1218 x := by
  norm_num [numericRow1218, reducedSource1218, Integer.Sparse.eval, Sparse.eval, nodeValue542, nodeValue702, nodeValue737, nodeValue787, nodeValue810, nodeValue4068]

noncomputable def reducedSource1219 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1219 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 787, 1), (Sum.inr 790, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1219 : Integer.Sparse.reindex keyMap MixedData.row1219 = numericRow1219 := by decide +kernel

theorem numericCheck1219 (x : Master → ℝ) : Integer.Sparse.eval numericRow1219 x =
    (1 : ℝ) * reducedSource1219 x := by
  norm_num [numericRow1219, reducedSource1219, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue787, nodeValue790, nodeValue810, nodeValue1708, nodeValue4068]

noncomputable def reducedSource1220 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue1592 x + ((2 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1220 : Integer.Sparse Master := [(Sum.inr 785, 1), (Sum.inr 1637, 2), (Sum.inr 1707, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1220 : Integer.Sparse.reindex keyMap MixedData.row1220 = numericRow1220 := by decide +kernel

theorem numericCheck1220 (x : Master → ℝ) : Integer.Sparse.eval numericRow1220 x =
    (1 : ℝ) * reducedSource1220 x := by
  norm_num [numericRow1220, reducedSource1220, Integer.Sparse.eval, Sparse.eval, nodeValue785, nodeValue1592, nodeValue1637, nodeValue1707, nodeValue1710, nodeValue4069]

noncomputable def reducedSource1221 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue538 x + ((1 : ℝ) * Sparse.eval nodeValue699 x + ((1 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1221 : Integer.Sparse Master := [(Sum.inr 538, 1), (Sum.inr 699, 1), (Sum.inr 733, 1), (Sum.inr 785, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1221 : Integer.Sparse.reindex keyMap MixedData.row1221 = numericRow1221 := by decide +kernel

theorem numericCheck1221 (x : Master → ℝ) : Integer.Sparse.eval numericRow1221 x =
    (1 : ℝ) * reducedSource1221 x := by
  norm_num [numericRow1221, reducedSource1221, Integer.Sparse.eval, Sparse.eval, nodeValue538, nodeValue699, nodeValue733, nodeValue785, nodeValue806, nodeValue812, nodeValue4069]

noncomputable def reducedSource1222 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue782 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1222 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 785, 1), (Sum.inr 789, 1), (Sum.inr 1707, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1222 : Integer.Sparse.reindex keyMap MixedData.row1222 = numericRow1222 := by decide +kernel

theorem numericCheck1222 (x : Master → ℝ) : Integer.Sparse.eval numericRow1222 x =
    (1 : ℝ) * reducedSource1222 x := by
  norm_num [numericRow1222, reducedSource1222, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue785, nodeValue789, nodeValue806, nodeValue1707, nodeValue4069]

noncomputable def reducedSource1223 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue536 x + ((1 : ℝ) * Sparse.eval nodeValue698 x + ((1 : ℝ) * Sparse.eval nodeValue731 x + ((1 : ℝ) * Sparse.eval nodeValue804 x + ((2 : ℝ) * Sparse.eval nodeValue809 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1223 : Integer.Sparse Master := [(Sum.inr 536, 1), (Sum.inr 698, 1), (Sum.inr 731, 1), (Sum.inr 804, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1223 : Integer.Sparse.reindex keyMap MixedData.row1223 = numericRow1223 := by decide +kernel

theorem numericCheck1223 (x : Master → ℝ) : Integer.Sparse.eval numericRow1223 x =
    (1 : ℝ) * reducedSource1223 x := by
  norm_num [numericRow1223, reducedSource1223, Integer.Sparse.eval, Sparse.eval, nodeValue536, nodeValue698, nodeValue731, nodeValue804, nodeValue809, nodeValue4070]

noncomputable def reducedSource1224 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue813 x + ((2 : ℝ) * Sparse.eval nodeValue1603 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1224 : Integer.Sparse Master := [(Sum.inr 813, 1), (Sum.inr 1603, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1224 : Integer.Sparse.reindex keyMap MixedData.row1224 = numericRow1224 := by decide +kernel

theorem numericCheck1224 (x : Master → ℝ) : Integer.Sparse.eval numericRow1224 x =
    (1 : ℝ) * reducedSource1224 x := by
  norm_num [numericRow1224, reducedSource1224, Integer.Sparse.eval, Sparse.eval, nodeValue813, nodeValue1603, nodeValue1651, nodeValue1716, nodeValue1728, nodeValue4069]

noncomputable def reducedSource1225 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue548 x + ((2 : ℝ) * Sparse.eval nodeValue708 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1225 : Integer.Sparse Master := [(Sum.inr 548, 1), (Sum.inr 708, 2), (Sum.inr 743, 1), (Sum.inr 813, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1225 : Integer.Sparse.reindex keyMap MixedData.row1225 = numericRow1225 := by decide +kernel

theorem numericCheck1225 (x : Master → ℝ) : Integer.Sparse.eval numericRow1225 x =
    (1 : ℝ) * reducedSource1225 x := by
  norm_num [numericRow1225, reducedSource1225, Integer.Sparse.eval, Sparse.eval, nodeValue548, nodeValue708, nodeValue743, nodeValue813, nodeValue816, nodeValue4069]

noncomputable def reducedSource1226 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1226 : Integer.Sparse Master := [(Sum.inr 807, 2), (Sum.inr 813, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1226 : Integer.Sparse.reindex keyMap MixedData.row1226 = numericRow1226 := by decide +kernel

theorem numericCheck1226 (x : Master → ℝ) : Integer.Sparse.eval numericRow1226 x =
    (1 : ℝ) * reducedSource1226 x := by
  norm_num [numericRow1226, reducedSource1226, Integer.Sparse.eval, Sparse.eval, nodeValue807, nodeValue813, nodeValue816, nodeValue856, nodeValue1728, nodeValue4069]

noncomputable def reducedSource1227 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4127 x + ((2 : ℝ) * Sparse.eval nodeValue4196 x + ((2 : ℝ) * Sparse.eval nodeValue4202 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((2 : ℝ) * Sparse.eval nodeValue4218 x + ((2 : ℝ) * Sparse.eval nodeValue4233 x + ((1 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((2 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4273 x + ((2 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + 0))))))))))))))))))))

def numericRow1227 : Integer.Sparse Master := [(Sum.inr 538, -2), (Sum.inr 545, -1), (Sum.inr 547, -1), (Sum.inr 663, -2), (Sum.inr 683, -1), (Sum.inr 684, -1), (Sum.inr 699, -2), (Sum.inr 705, -2), (Sum.inr 707, -2), (Sum.inr 733, -2), (Sum.inr 740, -1), (Sum.inr 742, -1), (Sum.inr 748, -2), (Sum.inr 762, -2), (Sum.inr 763, -2), (Sum.inr 785, -2), (Sum.inr 791, -1), (Sum.inr 799, -2), (Sum.inr 804, -2), (Sum.inr 842, -1), (Sum.inr 843, -1), (Sum.inr 849, -1), (Sum.inr 999, -2), (Sum.inr 1074, -1), (Sum.inr 1080, -1), (Sum.inr 1602, -2), (Sum.inr 1650, -1), (Sum.inr 1710, -1), (Sum.inr 4069, 4)]

theorem reindexCheck1227 : Integer.Sparse.reindex keyMap MixedData.row1227 = numericRow1227 := by decide +kernel

theorem numericCheck1227 (x : Master → ℝ) : Integer.Sparse.eval numericRow1227 x =
    (4 : ℝ) * reducedSource1227 x := by
  norm_num [numericRow1227, reducedSource1227, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4101, nodeValue4108, nodeValue4110, nodeValue4127, nodeValue4196, nodeValue4202, nodeValue4204, nodeValue4218, nodeValue4233, nodeValue4240, nodeValue4242, nodeValue4251, nodeValue4257, nodeValue4264, nodeValue4269, nodeValue4273, nodeValue4418, nodeValue4490, nodeValue4496, nodeValue4498]
  ring

noncomputable def reducedSource1228 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue663 x + ((1 : ℝ) * Sparse.eval nodeValue683 x + ((1 : ℝ) * Sparse.eval nodeValue684 x + ((1 : ℝ) * Sparse.eval nodeValue688 x + ((2 : ℝ) * Sparse.eval nodeValue748 x + ((2 : ℝ) * Sparse.eval nodeValue762 x + ((2 : ℝ) * Sparse.eval nodeValue763 x + ((2 : ℝ) * Sparse.eval nodeValue767 x + ((2 : ℝ) * Sparse.eval nodeValue799 x + ((2 : ℝ) * Sparse.eval nodeValue804 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue842 x + ((1 : ℝ) * Sparse.eval nodeValue843 x + ((1 : ℝ) * Sparse.eval nodeValue849 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((2 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))))))))))))))))

def numericRow1228 : Integer.Sparse Master := [(Sum.inr 663, 2), (Sum.inr 683, 1), (Sum.inr 684, 1), (Sum.inr 748, 2), (Sum.inr 762, 2), (Sum.inr 763, 2), (Sum.inr 799, 2), (Sum.inr 804, 2), (Sum.inr 842, 1), (Sum.inr 843, 1), (Sum.inr 849, 1), (Sum.inr 999, 2), (Sum.inr 1074, 1), (Sum.inr 1080, 1), (Sum.inr 4069, 1)]

theorem reindexCheck1228 : Integer.Sparse.reindex keyMap MixedData.row1228 = numericRow1228 := by decide +kernel

theorem numericCheck1228 (x : Master → ℝ) : Integer.Sparse.eval numericRow1228 x =
    (1 : ℝ) * reducedSource1228 x := by
  norm_num [numericRow1228, reducedSource1228, Integer.Sparse.eval, Sparse.eval, nodeValue663, nodeValue683, nodeValue684, nodeValue688, nodeValue748, nodeValue762, nodeValue763, nodeValue767, nodeValue799, nodeValue804, nodeValue806, nodeValue842, nodeValue843, nodeValue849, nodeValue851, nodeValue852, nodeValue999, nodeValue1074, nodeValue1080, nodeValue1082, nodeValue4069]

noncomputable def reducedSource1229 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue812 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1229 : Integer.Sparse Master := [(Sum.inr 1602, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1229 : Integer.Sparse.reindex keyMap MixedData.row1229 = numericRow1229 := by decide +kernel

theorem numericCheck1229 (x : Master → ℝ) : Integer.Sparse.eval numericRow1229 x =
    (1 : ℝ) * reducedSource1229 x := by
  norm_num [numericRow1229, reducedSource1229, Integer.Sparse.eval, Sparse.eval, nodeValue812, nodeValue1602, nodeValue1650, nodeValue1710, nodeValue1727, nodeValue4069]

noncomputable def reducedSource1230 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1230 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 740, 1), (Sum.inr 742, 1), (Sum.inr 1650, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1230 : Integer.Sparse.reindex keyMap MixedData.row1230 = numericRow1230 := by decide +kernel

theorem numericCheck1230 (x : Master → ℝ) : Integer.Sparse.eval numericRow1230 x =
    (1 : ℝ) * reducedSource1230 x := by
  norm_num [numericRow1230, reducedSource1230, Integer.Sparse.eval, Sparse.eval, nodeValue733, nodeValue740, nodeValue742, nodeValue812, nodeValue1650, nodeValue4069]

noncomputable def reducedSource1231 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((2 : ℝ) * Sparse.eval nodeValue4099 x + ((1 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4109 x + ((1 : ℝ) * Sparse.eval nodeValue4120 x + ((2 : ℝ) * Sparse.eval nodeValue4195 x + ((2 : ℝ) * Sparse.eval nodeValue4198 x + ((2 : ℝ) * Sparse.eval nodeValue4203 x + ((2 : ℝ) * Sparse.eval nodeValue4211 x + ((2 : ℝ) * Sparse.eval nodeValue4231 x + ((1 : ℝ) * Sparse.eval nodeValue4235 x + ((1 : ℝ) * Sparse.eval nodeValue4241 x + ((2 : ℝ) * Sparse.eval nodeValue4251 x + ((2 : ℝ) * Sparse.eval nodeValue4266 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((1 : ℝ) * Sparse.eval nodeValue4274 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + 0))))))))))))))))))))

def numericRow1231 : Integer.Sparse Master := [(Sum.inr 536, -2), (Sum.inr 540, -1), (Sum.inr 546, -1), (Sum.inr 657, -2), (Sum.inr 665, -1), (Sum.inr 676, -1), (Sum.inr 698, -2), (Sum.inr 701, -2), (Sum.inr 706, -2), (Sum.inr 731, -2), (Sum.inr 735, -1), (Sum.inr 741, -1), (Sum.inr 744, -2), (Sum.inr 750, -2), (Sum.inr 755, -2), (Sum.inr 781, -2), (Sum.inr 785, -2), (Sum.inr 801, -1), (Sum.inr 804, -2), (Sum.inr 815, -1), (Sum.inr 820, -1), (Sum.inr 826, -1), (Sum.inr 979, -2), (Sum.inr 1037, -1), (Sum.inr 1043, -1), (Sum.inr 1599, -2), (Sum.inr 1647, -1), (Sum.inr 1725, -1), (Sum.inr 4070, 4)]

theorem reindexCheck1231 : Integer.Sparse.reindex keyMap MixedData.row1231 = numericRow1231 := by decide +kernel

theorem numericCheck1231 (x : Master → ℝ) : Integer.Sparse.eval numericRow1231 x =
    (4 : ℝ) * reducedSource1231 x := by
  norm_num [numericRow1231, reducedSource1231, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4099, nodeValue4103, nodeValue4109, nodeValue4120, nodeValue4195, nodeValue4198, nodeValue4203, nodeValue4211, nodeValue4231, nodeValue4235, nodeValue4241, nodeValue4251, nodeValue4266, nodeValue4269, nodeValue4272, nodeValue4274, nodeValue4398, nodeValue4454, nodeValue4460, nodeValue4501]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
