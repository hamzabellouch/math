import OAI.Analysis.MutuallyUnbiased.MixedData.Source10
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
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

noncomputable def reducedSource1328 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue562 x + ((2 : ℝ) * Sparse.eval nodeValue724 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue858 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1328 : Integer.Sparse Master := [(Sum.inr 562, 1), (Sum.inr 724, 2), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1328 : Integer.Sparse.reindex keyMap MixedData.row1328 = numericRow1328 := by decide +kernel

theorem numericCheck1328 (x : Master → ℝ) : Integer.Sparse.eval numericRow1328 x =
    (1 : ℝ) * reducedSource1328 x := by
  norm_num [numericRow1328, reducedSource1328, Integer.Sparse.eval, Sparse.eval, nodeValue562, nodeValue724, nodeValue830, nodeValue852, nodeValue858, nodeValue4071]

noncomputable def reducedSource1329 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1329 : Integer.Sparse Master := [(Sum.inr 831, 1), (Sum.inr 1612, 2), (Sum.inr 1661, 1), (Sum.inr 1739, 2), (Sum.inr 4069, -1)]

theorem reindexCheck1329 : Integer.Sparse.reindex keyMap MixedData.row1329 = numericRow1329 := by decide +kernel

theorem numericCheck1329 (x : Master → ℝ) : Integer.Sparse.eval numericRow1329 x =
    (1 : ℝ) * reducedSource1329 x := by
  norm_num [numericRow1329, reducedSource1329, Integer.Sparse.eval, Sparse.eval, nodeValue831, nodeValue1612, nodeValue1661, nodeValue1739, nodeValue4069]

noncomputable def reducedSource1330 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue789 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1330 : Integer.Sparse Master := [(Sum.inr 789, 1), (Sum.inr 1594, 1), (Sum.inr 1640, 2), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1330 : Integer.Sparse.reindex keyMap MixedData.row1330 = numericRow1330 := by decide +kernel

theorem numericCheck1330 (x : Master → ℝ) : Integer.Sparse.eval numericRow1330 x =
    (1 : ℝ) * reducedSource1330 x := by
  norm_num [numericRow1330, reducedSource1330, Integer.Sparse.eval, Sparse.eval, nodeValue789, nodeValue1594, nodeValue1640, nodeValue1707, nodeValue1709, nodeValue4069]

noncomputable def reducedSource1331 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue543 x + ((1 : ℝ) * Sparse.eval nodeValue703 x + ((1 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue811 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1331 : Integer.Sparse Master := [(Sum.inr 543, 1), (Sum.inr 703, 1), (Sum.inr 738, 1), (Sum.inr 789, 1), (Sum.inr 811, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1331 : Integer.Sparse.reindex keyMap MixedData.row1331 = numericRow1331 := by decide +kernel

theorem numericCheck1331 (x : Master → ℝ) : Integer.Sparse.eval numericRow1331 x =
    (1 : ℝ) * reducedSource1331 x := by
  norm_num [numericRow1331, reducedSource1331, Integer.Sparse.eval, Sparse.eval, nodeValue543, nodeValue703, nodeValue738, nodeValue789, nodeValue806, nodeValue811, nodeValue4069]

noncomputable def reducedSource1332 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue552 x + ((1 : ℝ) * Sparse.eval nodeValue710 x + ((1 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue848 x + ((2 : ℝ) * Sparse.eval nodeValue852 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1332 : Integer.Sparse Master := [(Sum.inr 552, 1), (Sum.inr 710, 1), (Sum.inr 823, 1), (Sum.inr 848, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1332 : Integer.Sparse.reindex keyMap MixedData.row1332 = numericRow1332 := by decide +kernel

theorem numericCheck1332 (x : Master → ℝ) : Integer.Sparse.eval numericRow1332 x =
    (1 : ℝ) * reducedSource1332 x := by
  norm_num [numericRow1332, reducedSource1332, Integer.Sparse.eval, Sparse.eval, nodeValue552, nodeValue710, nodeValue823, nodeValue848, nodeValue852, nodeValue4071]

noncomputable def reducedSource1333 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue790 x + ((1 : ℝ) * Sparse.eval nodeValue1595 x + ((2 : ℝ) * Sparse.eval nodeValue1641 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0))))

def numericRow1333 : Integer.Sparse Master := [(Sum.inr 790, 1), (Sum.inr 1641, 2), (Sum.inr 1708, 2), (Sum.inr 4068, -1)]

theorem reindexCheck1333 : Integer.Sparse.reindex keyMap MixedData.row1333 = numericRow1333 := by decide +kernel

theorem numericCheck1333 (x : Master → ℝ) : Integer.Sparse.eval numericRow1333 x =
    (1 : ℝ) * reducedSource1333 x := by
  norm_num [numericRow1333, reducedSource1333, Integer.Sparse.eval, Sparse.eval, nodeValue790, nodeValue1595, nodeValue1641, nodeValue1708, nodeValue4068]

noncomputable def reducedSource1334 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue544 x + ((1 : ℝ) * Sparse.eval nodeValue704 x + ((1 : ℝ) * Sparse.eval nodeValue739 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue810 x + ((-1 : ℝ) * Sparse.eval nodeValue4068 x + 0)))))

def numericRow1334 : Integer.Sparse Master := [(Sum.inr 544, 1), (Sum.inr 704, 1), (Sum.inr 739, 1), (Sum.inr 790, 1), (Sum.inr 4068, -1)]

theorem reindexCheck1334 : Integer.Sparse.reindex keyMap MixedData.row1334 = numericRow1334 := by decide +kernel

theorem numericCheck1334 (x : Master → ℝ) : Integer.Sparse.eval numericRow1334 x =
    (1 : ℝ) * reducedSource1334 x := by
  norm_num [numericRow1334, reducedSource1334, Integer.Sparse.eval, Sparse.eval, nodeValue544, nodeValue704, nodeValue739, nodeValue790, nodeValue810, nodeValue4068]

noncomputable def reducedSource1335 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4130 x + ((2 : ℝ) * Sparse.eval nodeValue4197 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((2 : ℝ) * Sparse.eval nodeValue4205 x + ((2 : ℝ) * Sparse.eval nodeValue4221 x + ((2 : ℝ) * Sparse.eval nodeValue4234 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + 0))))))))))))))))))))

def numericRow1335 : Integer.Sparse Master := [(Sum.inr 539, -2), (Sum.inr 547, -1), (Sum.inr 548, -1), (Sum.inr 664, -2), (Sum.inr 684, -1), (Sum.inr 685, -1), (Sum.inr 700, -2), (Sum.inr 707, -2), (Sum.inr 708, -2), (Sum.inr 734, -2), (Sum.inr 742, -1), (Sum.inr 743, -1), (Sum.inr 749, -2), (Sum.inr 763, -2), (Sum.inr 764, -2), (Sum.inr 800, -2), (Sum.inr 807, -4), (Sum.inr 813, -1), (Sum.inr 843, -1), (Sum.inr 844, -1), (Sum.inr 853, -1), (Sum.inr 1000, -2), (Sum.inr 1075, -1), (Sum.inr 1083, -1), (Sum.inr 1605, -2), (Sum.inr 1653, -1), (Sum.inr 1728, -1), (Sum.inr 4069, 4)]

theorem reindexCheck1335 : Integer.Sparse.reindex keyMap MixedData.row1335 = numericRow1335 := by decide +kernel

theorem numericCheck1335 (x : Master → ℝ) : Integer.Sparse.eval numericRow1335 x =
    (4 : ℝ) * reducedSource1335 x := by
  norm_num [numericRow1335, reducedSource1335, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4102, nodeValue4110, nodeValue4111, nodeValue4130, nodeValue4197, nodeValue4204, nodeValue4205, nodeValue4221, nodeValue4234, nodeValue4242, nodeValue4243, nodeValue4264, nodeValue4265, nodeValue4269, nodeValue4270, nodeValue4283, nodeValue4419, nodeValue4491, nodeValue4498, nodeValue4499]; ring

noncomputable def reducedSource1336 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue664 x + ((1 : ℝ) * Sparse.eval nodeValue684 x + ((1 : ℝ) * Sparse.eval nodeValue685 x + ((1 : ℝ) * Sparse.eval nodeValue689 x + ((2 : ℝ) * Sparse.eval nodeValue749 x + ((2 : ℝ) * Sparse.eval nodeValue763 x + ((2 : ℝ) * Sparse.eval nodeValue764 x + ((2 : ℝ) * Sparse.eval nodeValue768 x + ((2 : ℝ) * Sparse.eval nodeValue800 x + ((2 : ℝ) * Sparse.eval nodeValue806 x + ((2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue843 x + ((1 : ℝ) * Sparse.eval nodeValue844 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))))))))))))))))

def numericRow1336 : Integer.Sparse Master := [(Sum.inr 664, 2), (Sum.inr 684, 1), (Sum.inr 685, 1), (Sum.inr 749, 2), (Sum.inr 763, 2), (Sum.inr 764, 2), (Sum.inr 800, 2), (Sum.inr 807, 2), (Sum.inr 843, 1), (Sum.inr 844, 1), (Sum.inr 853, 1), (Sum.inr 1000, 2), (Sum.inr 1075, 1), (Sum.inr 1083, 1), (Sum.inr 4069, 1)]

theorem reindexCheck1336 : Integer.Sparse.reindex keyMap MixedData.row1336 = numericRow1336 := by decide +kernel

theorem numericCheck1336 (x : Master → ℝ) : Integer.Sparse.eval numericRow1336 x =
    (1 : ℝ) * reducedSource1336 x := by
  norm_num [numericRow1336, reducedSource1336, Integer.Sparse.eval, Sparse.eval, nodeValue664, nodeValue684, nodeValue685, nodeValue689, nodeValue749, nodeValue763, nodeValue764, nodeValue768, nodeValue800, nodeValue806, nodeValue807, nodeValue843, nodeValue844, nodeValue851, nodeValue853, nodeValue856, nodeValue1000, nodeValue1075, nodeValue1082, nodeValue1083, nodeValue4069]

noncomputable def reducedSource1337 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue816 x + ((2 : ℝ) * Sparse.eval nodeValue1605 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1337 : Integer.Sparse Master := [(Sum.inr 1605, 2), (Sum.inr 1653, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1337 : Integer.Sparse.reindex keyMap MixedData.row1337 = numericRow1337 := by decide +kernel

theorem numericCheck1337 (x : Master → ℝ) : Integer.Sparse.eval numericRow1337 x =
    (1 : ℝ) * reducedSource1337 x := by
  norm_num [numericRow1337, reducedSource1337, Integer.Sparse.eval, Sparse.eval, nodeValue816, nodeValue1605, nodeValue1653, nodeValue1727, nodeValue1728, nodeValue4069]

noncomputable def reducedSource1338 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue539 x + ((1 : ℝ) * Sparse.eval nodeValue547 x + ((1 : ℝ) * Sparse.eval nodeValue548 x + ((1 : ℝ) * Sparse.eval nodeValue561 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1338 : Integer.Sparse Master := [(Sum.inr 539, 2), (Sum.inr 547, 1), (Sum.inr 548, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1338 : Integer.Sparse.reindex keyMap MixedData.row1338 = numericRow1338 := by decide +kernel

theorem numericCheck1338 (x : Master → ℝ) : Integer.Sparse.eval numericRow1338 x =
    (1 : ℝ) * reducedSource1338 x := by
  norm_num [numericRow1338, reducedSource1338, Integer.Sparse.eval, Sparse.eval, nodeValue539, nodeValue547, nodeValue548, nodeValue561, nodeValue816, nodeValue4069]

noncomputable def reducedSource1339 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue816 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1339 : Integer.Sparse Master := [(Sum.inr 734, 2), (Sum.inr 742, 1), (Sum.inr 743, 1), (Sum.inr 1653, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1339 : Integer.Sparse.reindex keyMap MixedData.row1339 = numericRow1339 := by decide +kernel

theorem numericCheck1339 (x : Master → ℝ) : Integer.Sparse.eval numericRow1339 x =
    (1 : ℝ) * reducedSource1339 x := by
  norm_num [numericRow1339, reducedSource1339, Integer.Sparse.eval, Sparse.eval, nodeValue734, nodeValue742, nodeValue743, nodeValue816, nodeValue1653, nodeValue4069]

noncomputable def reducedSource1340 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((2 : ℝ) * Sparse.eval nodeValue4115 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4123 x + ((1 : ℝ) * Sparse.eval nodeValue4132 x + ((2 : ℝ) * Sparse.eval nodeValue4207 x + ((2 : ℝ) * Sparse.eval nodeValue4212 x + ((2 : ℝ) * Sparse.eval nodeValue4214 x + ((2 : ℝ) * Sparse.eval nodeValue4223 x + ((2 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((1 : ℝ) * Sparse.eval nodeValue4284 x + ((2 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + 0)))))))))))))))))))

def numericRow1340 : Integer.Sparse Master := [(Sum.inr 552, -2), (Sum.inr 555, -1), (Sum.inr 562, -1), (Sum.inr 660, -2), (Sum.inr 671, -1), (Sum.inr 679, -1), (Sum.inr 710, -2), (Sum.inr 715, -2), (Sum.inr 724, -2), (Sum.inr 746, -2), (Sum.inr 753, -2), (Sum.inr 758, -2), (Sum.inr 789, -2), (Sum.inr 790, -2), (Sum.inr 815, -1), (Sum.inr 823, -2), (Sum.inr 826, -1), (Sum.inr 830, -2), (Sum.inr 831, -1), (Sum.inr 848, -2), (Sum.inr 858, -1), (Sum.inr 985, -2), (Sum.inr 1049, -1), (Sum.inr 1050, -1), (Sum.inr 1618, -2), (Sum.inr 1738, -1), (Sum.inr 1751, -1), (Sum.inr 4071, 4)]

theorem reindexCheck1340 : Integer.Sparse.reindex keyMap MixedData.row1340 = numericRow1340 := by decide +kernel

theorem numericCheck1340 (x : Master → ℝ) : Integer.Sparse.eval numericRow1340 x =
    (4 : ℝ) * reducedSource1340 x := by
  norm_num [numericRow1340, reducedSource1340, Integer.Sparse.eval, Sparse.eval, nodeValue4071, nodeValue4115, nodeValue4121, nodeValue4123, nodeValue4132, nodeValue4207, nodeValue4212, nodeValue4214, nodeValue4223, nodeValue4255, nodeValue4256, nodeValue4272, nodeValue4273, nodeValue4278, nodeValue4279, nodeValue4284, nodeValue4404, nodeValue4466, nodeValue4467, nodeValue4511]; ring

noncomputable def reducedSource1341 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4059 x + ((2 : ℝ) * Sparse.eval nodeValue4061 x + ((6 : ℝ) * Sparse.eval nodeValue4065 x + ((6 : ℝ) * Sparse.eval nodeValue4067 x + ((6 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))))

def numericRow1341 : Integer.Sparse Master := [(Sum.inr 4059, 3), (Sum.inr 4061, 2), (Sum.inr 4065, 6), (Sum.inr 4067, 6), (Sum.inr 4069, 6), (Sum.inr 4070, 2), (Sum.inr 4082, 3), (Sum.inr 4084, 2)]

theorem reindexCheck1341 : Integer.Sparse.reindex keyMap MixedData.row1341 = numericRow1341 := by decide +kernel

theorem numericCheck1341 (x : Master → ℝ) : Integer.Sparse.eval numericRow1341 x =
    (1 : ℝ) * reducedSource1341 x := by
  norm_num [numericRow1341, reducedSource1341, Integer.Sparse.eval, Sparse.eval, nodeValue4059, nodeValue4061, nodeValue4065, nodeValue4067, nodeValue4069, nodeValue4070, nodeValue4082, nodeValue4084]

noncomputable def reducedSource1342 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1342 : Integer.Sparse Master := [(Sum.inr 1716, 1), (Sum.inr 2521, 1), (Sum.inr 3022, 2), (Sum.inr 3049, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1342 : Integer.Sparse.reindex keyMap MixedData.row1342 = numericRow1342 := by decide +kernel

theorem numericCheck1342 (x : Master → ℝ) : Integer.Sparse.eval numericRow1342 x =
    (1 : ℝ) * reducedSource1342 x := by
  norm_num [numericRow1342, reducedSource1342, Integer.Sparse.eval, Sparse.eval, nodeValue1716, nodeValue2521, nodeValue3022, nodeValue3049, nodeValue3305, nodeValue4069]

noncomputable def reducedSource1343 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1343 : Integer.Sparse Master := [(Sum.inr 1714, 2), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 1739, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1343 : Integer.Sparse.reindex keyMap MixedData.row1343 = numericRow1343 := by decide +kernel

theorem numericCheck1343 (x : Master → ℝ) : Integer.Sparse.eval numericRow1343 x =
    (1 : ℝ) * reducedSource1343 x := by
  norm_num [numericRow1343, reducedSource1343, Integer.Sparse.eval, Sparse.eval, nodeValue1714, nodeValue1716, nodeValue1728, nodeValue1739, nodeValue3305, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
