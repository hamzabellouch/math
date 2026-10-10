import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1504 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1076 x + ((2 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1504 : Integer.Sparse Master := [(Sum.inr 1076, 1), (Sum.inr 2049, 2), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1504 : Integer.Sparse.reindex keyMap MixedData.row1504 = numericRow1504 := by decide +kernel

theorem numericCheck1504 (x : Master → ℝ) : Integer.Sparse.eval numericRow1504 x =
    (1 : ℝ) * reducedSource1504 x := by
  norm_num [numericRow1504, reducedSource1504, Integer.Sparse.eval, Sparse.eval, nodeValue1076, nodeValue2049, nodeValue2230, nodeValue2282, nodeValue2287, nodeValue4081]

noncomputable def reducedSource1505 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4184 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((2 : ℝ) * Sparse.eval nodeValue4353 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4357 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + 0))))))))))))))))))))

def numericRow1505 : Integer.Sparse Master := [(Sum.inr 613, -1), (Sum.inr 932, -2), (Sum.inr 1049, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -1), (Sum.inr 1525, -1), (Sum.inr 1681, -2), (Sum.inr 1708, -2), (Sum.inr 1728, -1), (Sum.inr 1738, -1), (Sum.inr 2058, -2), (Sum.inr 2216, -2), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2279, -2), (Sum.inr 4176, 8), (Sum.inr 4184, 4), (Sum.inr 4188, 4), (Sum.inr 4345, 8), (Sum.inr 4353, 8), (Sum.inr 4357, 8), (Sum.inr 4459, 8), (Sum.inr 4464, 4), (Sum.inr 4475, 8), (Sum.inr 4478, 4), (Sum.inr 4480, 4)]

theorem reindexCheck1505 : Integer.Sparse.reindex keyMap MixedData.row1505 = numericRow1505 := by decide +kernel

theorem numericCheck1505 (x : Master → ℝ) : Integer.Sparse.eval numericRow1505 x =
    (4 : ℝ) * reducedSource1505 x := by
  norm_num [numericRow1505, reducedSource1505, Integer.Sparse.eval, Sparse.eval, nodeValue4176, nodeValue4184, nodeValue4185, nodeValue4188, nodeValue4345, nodeValue4353, nodeValue4354, nodeValue4357, nodeValue4459, nodeValue4464, nodeValue4466, nodeValue4475, nodeValue4478, nodeValue4480, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4839, nodeValue4895, nodeValue4896, nodeValue4898]
  ring

noncomputable def reducedSource1506 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1530 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((2 : ℝ) * Sparse.eval nodeValue1681 x + ((2 : ℝ) * Sparse.eval nodeValue1682 x + ((2 : ℝ) * Sparse.eval nodeValue1686 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + 0))))))))))))))))))))

def numericRow1506 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1530, 1), (Sum.inr 1668, 2), (Sum.inr 1681, 2), (Sum.inr 1682, 2), (Sum.inr 1686, 2), (Sum.inr 1708, 2), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1728, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 2216, 2), (Sum.inr 2278, 1), (Sum.inr 2279, 1)]

theorem reindexCheck1506 : Integer.Sparse.reindex keyMap MixedData.row1506 = numericRow1506 := by decide +kernel

theorem numericCheck1506 (x : Master → ℝ) : Integer.Sparse.eval numericRow1506 x =
    (1 : ℝ) * reducedSource1506 x := by
  norm_num [numericRow1506, reducedSource1506, Integer.Sparse.eval, Sparse.eval, nodeValue1512, nodeValue1525, nodeValue1526, nodeValue1530, nodeValue1668, nodeValue1681, nodeValue1682, nodeValue1686, nodeValue1708, nodeValue1714, nodeValue1715, nodeValue1727, nodeValue1728, nodeValue1738, nodeValue1740, nodeValue1745, nodeValue1746, nodeValue2216, nodeValue2265, nodeValue2278, nodeValue2279]

noncomputable def reducedSource1507 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4400 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((2 : ℝ) * Sparse.eval nodeValue4425 x + ((2 : ℝ) * Sparse.eval nodeValue4427 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4462 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4504 x + ((1 : ℝ) * Sparse.eval nodeValue4506 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + 0))))))))))))))))))))

def numericRow1507 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 12), (Sum.inr 811, -864), (Sum.inr 824, -864), (Sum.inr 828, -432), (Sum.inr 831, -432), (Sum.inr 857, -432), (Sum.inr 858, -432), (Sum.inr 1005, -864), (Sum.inr 1044, -864), (Sum.inr 1083, -432), (Sum.inr 1087, -432), (Sum.inr 1294, -432), (Sum.inr 1623, -864), (Sum.inr 1728, -432), (Sum.inr 1737, -864), (Sum.inr 1739, -432), (Sum.inr 3305, -432), (Sum.inr 3308, -432), (Sum.inr 4400, 3456), (Sum.inr 4425, 3456), (Sum.inr 4427, 3456), (Sum.inr 4459, 3456), (Sum.inr 4462, 3456), (Sum.inr 4500, 1728), (Sum.inr 4504, 1728), (Sum.inr 4506, 1728), (Sum.inr 4607, 3456), (Sum.inr 4617, 1728)]

theorem reindexCheck1507 : Integer.Sparse.reindex keyMap MixedData.row1507 = numericRow1507 := by decide +kernel

theorem numericCheck1507 (x : Master → ℝ) : Integer.Sparse.eval numericRow1507 x =
    (1728 : ℝ) * reducedSource1507 x := by
  norm_num [numericRow1507, reducedSource1507, Integer.Sparse.eval, Sparse.eval, nodeValue4268, nodeValue4276, nodeValue4279, nodeValue4283, nodeValue4400, nodeValue4424, nodeValue4425, nodeValue4427, nodeValue4459, nodeValue4461, nodeValue4462, nodeValue4499, nodeValue4500, nodeValue4502, nodeValue4503, nodeValue4504, nodeValue4506, nodeValue4607, nodeValue4617, nodeValue4619, nodeValue4623]
  ring

noncomputable def reducedSource1508 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4347 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4357 x + ((2 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))))))))))

def numericRow1508 : Integer.Sparse Master := [(Sum.inr 608, -1), (Sum.inr 927, -2), (Sum.inr 1079, -2), (Sum.inr 1083, -2), (Sum.inr 1087, -1), (Sum.inr 1091, -1), (Sum.inr 1519, -1), (Sum.inr 1675, -2), (Sum.inr 1708, -2), (Sum.inr 1728, -2), (Sum.inr 1739, -1), (Sum.inr 1756, -1), (Sum.inr 2054, -2), (Sum.inr 2206, -2), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 4173, 8), (Sum.inr 4178, 4), (Sum.inr 4188, 4), (Sum.inr 4347, 8), (Sum.inr 4357, 8), (Sum.inr 4474, 8), (Sum.inr 4476, 4), (Sum.inr 4480, 4)]

theorem reindexCheck1508 : Integer.Sparse.reindex keyMap MixedData.row1508 = numericRow1508 := by decide +kernel

theorem numericCheck1508 (x : Master → ℝ) : Integer.Sparse.eval numericRow1508 x =
    (4 : ℝ) * reducedSource1508 x := by
  norm_num [numericRow1508, reducedSource1508, Integer.Sparse.eval, Sparse.eval, nodeValue4173, nodeValue4178, nodeValue4180, nodeValue4188, nodeValue4342, nodeValue4347, nodeValue4349, nodeValue4357, nodeValue4474, nodeValue4476, nodeValue4480, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4507, nodeValue4511, nodeValue4835, nodeValue4895, nodeValue4896, nodeValue4901]
  ring

noncomputable def reducedSource1509 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1508 x + ((1 : ℝ) * Sparse.eval nodeValue1519 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((2 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1675 x + ((2 : ℝ) * Sparse.eval nodeValue1676 x + ((2 : ℝ) * Sparse.eval nodeValue1682 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + 0))))))))))))))))))))

def numericRow1509 : Integer.Sparse Master := [(Sum.inr 1508, 2), (Sum.inr 1519, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 1675, 2), (Sum.inr 1676, 2), (Sum.inr 1682, 2), (Sum.inr 1708, 2), (Sum.inr 1709, 2), (Sum.inr 1728, 2), (Sum.inr 1729, 1), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1756, 1), (Sum.inr 2206, 2), (Sum.inr 2266, 1)]

theorem reindexCheck1509 : Integer.Sparse.reindex keyMap MixedData.row1509 = numericRow1509 := by decide +kernel

theorem numericCheck1509 (x : Master → ℝ) : Integer.Sparse.eval numericRow1509 x =
    (1 : ℝ) * reducedSource1509 x := by
  norm_num [numericRow1509, reducedSource1509, Integer.Sparse.eval, Sparse.eval, nodeValue1508, nodeValue1519, nodeValue1520, nodeValue1526, nodeValue1665, nodeValue1675, nodeValue1676, nodeValue1682, nodeValue1708, nodeValue1709, nodeValue1727, nodeValue1728, nodeValue1729, nodeValue1739, nodeValue1740, nodeValue1755, nodeValue1756, nodeValue2206, nodeValue2265, nodeValue2266, nodeValue2293]

noncomputable def reducedSource1510 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4122 x + ((1 : ℝ) * Sparse.eval nodeValue4133 x + ((2 : ℝ) * Sparse.eval nodeValue4301 x + ((2 : ℝ) * Sparse.eval nodeValue4303 x + ((2 : ℝ) * Sparse.eval nodeValue4304 x + ((2 : ℝ) * Sparse.eval nodeValue4314 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

def numericRow1510 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 80), (Sum.inr 554, -4320), (Sum.inr 555, -2160), (Sum.inr 556, -2160), (Sum.inr 563, -2160), (Sum.inr 668, -4320), (Sum.inr 670, -2160), (Sum.inr 671, -2160), (Sum.inr 692, -2160), (Sum.inr 879, -4320), (Sum.inr 881, -4320), (Sum.inr 882, -4320), (Sum.inr 892, -4320), (Sum.inr 1005, -4320), (Sum.inr 1009, -2160), (Sum.inr 1012, -2160), (Sum.inr 1041, -4320), (Sum.inr 1043, -2160), (Sum.inr 1050, -2160), (Sum.inr 1079, -4320), (Sum.inr 1080, -2160), (Sum.inr 1083, -2160), (Sum.inr 1556, -4320), (Sum.inr 1558, -4320), (Sum.inr 1559, -4320), (Sum.inr 1575, -4320), (Sum.inr 1623, -4320), (Sum.inr 1627, -2160), (Sum.inr 1630, -2160), (Sum.inr 1708, -4320), (Sum.inr 1710, -2160), (Sum.inr 1724, -4320), (Sum.inr 1725, -2160), (Sum.inr 1728, -2160), (Sum.inr 1751, -2160), (Sum.inr 2512, -4320), (Sum.inr 2743, -2160), (Sum.inr 3471, -4320), (Sum.inr 3548, -2160), (Sum.inr 3623, -2160), (Sum.inr 3627, -2160)]

theorem reindexCheck1510 : Integer.Sparse.reindex keyMap MixedData.row1510 = numericRow1510 := by decide +kernel

theorem numericCheck1510 (x : Master → ℝ) : Integer.Sparse.eval numericRow1510 x =
    (8640 : ℝ) * reducedSource1510 x := by
  norm_num [numericRow1510, reducedSource1510, Integer.Sparse.eval, Sparse.eval, nodeValue4119, nodeValue4121, nodeValue4122, nodeValue4133, nodeValue4301, nodeValue4303, nodeValue4304, nodeValue4314, nodeValue4424, nodeValue4428, nodeValue4431, nodeValue4458, nodeValue4460, nodeValue4467, nodeValue4495, nodeValue4496, nodeValue4499, nodeValue5102, nodeValue5275, nodeValue5293, nodeValue5306]
  ring

noncomputable def reducedSource1511 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4283 x + ((2 : ℝ) * Sparse.eval nodeValue4397 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((2 : ℝ) * Sparse.eval nodeValue4420 x + ((2 : ℝ) * Sparse.eval nodeValue4424 x + ((2 : ℝ) * Sparse.eval nodeValue4453 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4492 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0))))))))))))))))))))

def numericRow1511 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 807, -8640), (Sum.inr 813, -2160), (Sum.inr 853, -2160), (Sum.inr 1000, -4320), (Sum.inr 1005, -4320), (Sum.inr 1041, -4320), (Sum.inr 1075, -2160), (Sum.inr 1087, -2160), (Sum.inr 1294, -2160), (Sum.inr 1605, -4320), (Sum.inr 1623, -4320), (Sum.inr 1653, -2160), (Sum.inr 1724, -4320), (Sum.inr 1739, -2160), (Sum.inr 3305, -2160), (Sum.inr 3309, -2160), (Sum.inr 4420, 17280), (Sum.inr 4453, 17280), (Sum.inr 4459, 17280), (Sum.inr 4492, 8640), (Sum.inr 4500, 8640), (Sum.inr 4603, 17280), (Sum.inr 4620, 8640)]

theorem reindexCheck1511 : Integer.Sparse.reindex keyMap MixedData.row1511 = numericRow1511 := by decide +kernel

theorem numericCheck1511 (x : Master → ℝ) : Integer.Sparse.eval numericRow1511 x =
    (8640 : ℝ) * reducedSource1511 x := by
  norm_num [numericRow1511, reducedSource1511, Integer.Sparse.eval, Sparse.eval, nodeValue4265, nodeValue4270, nodeValue4273, nodeValue4283, nodeValue4397, nodeValue4419, nodeValue4420, nodeValue4424, nodeValue4453, nodeValue4458, nodeValue4459, nodeValue4491, nodeValue4492, nodeValue4498, nodeValue4500, nodeValue4502, nodeValue4503, nodeValue4603, nodeValue4619, nodeValue4620, nodeValue4624]
  ring

noncomputable def reducedSource1512 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1075 x + ((2 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1512 : Integer.Sparse Master := [(Sum.inr 1075, 1), (Sum.inr 2048, 2), (Sum.inr 2276, 1), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1512 : Integer.Sparse.reindex keyMap MixedData.row1512 = numericRow1512 := by decide +kernel

theorem numericCheck1512 (x : Master → ℝ) : Integer.Sparse.eval numericRow1512 x =
    (1 : ℝ) * reducedSource1512 x := by
  norm_num [numericRow1512, reducedSource1512, Integer.Sparse.eval, Sparse.eval, nodeValue1075, nodeValue2048, nodeValue2229, nodeValue2276, nodeValue2288, nodeValue4082]

noncomputable def reducedSource1513 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((4 : ℝ) * Sparse.eval nodeValue4355 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))

def numericRow1513 : Integer.Sparse Master := [(Sum.inr 603, -2), (Sum.inr 611, -1), (Sum.inr 614, -2), (Sum.inr 922, -2), (Sum.inr 930, -2), (Sum.inr 933, -4), (Sum.inr 1041, -4), (Sum.inr 1046, -2), (Sum.inr 1050, -2), (Sum.inr 1517, -2), (Sum.inr 1535, -1), (Sum.inr 1536, -2), (Sum.inr 1673, -2), (Sum.inr 1690, -2), (Sum.inr 1691, -4), (Sum.inr 1724, -4), (Sum.inr 1750, -2), (Sum.inr 1751, -2), (Sum.inr 4083, 4)]

theorem reindexCheck1513 : Integer.Sparse.reindex keyMap MixedData.row1513 = numericRow1513 := by decide +kernel

theorem numericCheck1513 (x : Master → ℝ) : Integer.Sparse.eval numericRow1513 x =
    (4 : ℝ) * reducedSource1513 x := by
  norm_num [numericRow1513, reducedSource1513, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4175, nodeValue4183, nodeValue4186, nodeValue4344, nodeValue4352, nodeValue4355, nodeValue4458, nodeValue4463, nodeValue4467, nodeValue4497, nodeValue4502, nodeValue4838, nodeValue4895]
  ring

noncomputable def reducedSource1514 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

def numericRow1514 : Integer.Sparse Master := [(Sum.inr 600, -2), (Sum.inr 605, -1), (Sum.inr 608, -1), (Sum.inr 613, -1), (Sum.inr 919, -2), (Sum.inr 924, -2), (Sum.inr 927, -2), (Sum.inr 932, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -1), (Sum.inr 1049, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -1), (Sum.inr 1087, -1), (Sum.inr 1507, -2), (Sum.inr 1518, -1), (Sum.inr 1519, -1), (Sum.inr 1525, -1), (Sum.inr 1664, -2), (Sum.inr 1674, -2), (Sum.inr 1675, -2), (Sum.inr 1681, -2), (Sum.inr 1707, -2), (Sum.inr 1708, -2), (Sum.inr 1725, -1), (Sum.inr 1728, -1), (Sum.inr 1738, -1), (Sum.inr 1739, -1), (Sum.inr 4084, 4)]

theorem reindexCheck1514 : Integer.Sparse.reindex keyMap MixedData.row1514 = numericRow1514 := by decide +kernel

theorem numericCheck1514 (x : Master → ℝ) : Integer.Sparse.eval numericRow1514 x =
    (4 : ℝ) * reducedSource1514 x := by
  norm_num [numericRow1514, reducedSource1514, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4172, nodeValue4177, nodeValue4180, nodeValue4185, nodeValue4341, nodeValue4346, nodeValue4349, nodeValue4354, nodeValue4457, nodeValue4460, nodeValue4466, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4505, nodeValue4511, nodeValue4834, nodeValue4894, nodeValue4895]
  ring

noncomputable def reducedSource1515 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1074 x + ((2 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1515 : Integer.Sparse Master := [(Sum.inr 1074, 1), (Sum.inr 2047, 2), (Sum.inr 2261, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1515 : Integer.Sparse.reindex keyMap MixedData.row1515 = numericRow1515 := by decide +kernel

theorem numericCheck1515 (x : Master → ℝ) : Integer.Sparse.eval numericRow1515 x =
    (1 : ℝ) * reducedSource1515 x := by
  norm_num [numericRow1515, reducedSource1515, Integer.Sparse.eval, Sparse.eval, nodeValue1074, nodeValue2047, nodeValue2228, nodeValue2261, nodeValue2287, nodeValue4081]

noncomputable def reducedSource1516 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4170 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4179 x + ((2 : ℝ) * Sparse.eval nodeValue4340 x + ((2 : ℝ) * Sparse.eval nodeValue4343 x + ((4 : ℝ) * Sparse.eval nodeValue4348 x + ((2 : ℝ) * Sparse.eval nodeValue4494 x + ((4 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue4501 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + 0)))))))))))))

def numericRow1516 : Integer.Sparse Master := [(Sum.inr 602, -1), (Sum.inr 921, -2), (Sum.inr 1080, -4), (Sum.inr 1094, -2), (Sum.inr 1509, -1), (Sum.inr 1666, -2), (Sum.inr 1710, -4), (Sum.inr 1741, -2), (Sum.inr 2052, -2), (Sum.inr 2193, -2), (Sum.inr 2247, -1), (Sum.inr 2290, -1), (Sum.inr 4170, 8), (Sum.inr 4179, 8), (Sum.inr 4348, 16), (Sum.inr 4494, 8), (Sum.inr 4500, 8)]

theorem reindexCheck1516 : Integer.Sparse.reindex keyMap MixedData.row1516 = numericRow1516 := by decide +kernel

theorem numericCheck1516 (x : Master → ℝ) : Integer.Sparse.eval numericRow1516 x =
    (4 : ℝ) * reducedSource1516 x := by
  norm_num [numericRow1516, reducedSource1516, Integer.Sparse.eval, Sparse.eval, nodeValue4170, nodeValue4174, nodeValue4179, nodeValue4340, nodeValue4343, nodeValue4348, nodeValue4494, nodeValue4496, nodeValue4500, nodeValue4501, nodeValue4510, nodeValue4832, nodeValue4890, nodeValue4897]
  ring

noncomputable def reducedSource1517 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue651 x + ((1 : ℝ) * Sparse.eval nodeValue652 x + ((2 : ℝ) * Sparse.eval nodeValue653 x + ((2 : ℝ) * Sparse.eval nodeValue1345 x + ((2 : ℝ) * Sparse.eval nodeValue1346 x + ((4 : ℝ) * Sparse.eval nodeValue1347 x + ((2 : ℝ) * Sparse.eval nodeValue1435 x + ((2 : ℝ) * Sparse.eval nodeValue1436 x + ((4 : ℝ) * Sparse.eval nodeValue1451 x + ((2 : ℝ) * Sparse.eval nodeValue1452 x + ((2 : ℝ) * Sparse.eval nodeValue1454 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + 0)))))))))))))

def numericRow1517 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, -40), (Sum.inl 2, -520), (Sum.inl 35, -160), (Sum.inl 1, 10), (Sum.inr 651, 2160), (Sum.inr 653, 2160), (Sum.inr 1347, 4320), (Sum.inr 1435, 2160), (Sum.inr 1436, 2160)]

theorem reindexCheck1517 : Integer.Sparse.reindex keyMap MixedData.row1517 = numericRow1517 := by decide +kernel

theorem numericCheck1517 (x : Master → ℝ) : Integer.Sparse.eval numericRow1517 x =
    (1080 : ℝ) * reducedSource1517 x := by
  norm_num [numericRow1517, reducedSource1517, Integer.Sparse.eval, Sparse.eval, nodeValue651, nodeValue652, nodeValue653, nodeValue1345, nodeValue1346, nodeValue1347, nodeValue1435, nodeValue1436, nodeValue1451, nodeValue1452, nodeValue1454, nodeValue2755, nodeValue3082, nodeValue3114]
  ring

noncomputable def reducedSource1518 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1503 x + ((1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1513 x + ((2 : ℝ) * Sparse.eval nodeValue1662 x + ((2 : ℝ) * Sparse.eval nodeValue1666 x + ((4 : ℝ) * Sparse.eval nodeValue1669 x + ((2 : ℝ) * Sparse.eval nodeValue1700 x + ((4 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue1730 x + ((2 : ℝ) * Sparse.eval nodeValue1741 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + 0)))))))))))))

def numericRow1518 : Integer.Sparse Master := [(Sum.inr 1503, 2), (Sum.inr 1509, 1), (Sum.inr 1513, 2), (Sum.inr 1666, 2), (Sum.inr 1669, 4), (Sum.inr 1700, 2), (Sum.inr 1710, 4), (Sum.inr 1716, 2), (Sum.inr 1741, 2), (Sum.inr 2193, 2), (Sum.inr 2247, 1)]

theorem reindexCheck1518 : Integer.Sparse.reindex keyMap MixedData.row1518 = numericRow1518 := by decide +kernel

theorem numericCheck1518 (x : Master → ℝ) : Integer.Sparse.eval numericRow1518 x =
    (1 : ℝ) * reducedSource1518 x := by
  norm_num [numericRow1518, reducedSource1518, Integer.Sparse.eval, Sparse.eval, nodeValue1503, nodeValue1509, nodeValue1513, nodeValue1662, nodeValue1666, nodeValue1669, nodeValue1700, nodeValue1710, nodeValue1716, nodeValue1730, nodeValue1741, nodeValue2193, nodeValue2247, nodeValue2268]

noncomputable def reducedSource1519 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue598 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1519 : Integer.Sparse Master := [(Sum.inr 598, 2), (Sum.inr 602, 1), (Sum.inr 607, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1519 : Integer.Sparse.reindex keyMap MixedData.row1519 = numericRow1519 := by decide +kernel

theorem numericCheck1519 (x : Master → ℝ) : Integer.Sparse.eval numericRow1519 x =
    (1 : ℝ) * reducedSource1519 x := by
  norm_num [numericRow1519, reducedSource1519, Integer.Sparse.eval, Sparse.eval, nodeValue598, nodeValue602, nodeValue607, nodeValue1080, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
