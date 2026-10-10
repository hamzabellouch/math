import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1584 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4150 x + ((2 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((2 : ℝ) * Sparse.eval nodeValue4364 x + ((2 : ℝ) * Sparse.eval nodeValue4366 x + ((2 : ℝ) * Sparse.eval nodeValue4438 x + ((4 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4456 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + 0)))))))))))))

def numericRow1584 : Integer.Sparse Master := [(Sum.inr 599, -1), (Sum.inr 1039, -2), (Sum.inr 1041, -4), (Sum.inr 1044, -2), (Sum.inr 1506, -1), (Sum.inr 1706, -2), (Sum.inr 1724, -4), (Sum.inr 1737, -2), (Sum.inr 2105, -1), (Sum.inr 2241, -1), (Sum.inr 2243, -4), (Sum.inr 4150, 8), (Sum.inr 4152, 8), (Sum.inr 4364, 8), (Sum.inr 4366, 8), (Sum.inr 4439, 16)]

theorem reindexCheck1584 : Integer.Sparse.reindex keyMap MixedData.row1584 = numericRow1584 := by decide +kernel

theorem numericCheck1584 (x : Master → ℝ) : Integer.Sparse.eval numericRow1584 x =
    (4 : ℝ) * reducedSource1584 x := by
  norm_num [numericRow1584, reducedSource1584, Integer.Sparse.eval, Sparse.eval, nodeValue4150, nodeValue4152, nodeValue4171, nodeValue4364, nodeValue4366, nodeValue4438, nodeValue4439, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4497, nodeValue4864, nodeValue4887, nodeValue4893]
  ring

noncomputable def reducedSource1585 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1506 x + ((2 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1703 x + ((2 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1711 x + ((4 : ℝ) * Sparse.eval nodeValue1713 x + ((4 : ℝ) * Sparse.eval nodeValue1724 x + ((2 : ℝ) * Sparse.eval nodeValue1726 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + 0)))))))))))))

def numericRow1585 : Integer.Sparse Master := [(Sum.inr 1504, 2), (Sum.inr 1506, 1), (Sum.inr 1510, 2), (Sum.inr 1703, 2), (Sum.inr 1706, 2), (Sum.inr 1711, 2), (Sum.inr 1713, 4), (Sum.inr 1724, 4), (Sum.inr 1737, 2), (Sum.inr 2241, 1), (Sum.inr 2243, 2)]

theorem reindexCheck1585 : Integer.Sparse.reindex keyMap MixedData.row1585 = numericRow1585 := by decide +kernel

theorem numericCheck1585 (x : Master → ℝ) : Integer.Sparse.eval numericRow1585 x =
    (1 : ℝ) * reducedSource1585 x := by
  norm_num [numericRow1585, reducedSource1585, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1506, nodeValue1510, nodeValue1703, nodeValue1705, nodeValue1706, nodeValue1711, nodeValue1713, nodeValue1724, nodeValue1726, nodeValue1737, nodeValue2241, nodeValue2243, nodeValue2263]

noncomputable def reducedSource1586 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue599 x + ((3 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1081 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))

def numericRow1586 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 1039, 3), (Sum.inr 4083, -1)]

theorem reindexCheck1586 : Integer.Sparse.reindex keyMap MixedData.row1586 = numericRow1586 := by decide +kernel

theorem numericCheck1586 (x : Master → ℝ) : Integer.Sparse.eval numericRow1586 x =
    (1 : ℝ) * reducedSource1586 x := by
  norm_num [numericRow1586, reducedSource1586, Integer.Sparse.eval, Sparse.eval, nodeValue599, nodeValue1039, nodeValue1081, nodeValue4083]

noncomputable def reducedSource1587 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4098 x + ((2 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4113 x + ((2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((4 : ℝ) * Sparse.eval nodeValue4396 x + ((2 : ℝ) * Sparse.eval nodeValue4399 x + ((2 : ℝ) * Sparse.eval nodeValue4417 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + 0)))))))))))))

def numericRow1587 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 15), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 1, -110), (Sum.inr 535, -8640), (Sum.inr 537, -8640), (Sum.inr 550, -4320), (Sum.inr 656, -8640), (Sum.inr 658, -4320), (Sum.inr 662, -8640), (Sum.inr 919, -8640), (Sum.inr 922, -8640), (Sum.inr 977, -17280), (Sum.inr 980, -8640), (Sum.inr 998, -8640), (Sum.inr 1040, -8640), (Sum.inr 1041, -17280), (Sum.inr 1079, -8640), (Sum.inr 1597, -17280), (Sum.inr 1600, -8640), (Sum.inr 1616, -8640), (Sum.inr 1664, -8640), (Sum.inr 1673, -8640), (Sum.inr 1707, -8640), (Sum.inr 1708, -8640), (Sum.inr 1724, -17280), (Sum.inr 2721, -8640), (Sum.inr 3532, -8640), (Sum.inr 3602, -4320), (Sum.inr 3622, -8640)]

theorem reindexCheck1587 : Integer.Sparse.reindex keyMap MixedData.row1587 = numericRow1587 := by decide +kernel

theorem numericCheck1587 (x : Master → ℝ) : Integer.Sparse.eval numericRow1587 x =
    (17280 : ℝ) * reducedSource1587 x := by
  norm_num [numericRow1587, reducedSource1587, Integer.Sparse.eval, Sparse.eval, nodeValue4098, nodeValue4100, nodeValue4113, nodeValue4341, nodeValue4344, nodeValue4396, nodeValue4399, nodeValue4417, nodeValue4457, nodeValue4458, nodeValue4495, nodeValue5167, nodeValue5257, nodeValue5292]
  ring

noncomputable def reducedSource1588 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue535 x + ((2 : ℝ) * Sparse.eval nodeValue537 x + ((1 : ℝ) * Sparse.eval nodeValue550 x + ((2 : ℝ) * Sparse.eval nodeValue919 x + ((2 : ℝ) * Sparse.eval nodeValue922 x + ((4 : ℝ) * Sparse.eval nodeValue977 x + ((2 : ℝ) * Sparse.eval nodeValue980 x + ((2 : ℝ) * Sparse.eval nodeValue998 x + ((2 : ℝ) * Sparse.eval nodeValue1040 x + ((4 : ℝ) * Sparse.eval nodeValue1041 x + ((2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + 0)))))))))))))

def numericRow1588 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, 110), (Sum.inr 535, 8640), (Sum.inr 537, 8640), (Sum.inr 550, 4320), (Sum.inr 919, 8640), (Sum.inr 922, 8640), (Sum.inr 977, 17280), (Sum.inr 980, 8640), (Sum.inr 998, 8640), (Sum.inr 1040, 8640), (Sum.inr 1041, 17280), (Sum.inr 1079, 8640), (Sum.inr 2721, 8640)]

theorem reindexCheck1588 : Integer.Sparse.reindex keyMap MixedData.row1588 = numericRow1588 := by decide +kernel

theorem numericCheck1588 (x : Master → ℝ) : Integer.Sparse.eval numericRow1588 x =
    (4320 : ℝ) * reducedSource1588 x := by
  norm_num [numericRow1588, reducedSource1588, Integer.Sparse.eval, Sparse.eval, nodeValue535, nodeValue537, nodeValue550, nodeValue919, nodeValue922, nodeValue977, nodeValue980, nodeValue998, nodeValue1040, nodeValue1041, nodeValue1079, nodeValue2593, nodeValue2721, nodeValue2766]
  ring

noncomputable def reducedSource1589 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4263 x + ((4 : ℝ) * Sparse.eval nodeValue4449 x + ((2 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4455 x + ((4 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4469 x + ((2 : ℝ) * Sparse.eval nodeValue4473 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4599 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + 0)))))))))))))

def numericRow1589 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 6, -15), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -70), (Sum.inr 783, -8640), (Sum.inr 786, -4320), (Sum.inr 803, -8640), (Sum.inr 822, -4320), (Sum.inr 1034, -8640), (Sum.inr 1039, -17280), (Sum.inr 1079, -8640), (Sum.inr 1235, -8640), (Sum.inr 1644, -8640), (Sum.inr 1706, -17280), (Sum.inr 1708, -8640), (Sum.inr 3292, -8640), (Sum.inr 3307, -4320), (Sum.inr 4449, 69120), (Sum.inr 4469, 34560), (Sum.inr 4473, 34560), (Sum.inr 4599, 34560)]

theorem reindexCheck1589 : Integer.Sparse.reindex keyMap MixedData.row1589 = numericRow1589 := by decide +kernel

theorem numericCheck1589 (x : Master → ℝ) : Integer.Sparse.eval numericRow1589 x =
    (17280 : ℝ) * reducedSource1589 x := by
  norm_num [numericRow1589, reducedSource1589, Integer.Sparse.eval, Sparse.eval, nodeValue4249, nodeValue4252, nodeValue4263, nodeValue4449, nodeValue4451, nodeValue4455, nodeValue4456, nodeValue4469, nodeValue4473, nodeValue4495, nodeValue4497, nodeValue4599, nodeValue4601, nodeValue4622]
  ring

noncomputable def reducedSource1590 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1590 : Integer.Sparse Master := [(Sum.inr 1070, 1), (Sum.inr 2043, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1590 : Integer.Sparse.reindex keyMap MixedData.row1590 = numericRow1590 := by decide +kernel

theorem numericCheck1590 (x : Master → ℝ) : Integer.Sparse.eval numericRow1590 x =
    (1 : ℝ) * reducedSource1590 x := by
  norm_num [numericRow1590, reducedSource1590, Integer.Sparse.eval, Sparse.eval, nodeValue1070, nodeValue2043, nodeValue2220, nodeValue2224, nodeValue2259, nodeValue2287, nodeValue4081]

noncomputable def reducedSource1591 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1591 : Integer.Sparse Master := [(Sum.inr 1071, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 2), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1591 : Integer.Sparse.reindex keyMap MixedData.row1591 = numericRow1591 := by decide +kernel

theorem numericCheck1591 (x : Master → ℝ) : Integer.Sparse.eval numericRow1591 x =
    (1 : ℝ) * reducedSource1591 x := by
  norm_num [numericRow1591, reducedSource1591, Integer.Sparse.eval, Sparse.eval, nodeValue1071, nodeValue2044, nodeValue2225, nodeValue2274, nodeValue2288, nodeValue4082]

noncomputable def reducedSource1592 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2046 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1592 : Integer.Sparse Master := [(Sum.inr 1073, 1), (Sum.inr 2046, 1), (Sum.inr 2260, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1592 : Integer.Sparse.reindex keyMap MixedData.row1592 = numericRow1592 := by decide +kernel

theorem numericCheck1592 (x : Master → ℝ) : Integer.Sparse.eval numericRow1592 x =
    (1 : ℝ) * reducedSource1592 x := by
  norm_num [numericRow1592, reducedSource1592, Integer.Sparse.eval, Sparse.eval, nodeValue1073, nodeValue2046, nodeValue2227, nodeValue2260, nodeValue2275, nodeValue4080]

noncomputable def reducedSource1593 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4169 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4173 x + ((2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4455 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

def numericRow1593 : Integer.Sparse Master := [(Sum.inr 600, -1), (Sum.inr 919, -1), (Sum.inr 1040, -1), (Sum.inr 1079, -2), (Sum.inr 1083, -2), (Sum.inr 1087, -2), (Sum.inr 1507, -1), (Sum.inr 1664, -1), (Sum.inr 1707, -1), (Sum.inr 1708, -2), (Sum.inr 1728, -2), (Sum.inr 1739, -2), (Sum.inr 2051, -1), (Sum.inr 2191, -1), (Sum.inr 2244, -1), (Sum.inr 2245, -1), (Sum.inr 2262, -1), (Sum.inr 2277, -1), (Sum.inr 4169, 4), (Sum.inr 4173, 4), (Sum.inr 4176, 8), (Sum.inr 4345, 8), (Sum.inr 4459, 8), (Sum.inr 4473, 4), (Sum.inr 4474, 4), (Sum.inr 4475, 8)]

theorem reindexCheck1593 : Integer.Sparse.reindex keyMap MixedData.row1593 = numericRow1593 := by decide +kernel

theorem numericCheck1593 (x : Master → ℝ) : Integer.Sparse.eval numericRow1593 x =
    (4 : ℝ) * reducedSource1593 x := by
  norm_num [numericRow1593, reducedSource1593, Integer.Sparse.eval, Sparse.eval, nodeValue4169, nodeValue4172, nodeValue4173, nodeValue4176, nodeValue4341, nodeValue4342, nodeValue4345, nodeValue4455, nodeValue4457, nodeValue4459, nodeValue4473, nodeValue4474, nodeValue4475, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4831, nodeValue4888, nodeValue4889, nodeValue4895]
  ring

noncomputable def reducedSource1594 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1502 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1664 x + ((1 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((2 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((2 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1728 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + 0))))))))))))))))))))

def numericRow1594 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1512, 2), (Sum.inr 1664, 1), (Sum.inr 1668, 2), (Sum.inr 1699, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 2), (Sum.inr 1709, 1), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1728, 2), (Sum.inr 1739, 2), (Sum.inr 2191, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1)]

theorem reindexCheck1594 : Integer.Sparse.reindex keyMap MixedData.row1594 = numericRow1594 := by decide +kernel

theorem numericCheck1594 (x : Master → ℝ) : Integer.Sparse.eval numericRow1594 x =
    (1 : ℝ) * reducedSource1594 x := by
  norm_num [numericRow1594, reducedSource1594, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1507, nodeValue1508, nodeValue1512, nodeValue1664, nodeValue1665, nodeValue1668, nodeValue1698, nodeValue1699, nodeValue1707, nodeValue1708, nodeValue1709, nodeValue1714, nodeValue1715, nodeValue1727, nodeValue1728, nodeValue1739, nodeValue2191, nodeValue2244, nodeValue2245, nodeValue2265]

noncomputable def reducedSource1595 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4171 x + ((3 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((3 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((3 : ℝ) * Sparse.eval nodeValue4456 x + ((6 : ℝ) * Sparse.eval nodeValue4458 x + ((3 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((3 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4893 x + 0))))))))))))

def numericRow1595 : Integer.Sparse Master := [(Sum.inr 599, -1), (Sum.inr 603, -3), (Sum.inr 610, -1), (Sum.inr 922, -3), (Sum.inr 929, -1), (Sum.inr 1039, -3), (Sum.inr 1041, -6), (Sum.inr 1044, -3), (Sum.inr 1506, -1), (Sum.inr 1517, -3), (Sum.inr 1524, -1), (Sum.inr 1673, -3), (Sum.inr 1680, -1), (Sum.inr 1706, -3), (Sum.inr 1724, -6), (Sum.inr 1737, -3), (Sum.inr 4083, 4)]

theorem reindexCheck1595 : Integer.Sparse.reindex keyMap MixedData.row1595 = numericRow1595 := by decide +kernel

theorem numericCheck1595 (x : Master → ℝ) : Integer.Sparse.eval numericRow1595 x =
    (4 : ℝ) * reducedSource1595 x := by
  norm_num [numericRow1595, reducedSource1595, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4171, nodeValue4175, nodeValue4182, nodeValue4344, nodeValue4351, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4497, nodeValue4502, nodeValue4833, nodeValue4893]
  ring

noncomputable def reducedSource1596 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue1940 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1596 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 2219, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1596 : Integer.Sparse.reindex keyMap MixedData.row1596 = numericRow1596 := by decide +kernel

theorem numericCheck1596 (x : Master → ℝ) : Integer.Sparse.eval numericRow1596 x =
    (1 : ℝ) * reducedSource1596 x := by
  norm_num [numericRow1596, reducedSource1596, Integer.Sparse.eval, Sparse.eval, nodeValue995, nodeValue1940, nodeValue2201, nodeValue2219, nodeValue2224, nodeValue4081]

noncomputable def reducedSource1597 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue996 x + ((1 : ℝ) * Sparse.eval nodeValue1941 x + ((2 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

def numericRow1597 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 2213, 2), (Sum.inr 2225, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1597 : Integer.Sparse.reindex keyMap MixedData.row1597 = numericRow1597 := by decide +kernel

theorem numericCheck1597 (x : Master → ℝ) : Integer.Sparse.eval numericRow1597 x =
    (1 : ℝ) * reducedSource1597 x := by
  norm_num [numericRow1597, reducedSource1597, Integer.Sparse.eval, Sparse.eval, nodeValue996, nodeValue1941, nodeValue2213, nodeValue2225, nodeValue4082]

noncomputable def reducedSource1598 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4079 x + ((4 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4164 x + ((4 : ℝ) * Sparse.eval nodeValue4306 x + ((12 : ℝ) * Sparse.eval nodeValue4399 x + ((4 : ℝ) * Sparse.eval nodeValue4451 x + ((4 : ℝ) * Sparse.eval nodeValue4833 x + 0))))))

def numericRow1598 : Integer.Sparse Master := [(Sum.inr 571, -4), (Sum.inr 592, -1), (Sum.inr 980, -12), (Sum.inr 1034, -4), (Sum.inr 1491, -4), (Sum.inr 1497, -1), (Sum.inr 1616, -12), (Sum.inr 1644, -4), (Sum.inr 4079, 4)]

theorem reindexCheck1598 : Integer.Sparse.reindex keyMap MixedData.row1598 = numericRow1598 := by decide +kernel

theorem numericCheck1598 (x : Master → ℝ) : Integer.Sparse.eval numericRow1598 x =
    (4 : ℝ) * reducedSource1598 x := by
  norm_num [numericRow1598, reducedSource1598, Integer.Sparse.eval, Sparse.eval, nodeValue4079, nodeValue4143, nodeValue4164, nodeValue4306, nodeValue4399, nodeValue4451, nodeValue4833]
  ring

noncomputable def reducedSource1599 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4068 x + ((3 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4104 x + ((1 : ℝ) * Sparse.eval nodeValue4117 x + ((3 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4236 x + ((6 : ℝ) * Sparse.eval nodeValue4249 x + ((3 : ℝ) * Sparse.eval nodeValue4252 x + ((3 : ℝ) * Sparse.eval nodeValue4263 x + ((3 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((3 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + 0))))))))))))

def numericRow1599 : Integer.Sparse Master := [(Sum.inr 537, -3), (Sum.inr 541, -1), (Sum.inr 662, -3), (Sum.inr 674, -1), (Sum.inr 732, -3), (Sum.inr 736, -1), (Sum.inr 783, -6), (Sum.inr 786, -3), (Sum.inr 798, -3), (Sum.inr 803, -6), (Sum.inr 818, -1), (Sum.inr 822, -3), (Sum.inr 1034, -1), (Sum.inr 1039, -3), (Sum.inr 1644, -1), (Sum.inr 1706, -3), (Sum.inr 4068, 4)]

theorem reindexCheck1599 : Integer.Sparse.reindex keyMap MixedData.row1599 = numericRow1599 := by decide +kernel

theorem numericCheck1599 (x : Master → ℝ) : Integer.Sparse.eval numericRow1599 x =
    (4 : ℝ) * reducedSource1599 x := by
  norm_num [numericRow1599, reducedSource1599, Integer.Sparse.eval, Sparse.eval, nodeValue4068, nodeValue4100, nodeValue4104, nodeValue4117, nodeValue4232, nodeValue4236, nodeValue4249, nodeValue4252, nodeValue4263, nodeValue4267, nodeValue4451, nodeValue4456, nodeValue4497]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
