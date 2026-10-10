import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1680 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1680 : Integer.Sparse Master := [(Sum.inr 2390, 1), (Sum.inr 2393, 1), (Sum.inr 2395, 1), (Sum.inr 2404, 1), (Sum.inr 2678, 1), (Sum.inr 3771, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1680 : Integer.Sparse.reindex keyMap MixedData.row1680 = numericRow1680 := by decide +kernel

theorem numericCheck1680 (x : Master → ℝ) : Integer.Sparse.eval numericRow1680 x =
    (1 : ℝ) * reducedSource1680 x := by
  norm_num [numericRow1680, reducedSource1680, Integer.Sparse.eval, Sparse.eval, nodeValue2390, nodeValue2393, nodeValue2395, nodeValue2404, nodeValue2678, nodeValue3771, nodeValue4088]

noncomputable def reducedSource1681 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1898 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue1912 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

def numericRow1681 : Integer.Sparse Master := [(Sum.inr 1898, 1), (Sum.inr 1901, 1), (Sum.inr 2191, 1), (Sum.inr 3460, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1681 : Integer.Sparse.reindex keyMap MixedData.row1681 = numericRow1681 := by decide +kernel

theorem numericCheck1681 (x : Master → ℝ) : Integer.Sparse.eval numericRow1681 x =
    (1 : ℝ) * reducedSource1681 x := by
  norm_num [numericRow1681, reducedSource1681, Integer.Sparse.eval, Sparse.eval, nodeValue1898, nodeValue1901, nodeValue1912, nodeValue2191, nodeValue3460, nodeValue4079]

noncomputable def reducedSource1682 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1682 : Integer.Sparse Master := [(Sum.inr 2076, 1), (Sum.inr 2080, 1), (Sum.inr 2082, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 3565, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1682 : Integer.Sparse.reindex keyMap MixedData.row1682 = numericRow1682 := by decide +kernel

theorem numericCheck1682 (x : Master → ℝ) : Integer.Sparse.eval numericRow1682 x =
    (1 : ℝ) * reducedSource1682 x := by
  norm_num [numericRow1682, reducedSource1682, Integer.Sparse.eval, Sparse.eval, nodeValue2076, nodeValue2080, nodeValue2082, nodeValue2102, nodeValue2206, nodeValue3565, nodeValue4080]

noncomputable def reducedSource1683 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue2811 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1683 : Integer.Sparse Master := [(Sum.inr 1325, 1), (Sum.inr 2811, 2), (Sum.inr 2820, 1), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1683 : Integer.Sparse.reindex keyMap MixedData.row1683 = numericRow1683 := by decide +kernel

theorem numericCheck1683 (x : Master → ℝ) : Integer.Sparse.eval numericRow1683 x =
    (1 : ℝ) * reducedSource1683 x := by
  norm_num [numericRow1683, reducedSource1683, Integer.Sparse.eval, Sparse.eval, nodeValue1325, nodeValue2811, nodeValue2820, nodeValue2886, nodeValue2889, nodeValue4092]

noncomputable def reducedSource1684 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5034 x + ((2 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + 0))))))))))))))))))))

def numericRow1684 : Integer.Sparse Master := [(Sum.inr 1145, -1), (Sum.inr 2345, -1), (Sum.inr 2434, -2), (Sum.inr 2512, -2), (Sum.inr 2743, -1), (Sum.inr 2881, -2), (Sum.inr 2889, -1), (Sum.inr 3054, -1), (Sum.inr 3277, -1), (Sum.inr 3423, -1), (Sum.inr 3457, -2), (Sum.inr 3471, -2), (Sum.inr 3548, -1), (Sum.inr 3624, -2), (Sum.inr 3626, -1), (Sum.inr 3631, -1), (Sum.inr 4367, 8), (Sum.inr 4370, 4), (Sum.inr 4374, 4), (Sum.inr 4476, 4), (Sum.inr 4547, 8), (Sum.inr 4609, 4), (Sum.inr 4944, 8), (Sum.inr 5034, 8), (Sum.inr 5087, 8), (Sum.inr 5139, 8), (Sum.inr 5268, 4)]

theorem reindexCheck1684 : Integer.Sparse.reindex keyMap MixedData.row1684 = numericRow1684 := by decide +kernel

theorem numericCheck1684 (x : Master → ℝ) : Integer.Sparse.eval numericRow1684 x =
    (4 : ℝ) * reducedSource1684 x := by
  norm_num [numericRow1684, reducedSource1684, Integer.Sparse.eval, Sparse.eval, nodeValue4367, nodeValue4370, nodeValue4374, nodeValue4476, nodeValue4547, nodeValue4559, nodeValue4609, nodeValue4944, nodeValue4953, nodeValue4972, nodeValue5034, nodeValue5087, nodeValue5102, nodeValue5111, nodeValue5139, nodeValue5204, nodeValue5207, nodeValue5268, nodeValue5275, nodeValue5302, nodeValue5413]; ring

noncomputable def reducedSource1685 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3451 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + 0))))))))))))))))))))

def numericRow1685 : Integer.Sparse Master := [(Sum.inr 1720, 2), (Sum.inr 1722, 1), (Sum.inr 1729, 1), (Sum.inr 1748, 1), (Sum.inr 3266, 2), (Sum.inr 3277, 1), (Sum.inr 3302, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3451, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3472, 2), (Sum.inr 3523, 2), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3631, 1)]

theorem reindexCheck1685 : Integer.Sparse.reindex keyMap MixedData.row1685 = numericRow1685 := by decide +kernel

theorem numericCheck1685 (x : Master → ℝ) : Integer.Sparse.eval numericRow1685 x =
    (1 : ℝ) * reducedSource1685 x := by
  norm_num [numericRow1685, reducedSource1685, Integer.Sparse.eval, Sparse.eval, nodeValue1720, nodeValue1722, nodeValue1729, nodeValue1748, nodeValue3266, nodeValue3277, nodeValue3302, nodeValue3413, nodeValue3423, nodeValue3451, nodeValue3457, nodeValue3471, nodeValue3472, nodeValue3485, nodeValue3523, nodeValue3548, nodeValue3549, nodeValue3624, nodeValue3626, nodeValue3631, nodeValue3817]

noncomputable def reducedSource1686 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4219 x + ((1 : ℝ) * Sparse.eval nodeValue4225 x + ((1 : ℝ) * Sparse.eval nodeValue4229 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((2 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4650 x + ((1 : ℝ) * Sparse.eval nodeValue4657 x + ((2 : ℝ) * Sparse.eval nodeValue4713 x + ((2 : ℝ) * Sparse.eval nodeValue4719 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

def numericRow1686 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 5), (Sum.inr 720, -2160), (Sum.inr 726, -1080), (Sum.inr 729, -1080), (Sum.inr 769, -2160), (Sum.inr 773, -1080), (Sum.inr 774, -1080), (Sum.inr 813, -1080), (Sum.inr 853, -1080), (Sum.inr 1098, -2160), (Sum.inr 1103, -1080), (Sum.inr 1239, -1080), (Sum.inr 1778, -2160), (Sum.inr 1783, -1080), (Sum.inr 1854, -2160), (Sum.inr 1857, -1080), (Sum.inr 1858, -1080), (Sum.inr 1867, -2160), (Sum.inr 1873, -2160), (Sum.inr 1891, -2160), (Sum.inr 1893, -2160), (Sum.inr 1894, -2160), (Sum.inr 1915, -2160), (Sum.inr 1946, -2160), (Sum.inr 2025, -2160), (Sum.inr 2058, -2160), (Sum.inr 2065, -1080), (Sum.inr 2216, -2160), (Sum.inr 2218, -1080), (Sum.inr 2224, -2160), (Sum.inr 2226, -1080), (Sum.inr 2247, -1080), (Sum.inr 2266, -1080), (Sum.inr 2278, -1080), (Sum.inr 2290, -1080), (Sum.inr 2881, -2160), (Sum.inr 2889, -1080), (Sum.inr 3624, -2160), (Sum.inr 3631, -1080), (Sum.inr 3632, -1080), (Sum.inr 3907, -1080)]

theorem reindexCheck1686 : Integer.Sparse.reindex keyMap MixedData.row1686 = numericRow1686 := by decide +kernel

theorem numericCheck1686 (x : Master → ℝ) : Integer.Sparse.eval numericRow1686 x =
    (4320 : ℝ) * reducedSource1686 x := by
  norm_num [numericRow1686, reducedSource1686, Integer.Sparse.eval, Sparse.eval, nodeValue4219, nodeValue4225, nodeValue4229, nodeValue4270, nodeValue4514, nodeValue4519, nodeValue4605, nodeValue4650, nodeValue4657, nodeValue4713, nodeValue4719, nodeValue4742, nodeValue4807, nodeValue4839, nodeValue4845, nodeValue4890, nodeValue4896, nodeValue5204, nodeValue5207, nodeValue5294, nodeValue5443]; ring

noncomputable def reducedSource1687 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4371 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4761 x + ((2 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4817 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + 0))))))))))))))))))))

def numericRow1687 : Integer.Sparse Master := [(Sum.inr 939, -1), (Sum.inr 1091, -1), (Sum.inr 1694, -1), (Sum.inr 1756, -1), (Sum.inr 1819, -1), (Sum.inr 1970, -2), (Sum.inr 2054, -2), (Sum.inr 2062, -2), (Sum.inr 2169, -1), (Sum.inr 2186, -2), (Sum.inr 2206, -2), (Sum.inr 2230, -2), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 2743, -1), (Sum.inr 3548, -1), (Sum.inr 4347, 8), (Sum.inr 4358, 4), (Sum.inr 4371, 8), (Sum.inr 4375, 4), (Sum.inr 4478, 4), (Sum.inr 4682, 8), (Sum.inr 4761, 8), (Sum.inr 4817, 8), (Sum.inr 5205, 8), (Sum.inr 5206, 4), (Sum.inr 5276, 4)]

theorem reindexCheck1687 : Integer.Sparse.reindex keyMap MixedData.row1687 = numericRow1687 := by decide +kernel

theorem numericCheck1687 (x : Master → ℝ) : Integer.Sparse.eval numericRow1687 x =
    (4 : ℝ) * reducedSource1687 x := by
  norm_num [numericRow1687, reducedSource1687, Integer.Sparse.eval, Sparse.eval, nodeValue4347, nodeValue4358, nodeValue4361, nodeValue4371, nodeValue4375, nodeValue4478, nodeValue4507, nodeValue4682, nodeValue4693, nodeValue4761, nodeValue4770, nodeValue4817, nodeValue4835, nodeValue4843, nodeValue4846, nodeValue4899, nodeValue4901, nodeValue5205, nodeValue5206, nodeValue5275, nodeValue5276]; ring

noncomputable def reducedSource1688 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1742 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((2 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue2175 x + ((2 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + 0))))))))))))))))))))

def numericRow1688 : Integer.Sparse Master := [(Sum.inr 1676, 2), (Sum.inr 1694, 1), (Sum.inr 1695, 1), (Sum.inr 1742, 2), (Sum.inr 1743, 1), (Sum.inr 1746, 1), (Sum.inr 1756, 1), (Sum.inr 2153, 2), (Sum.inr 2169, 1), (Sum.inr 2175, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2230, 2), (Sum.inr 2294, 1), (Sum.inr 2687, 1), (Sum.inr 2706, 2), (Sum.inr 2743, 1), (Sum.inr 2744, 1)]

theorem reindexCheck1688 : Integer.Sparse.reindex keyMap MixedData.row1688 = numericRow1688 := by decide +kernel

theorem numericCheck1688 (x : Master → ℝ) : Integer.Sparse.eval numericRow1688 x =
    (1 : ℝ) * reducedSource1688 x := by
  norm_num [numericRow1688, reducedSource1688, Integer.Sparse.eval, Sparse.eval, nodeValue1676, nodeValue1694, nodeValue1695, nodeValue1742, nodeValue1743, nodeValue1746, nodeValue1756, nodeValue2153, nodeValue2169, nodeValue2175, nodeValue2186, nodeValue2206, nodeValue2207, nodeValue2229, nodeValue2230, nodeValue2293, nodeValue2294, nodeValue2687, nodeValue2706, nodeValue2743, nodeValue2744]

noncomputable def reducedSource1689 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1970 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1689 : Integer.Sparse Master := [(Sum.inr 939, 1), (Sum.inr 1819, 1), (Sum.inr 1970, 2), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1689 : Integer.Sparse.reindex keyMap MixedData.row1689 = numericRow1689 := by decide +kernel

theorem numericCheck1689 (x : Master → ℝ) : Integer.Sparse.eval numericRow1689 x =
    (1 : ℝ) * reducedSource1689 x := by
  norm_num [numericRow1689, reducedSource1689, Integer.Sparse.eval, Sparse.eval, nodeValue939, nodeValue1819, nodeValue1970, nodeValue2062, nodeValue2066, nodeValue4084]

noncomputable def reducedSource1690 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1315 x + ((1 : ℝ) * Sparse.eval nodeValue1961 x + ((1 : ℝ) * Sparse.eval nodeValue1970 x + ((2 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1690 : Integer.Sparse Master := [(Sum.inr 1315, 1), (Sum.inr 1961, 1), (Sum.inr 1970, 1), (Sum.inr 2062, 2), (Sum.inr 2879, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1690 : Integer.Sparse.reindex keyMap MixedData.row1690 = numericRow1690 := by decide +kernel

theorem numericCheck1690 (x : Master → ℝ) : Integer.Sparse.eval numericRow1690 x =
    (1 : ℝ) * reducedSource1690 x := by
  norm_num [numericRow1690, reducedSource1690, Integer.Sparse.eval, Sparse.eval, nodeValue1315, nodeValue1961, nodeValue1970, nodeValue2062, nodeValue2879, nodeValue4084]

noncomputable def reducedSource1691 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1691 : Integer.Sparse Master := [(Sum.inr 2128, 2), (Sum.inr 2130, 1), (Sum.inr 2137, 1), (Sum.inr 2276, 1), (Sum.inr 2687, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1691 : Integer.Sparse.reindex keyMap MixedData.row1691 = numericRow1691 := by decide +kernel

theorem numericCheck1691 (x : Master → ℝ) : Integer.Sparse.eval numericRow1691 x =
    (1 : ℝ) * reducedSource1691 x := by
  norm_num [numericRow1691, reducedSource1691, Integer.Sparse.eval, Sparse.eval, nodeValue2128, nodeValue2130, nodeValue2137, nodeValue2276, nodeValue2687, nodeValue4082]

noncomputable def reducedSource1692 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1692 : Integer.Sparse Master := [(Sum.inr 2085, 1), (Sum.inr 2087, 1), (Sum.inr 2093, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1692 : Integer.Sparse.reindex keyMap MixedData.row1692 = numericRow1692 := by decide +kernel

theorem numericCheck1692 (x : Master → ℝ) : Integer.Sparse.eval numericRow1692 x =
    (1 : ℝ) * reducedSource1692 x := by
  norm_num [numericRow1692, reducedSource1692, Integer.Sparse.eval, Sparse.eval, nodeValue2085, nodeValue2087, nodeValue2093, nodeValue2101, nodeValue2242, nodeValue3570, nodeValue4080]

noncomputable def reducedSource1693 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1693 : Integer.Sparse Master := [(Sum.inr 2492, 1), (Sum.inr 2606, 1), (Sum.inr 2608, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1693 : Integer.Sparse.reindex keyMap MixedData.row1693 = numericRow1693 := by decide +kernel

theorem numericCheck1693 (x : Master → ℝ) : Integer.Sparse.eval numericRow1693 x =
    (1 : ℝ) * reducedSource1693 x := by
  norm_num [numericRow1693, reducedSource1693, Integer.Sparse.eval, Sparse.eval, nodeValue2492, nodeValue2606, nodeValue2608, nodeValue2629, nodeValue2672, nodeValue3811, nodeValue4088]

noncomputable def reducedSource1694 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1694 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2032, 1), (Sum.inr 2038, 1), (Sum.inr 2048, 1), (Sum.inr 2276, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1694 : Integer.Sparse.reindex keyMap MixedData.row1694 = numericRow1694 := by decide +kernel

theorem numericCheck1694 (x : Master → ℝ) : Integer.Sparse.eval numericRow1694 x =
    (1 : ℝ) * reducedSource1694 x := by
  norm_num [numericRow1694, reducedSource1694, Integer.Sparse.eval, Sparse.eval, nodeValue2030, nodeValue2032, nodeValue2038, nodeValue2048, nodeValue2276, nodeValue3538, nodeValue4082]

noncomputable def reducedSource1695 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1695 : Integer.Sparse Master := [(Sum.inr 2469, 1), (Sum.inr 2609, 1), (Sum.inr 2613, 2), (Sum.inr 2694, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1695 : Integer.Sparse.reindex keyMap MixedData.row1695 = numericRow1695 := by decide +kernel

theorem numericCheck1695 (x : Master → ℝ) : Integer.Sparse.eval numericRow1695 x =
    (1 : ℝ) * reducedSource1695 x := by
  norm_num [numericRow1695, reducedSource1695, Integer.Sparse.eval, Sparse.eval, nodeValue2469, nodeValue2609, nodeValue2613, nodeValue2694, nodeValue3799, nodeValue4090]

end MUB6.Certificate.MixedSourceBridge

end OAI
