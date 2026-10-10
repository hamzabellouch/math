import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1728 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2377 x + ((1 : ℝ) * Sparse.eval nodeValue2541 x + ((2 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1728 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 2551, 2), (Sum.inr 2705, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1728 : Integer.Sparse.reindex keyMap MixedData.row1728 = numericRow1728 := by decide +kernel

theorem numericCheck1728 (x : Master → ℝ) : Integer.Sparse.eval numericRow1728 x =
    (1 : ℝ) * reducedSource1728 x := by
  norm_num [numericRow1728, reducedSource1728, Integer.Sparse.eval, Sparse.eval, nodeValue2377, nodeValue2541, nodeValue2551, nodeValue2705, nodeValue3757, nodeValue4088]

noncomputable def reducedSource1729 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1897 x + ((1 : ℝ) * Sparse.eval nodeValue2540 x + ((2 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1729 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2550, 2), (Sum.inr 2704, 1), (Sum.inr 3459, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1729 : Integer.Sparse.reindex keyMap MixedData.row1729 = numericRow1729 := by decide +kernel

theorem numericCheck1729 (x : Master → ℝ) : Integer.Sparse.eval numericRow1729 x =
    (1 : ℝ) * reducedSource1729 x := by
  norm_num [numericRow1729, reducedSource1729, Integer.Sparse.eval, Sparse.eval, nodeValue1897, nodeValue2540, nodeValue2550, nodeValue2704, nodeValue3459, nodeValue4080]

noncomputable def reducedSource1730 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1730 : Integer.Sparse Master := [(Sum.inr 2075, 1), (Sum.inr 2079, 1), (Sum.inr 2082, 1), (Sum.inr 2101, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1730 : Integer.Sparse.reindex keyMap MixedData.row1730 = numericRow1730 := by decide +kernel

theorem numericCheck1730 (x : Master → ℝ) : Integer.Sparse.eval numericRow1730 x =
    (1 : ℝ) * reducedSource1730 x := by
  norm_num [numericRow1730, reducedSource1730, Integer.Sparse.eval, Sparse.eval, nodeValue2075, nodeValue2079, nodeValue2082, nodeValue2101, nodeValue2205, nodeValue3564, nodeValue4080]

noncomputable def reducedSource1731 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1875 x + ((1 : ℝ) * Sparse.eval nodeValue1880 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2504 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1731 : Integer.Sparse Master := [(Sum.inr 1123, 1), (Sum.inr 1875, 1), (Sum.inr 1880, 1), (Sum.inr 2079, 1), (Sum.inr 2504, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1731 : Integer.Sparse.reindex keyMap MixedData.row1731 = numericRow1731 := by decide +kernel

theorem numericCheck1731 (x : Master → ℝ) : Integer.Sparse.eval numericRow1731 x =
    (1 : ℝ) * reducedSource1731 x := by
  norm_num [numericRow1731, reducedSource1731, Integer.Sparse.eval, Sparse.eval, nodeValue1123, nodeValue1875, nodeValue1880, nodeValue1914, nodeValue2079, nodeValue2504, nodeValue4080]

noncomputable def reducedSource1732 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1799 x + ((1 : ℝ) * Sparse.eval nodeValue1874 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2047 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1732 : Integer.Sparse Master := [(Sum.inr 916, 1), (Sum.inr 1799, 1), (Sum.inr 1874, 1), (Sum.inr 2018, 1), (Sum.inr 2047, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1732 : Integer.Sparse.reindex keyMap MixedData.row1732 = numericRow1732 := by decide +kernel

theorem numericCheck1732 (x : Master → ℝ) : Integer.Sparse.eval numericRow1732 x =
    (1 : ℝ) * reducedSource1732 x := by
  norm_num [numericRow1732, reducedSource1732, Integer.Sparse.eval, Sparse.eval, nodeValue916, nodeValue1799, nodeValue1874, nodeValue1911, nodeValue2018, nodeValue2047, nodeValue4081]

noncomputable def reducedSource1733 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2461 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

def numericRow1733 : Integer.Sparse Master := [(Sum.inr 2449, 1), (Sum.inr 2452, 1), (Sum.inr 2477, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1733 : Integer.Sparse.reindex keyMap MixedData.row1733 = numericRow1733 := by decide +kernel

theorem numericCheck1733 (x : Master → ℝ) : Integer.Sparse.eval numericRow1733 x =
    (1 : ℝ) * reducedSource1733 x := by
  norm_num [numericRow1733, reducedSource1733, Integer.Sparse.eval, Sparse.eval, nodeValue2449, nodeValue2452, nodeValue2461, nodeValue2477, nodeValue2694, nodeValue3793, nodeValue4090]

noncomputable def reducedSource1734 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4760 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))

def numericRow1734 : Integer.Sparse Master := [(Sum.inr 924, -2), (Sum.inr 934, -1), (Sum.inr 938, -1), (Sum.inr 1128, -2), (Sum.inr 1143, -1), (Sum.inr 1239, -1), (Sum.inr 1674, -2), (Sum.inr 1692, -1), (Sum.inr 1693, -1), (Sum.inr 1807, -2), (Sum.inr 1818, -1), (Sum.inr 1960, -2), (Sum.inr 1969, -2), (Sum.inr 2022, -2), (Sum.inr 2151, -2), (Sum.inr 2167, -1), (Sum.inr 2168, -1), (Sum.inr 2173, -2), (Sum.inr 2184, -2), (Sum.inr 2185, -2), (Sum.inr 2203, -2), (Sum.inr 2226, -1), (Sum.inr 2509, -2), (Sum.inr 2522, -1), (Sum.inr 2685, -1), (Sum.inr 2704, -2), (Sum.inr 2740, -2), (Sum.inr 4084, 4)]

theorem reindexCheck1734 : Integer.Sparse.reindex keyMap MixedData.row1734 = numericRow1734 := by decide +kernel

theorem numericCheck1734 (x : Master → ℝ) : Integer.Sparse.eval numericRow1734 x =
    (4 : ℝ) * reducedSource1734 x := by
  norm_num [numericRow1734, reducedSource1734, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4346, nodeValue4356, nodeValue4360, nodeValue4505, nodeValue4543, nodeValue4557, nodeValue4605, nodeValue4681, nodeValue4692, nodeValue4760, nodeValue4769, nodeValue4804, nodeValue4834, nodeValue4841, nodeValue4846, nodeValue4897, nodeValue5099, nodeValue5110, nodeValue5272, nodeValue5274]; ring

noncomputable def reducedSource1735 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1674 x + ((1 : ℝ) * Sparse.eval nodeValue1692 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((2 : ℝ) * Sparse.eval nodeValue2173 x + ((2 : ℝ) * Sparse.eval nodeValue2184 x + ((2 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((2 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))))))))))

def numericRow1735 : Integer.Sparse Master := [(Sum.inr 1674, 2), (Sum.inr 1692, 1), (Sum.inr 1693, 1), (Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2173, 2), (Sum.inr 2184, 2), (Sum.inr 2185, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 1), (Sum.inr 2685, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 4084, 1)]

theorem reindexCheck1735 : Integer.Sparse.reindex keyMap MixedData.row1735 = numericRow1735 := by decide +kernel

theorem numericCheck1735 (x : Master → ℝ) : Integer.Sparse.eval numericRow1735 x =
    (1 : ℝ) * reducedSource1735 x := by
  norm_num [numericRow1735, reducedSource1735, Integer.Sparse.eval, Sparse.eval, nodeValue1674, nodeValue1692, nodeValue1693, nodeValue1754, nodeValue2151, nodeValue2167, nodeValue2168, nodeValue2173, nodeValue2184, nodeValue2185, nodeValue2203, nodeValue2205, nodeValue2226, nodeValue2228, nodeValue2229, nodeValue2292, nodeValue2685, nodeValue2704, nodeValue2740, nodeValue2742, nodeValue4084]

noncomputable def reducedSource1736 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2403 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1736 : Integer.Sparse Master := [(Sum.inr 2382, 1), (Sum.inr 2385, 1), (Sum.inr 2388, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1736 : Integer.Sparse.reindex keyMap MixedData.row1736 = numericRow1736 := by decide +kernel

theorem numericCheck1736 (x : Master → ℝ) : Integer.Sparse.eval numericRow1736 x =
    (1 : ℝ) * reducedSource1736 x := by
  norm_num [numericRow1736, reducedSource1736, Integer.Sparse.eval, Sparse.eval, nodeValue2382, nodeValue2385, nodeValue2388, nodeValue2403, nodeValue2672, nodeValue3766, nodeValue4088]

noncomputable def reducedSource1737 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2468 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1737 : Integer.Sparse Master := [(Sum.inr 2385, 1), (Sum.inr 2459, 1), (Sum.inr 2505, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1737 : Integer.Sparse.reindex keyMap MixedData.row1737 = numericRow1737 := by decide +kernel

theorem numericCheck1737 (x : Master → ℝ) : Integer.Sparse.eval numericRow1737 x =
    (1 : ℝ) * reducedSource1737 x := by
  norm_num [numericRow1737, reducedSource1737, Integer.Sparse.eval, Sparse.eval, nodeValue2385, nodeValue2459, nodeValue2468, nodeValue2505, nodeValue2705, nodeValue3766, nodeValue4088]

noncomputable def reducedSource1738 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4293 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4308 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4525 x + ((1 : ℝ) * Sparse.eval nodeValue4538 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4649 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4712 x + ((1 : ℝ) * Sparse.eval nodeValue4721 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4736 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5055 x + ((1 : ℝ) * Sparse.eval nodeValue5094 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + 0)))))))))))))))))))))))))))))

def numericRow1738 : Integer.Sparse Master := [(Sum.inr 865, -1), (Sum.inr 871, -1), (Sum.inr 873, -1), (Sum.inr 982, -1), (Sum.inr 1105, -1), (Sum.inr 1109, -1), (Sum.inr 1123, -1), (Sum.inr 1202, -1), (Sum.inr 1553, -1), (Sum.inr 1568, -1), (Sum.inr 1569, -1), (Sum.inr 1617, -1), (Sum.inr 1760, -1), (Sum.inr 1766, -1), (Sum.inr 1836, -1), (Sum.inr 1849, -1), (Sum.inr 1850, -1), (Sum.inr 1860, -1), (Sum.inr 1875, -1), (Sum.inr 1880, -1), (Sum.inr 1887, -1), (Sum.inr 1888, -1), (Sum.inr 1897, -1), (Sum.inr 1905, -1), (Sum.inr 1907, -1), (Sum.inr 1937, -1), (Sum.inr 1938, -1), (Sum.inr 1942, -1), (Sum.inr 1987, -1), (Sum.inr 1996, -1), (Sum.inr 2047, -1), (Sum.inr 2052, -1), (Sum.inr 2079, -1), (Sum.inr 2193, -1), (Sum.inr 2399, -1), (Sum.inr 2458, -2), (Sum.inr 2467, -1), (Sum.inr 2504, -2), (Sum.inr 2509, -1), (Sum.inr 2704, -1), (Sum.inr 4080, 4)]

theorem reindexCheck1738 : Integer.Sparse.reindex keyMap MixedData.row1738 = numericRow1738 := by decide +kernel

theorem numericCheck1738 (x : Master → ℝ) : Integer.Sparse.eval numericRow1738 x =
    (4 : ℝ) * reducedSource1738 x := by
  norm_num [numericRow1738, reducedSource1738, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4287, nodeValue4293, nodeValue4295, nodeValue4308, nodeValue4401, nodeValue4521, nodeValue4525, nodeValue4538, nodeValue4583, nodeValue4631, nodeValue4637, nodeValue4649, nodeValue4706, nodeValue4712, nodeValue4721, nodeValue4726, nodeValue4728, nodeValue4736, nodeValue4741, nodeValue4745, nodeValue4779, nodeValue4827, nodeValue4832, nodeValue4834, nodeValue5014, nodeValue5055, nodeValue5094, nodeValue5099, nodeValue5101]; ring

noncomputable def reducedSource1739 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4304 x + ((1 : ℝ) * Sparse.eval nodeValue4317 x + ((1 : ℝ) * Sparse.eval nodeValue4319 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4643 x + ((2 : ℝ) * Sparse.eval nodeValue4645 x + ((1 : ℝ) * Sparse.eval nodeValue4655 x + ((1 : ℝ) * Sparse.eval nodeValue4657 x + ((2 : ℝ) * Sparse.eval nodeValue4710 x + ((2 : ℝ) * Sparse.eval nodeValue4719 x + ((2 : ℝ) * Sparse.eval nodeValue4741 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4754 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + 0))))))))))))))))))))

def numericRow1739 : Integer.Sparse Master := [(Sum.inr 882, -2), (Sum.inr 897, -1), (Sum.inr 1012, -1), (Sum.inr 1558, -2), (Sum.inr 1577, -1), (Sum.inr 1627, -1), (Sum.inr 1774, -2), (Sum.inr 1783, -1), (Sum.inr 1840, -2), (Sum.inr 1857, -1), (Sum.inr 1864, -2), (Sum.inr 1873, -2), (Sum.inr 1882, -2), (Sum.inr 1893, -2), (Sum.inr 1915, -2), (Sum.inr 1946, -2), (Sum.inr 1951, -2), (Sum.inr 2003, -2), (Sum.inr 2006, -2), (Sum.inr 2062, -1), (Sum.inr 2230, -1), (Sum.inr 2385, -2), (Sum.inr 2407, -1), (Sum.inr 2519, -1), (Sum.inr 3353, -2), (Sum.inr 3360, -1), (Sum.inr 3486, -1), (Sum.inr 4081, 4)]

theorem reindexCheck1739 : Integer.Sparse.reindex keyMap MixedData.row1739 = numericRow1739 := by decide +kernel

theorem numericCheck1739 (x : Master → ℝ) : Integer.Sparse.eval numericRow1739 x =
    (4 : ℝ) * reducedSource1739 x := by
  norm_num [numericRow1739, reducedSource1739, Integer.Sparse.eval, Sparse.eval, nodeValue4081, nodeValue4304, nodeValue4317, nodeValue4319, nodeValue4431, nodeValue4643, nodeValue4645, nodeValue4655, nodeValue4657, nodeValue4710, nodeValue4719, nodeValue4741, nodeValue4742, nodeValue4754, nodeValue4788, nodeValue4841, nodeValue4843, nodeValue5000, nodeValue5021, nodeValue5107, nodeValue5109]; ring

noncomputable def reducedSource1740 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((4 : ℝ) * Sparse.eval nodeValue4343 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((2 : ℝ) * Sparse.eval nodeValue4359 x + ((2 : ℝ) * Sparse.eval nodeValue4501 x + ((4 : ℝ) * Sparse.eval nodeValue4678 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((2 : ℝ) * Sparse.eval nodeValue4759 x + ((4 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + 0))))))))))))

def numericRow1740 : Integer.Sparse Master := [(Sum.inr 921, -4), (Sum.inr 928, -1), (Sum.inr 937, -2), (Sum.inr 1666, -4), (Sum.inr 1677, -1), (Sum.inr 1683, -2), (Sum.inr 1804, -4), (Sum.inr 1817, -1), (Sum.inr 1959, -2), (Sum.inr 2052, -4), (Sum.inr 2065, -2), (Sum.inr 2143, -4), (Sum.inr 2159, -1), (Sum.inr 2170, -2), (Sum.inr 2193, -4), (Sum.inr 2218, -2), (Sum.inr 2726, -1), (Sum.inr 3545, -1), (Sum.inr 4085, 4)]

theorem reindexCheck1740 : Integer.Sparse.reindex keyMap MixedData.row1740 = numericRow1740 := by decide +kernel

theorem numericCheck1740 (x : Master → ℝ) : Integer.Sparse.eval numericRow1740 x =
    (4 : ℝ) * reducedSource1740 x := by
  norm_num [numericRow1740, reducedSource1740, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4343, nodeValue4350, nodeValue4359, nodeValue4501, nodeValue4678, nodeValue4691, nodeValue4759, nodeValue4832, nodeValue4837, nodeValue4845, nodeValue4897, nodeValue5261]; ring

noncomputable def reducedSource1741 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1666 x + ((1 : ℝ) * Sparse.eval nodeValue1677 x + ((2 : ℝ) * Sparse.eval nodeValue1683 x + ((2 : ℝ) * Sparse.eval nodeValue1730 x + ((4 : ℝ) * Sparse.eval nodeValue2143 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((2 : ℝ) * Sparse.eval nodeValue2170 x + ((4 : ℝ) * Sparse.eval nodeValue2193 x + ((4 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

def numericRow1741 : Integer.Sparse Master := [(Sum.inr 1666, 4), (Sum.inr 1677, 1), (Sum.inr 1683, 2), (Sum.inr 2143, 4), (Sum.inr 2159, 1), (Sum.inr 2170, 2), (Sum.inr 2193, 4), (Sum.inr 2218, 2), (Sum.inr 2726, 1), (Sum.inr 4085, 1)]

theorem reindexCheck1741 : Integer.Sparse.reindex keyMap MixedData.row1741 = numericRow1741 := by decide +kernel

theorem numericCheck1741 (x : Master → ℝ) : Integer.Sparse.eval numericRow1741 x =
    (1 : ℝ) * reducedSource1741 x := by
  norm_num [numericRow1741, reducedSource1741, Integer.Sparse.eval, Sparse.eval, nodeValue1666, nodeValue1677, nodeValue1683, nodeValue1730, nodeValue2143, nodeValue2159, nodeValue2170, nodeValue2193, nodeValue2208, nodeValue2218, nodeValue2268, nodeValue2726, nodeValue4085]

noncomputable def reducedSource1742 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue937 x + ((2 : ℝ) * Sparse.eval nodeValue1804 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow1742 : Integer.Sparse Master := [(Sum.inr 937, 1), (Sum.inr 1804, 2), (Sum.inr 1817, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1742 : Integer.Sparse.reindex keyMap MixedData.row1742 = numericRow1742 := by decide +kernel

theorem numericCheck1742 (x : Master → ℝ) : Integer.Sparse.eval numericRow1742 x =
    (1 : ℝ) * reducedSource1742 x := by
  norm_num [numericRow1742, reducedSource1742, Integer.Sparse.eval, Sparse.eval, nodeValue937, nodeValue1804, nodeValue1817, nodeValue2056, nodeValue2065, nodeValue4085]

noncomputable def reducedSource1743 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((1 : ℝ) * Sparse.eval nodeValue4286 x + ((1 : ℝ) * Sparse.eval nodeValue4289 x + ((1 : ℝ) * Sparse.eval nodeValue4294 x + ((1 : ℝ) * Sparse.eval nodeValue4302 x + ((1 : ℝ) * Sparse.eval nodeValue4320 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4426 x + ((1 : ℝ) * Sparse.eval nodeValue4630 x + ((1 : ℝ) * Sparse.eval nodeValue4636 x + ((1 : ℝ) * Sparse.eval nodeValue4643 x + ((1 : ℝ) * Sparse.eval nodeValue4658 x + ((1 : ℝ) * Sparse.eval nodeValue4673 x + ((1 : ℝ) * Sparse.eval nodeValue4708 x + ((1 : ℝ) * Sparse.eval nodeValue4720 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4738 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((1 : ℝ) * Sparse.eval nodeValue4778 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + 0)))))))))))))))))))))))))))))

def numericRow1743 : Integer.Sparse Master := [(Sum.inr 864, -1), (Sum.inr 867, -1), (Sum.inr 872, -1), (Sum.inr 898, -1), (Sum.inr 902, -1), (Sum.inr 916, -1), (Sum.inr 979, -1), (Sum.inr 1550, -1), (Sum.inr 1555, -1), (Sum.inr 1562, -1), (Sum.inr 1586, -1), (Sum.inr 1590, -1), (Sum.inr 1599, -1), (Sum.inr 1633, -1), (Sum.inr 1759, -1), (Sum.inr 1765, -1), (Sum.inr 1784, -1), (Sum.inr 1799, -1), (Sum.inr 1833, -1), (Sum.inr 1843, -1), (Sum.inr 1874, -1), (Sum.inr 1884, -1), (Sum.inr 1896, -1), (Sum.inr 1897, -1), (Sum.inr 1907, -1), (Sum.inr 1917, -1), (Sum.inr 1920, -1), (Sum.inr 1924, -1), (Sum.inr 1986, -2), (Sum.inr 1987, -1), (Sum.inr 1996, -1), (Sum.inr 2003, -1), (Sum.inr 2006, -1), (Sum.inr 2018, -2), (Sum.inr 2022, -1), (Sum.inr 2047, -1), (Sum.inr 2079, -1), (Sum.inr 2203, -1), (Sum.inr 2482, -1), (Sum.inr 3468, -1), (Sum.inr 4081, 4)]

theorem reindexCheck1743 : Integer.Sparse.reindex keyMap MixedData.row1743 = numericRow1743 := by decide +kernel

theorem numericCheck1743 (x : Master → ℝ) : Integer.Sparse.eval numericRow1743 x =
    (4 : ℝ) * reducedSource1743 x := by
  norm_num [numericRow1743, reducedSource1743, Integer.Sparse.eval, Sparse.eval, nodeValue4081, nodeValue4286, nodeValue4289, nodeValue4294, nodeValue4302, nodeValue4320, nodeValue4324, nodeValue4338, nodeValue4398, nodeValue4426, nodeValue4630, nodeValue4636, nodeValue4643, nodeValue4658, nodeValue4673, nodeValue4708, nodeValue4720, nodeValue4728, nodeValue4738, nodeValue4741, nodeValue4744, nodeValue4778, nodeValue4779, nodeValue4788, nodeValue4800, nodeValue4804, nodeValue4827, nodeValue4837, nodeValue4841, nodeValue5075]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
