import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1872 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4415 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4427 x + ((1 : ℝ) * Sparse.eval nodeValue4487 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((2 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4750 x + ((2 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4785 x + ((2 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4825 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + 0))))))))))))))))))))

def numericRow1872 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 1000, -1080), (Sum.inr 1605, -1080), (Sum.inr 1901, -540), (Sum.inr 1929, -540), (Sum.inr 1941, -540), (Sum.inr 1949, -540), (Sum.inr 1990, -1080), (Sum.inr 1997, -1080), (Sum.inr 2028, -1080), (Sum.inr 2029, -540), (Sum.inr 2116, -540), (Sum.inr 2215, -1080), (Sum.inr 2225, -540), (Sum.inr 2288, -540), (Sum.inr 2489, -540), (Sum.inr 2931, -1080), (Sum.inr 3482, -540), (Sum.inr 3612, -1080), (Sum.inr 3616, -540), (Sum.inr 4427, 2160), (Sum.inr 4487, 2160), (Sum.inr 4785, 2160), (Sum.inr 4795, 4320), (Sum.inr 4821, 4320), (Sum.inr 4825, 2160), (Sum.inr 4856, 4320)]

theorem reindexCheck1872 : Integer.Sparse.reindex keyMap MixedData.row1872 = numericRow1872 := by decide +kernel

theorem numericCheck1872 (x : Master → ℝ) : Integer.Sparse.eval numericRow1872 x =
    (2160 : ℝ) * reducedSource1872 x := by
  norm_num [numericRow1872, reducedSource1872, Integer.Sparse.eval, Sparse.eval, nodeValue4415, nodeValue4419, nodeValue4427, nodeValue4487, nodeValue4732, nodeValue4745, nodeValue4750, nodeValue4782, nodeValue4785, nodeValue4795, nodeValue4810, nodeValue4811, nodeValue4821, nodeValue4825, nodeValue4846, nodeValue4856, nodeValue4875, nodeValue5081, nodeValue5130, nodeValue5152, nodeValue5177]; ring

noncomputable def reducedSource1873 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4362 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((1 : ℝ) * Sparse.eval nodeValue4694 x + ((2 : ℝ) * Sparse.eval nodeValue4702 x + ((2 : ℝ) * Sparse.eval nodeValue4762 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + 0))))))))))))))))))))

def numericRow1873 : Integer.Sparse Master := [(Sum.inr 937, -1), (Sum.inr 1094, -1), (Sum.inr 1683, -1), (Sum.inr 1741, -1), (Sum.inr 1804, -2), (Sum.inr 1817, -1), (Sum.inr 2052, -2), (Sum.inr 2065, -2), (Sum.inr 2143, -2), (Sum.inr 2159, -1), (Sum.inr 2193, -2), (Sum.inr 2218, -2), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 2726, -1), (Sum.inr 3545, -1), (Sum.inr 4348, 8), (Sum.inr 4362, 4), (Sum.inr 4683, 8), (Sum.inr 4694, 4), (Sum.inr 4702, 8), (Sum.inr 4762, 8), (Sum.inr 4836, 8), (Sum.inr 4844, 4), (Sum.inr 5222, 8), (Sum.inr 5235, 4), (Sum.inr 5268, 4)]

theorem reindexCheck1873 : Integer.Sparse.reindex keyMap MixedData.row1873 = numericRow1873 := by decide +kernel

theorem numericCheck1873 (x : Master → ℝ) : Integer.Sparse.eval numericRow1873 x =
    (4 : ℝ) * reducedSource1873 x := by
  norm_num [numericRow1873, reducedSource1873, Integer.Sparse.eval, Sparse.eval, nodeValue4348, nodeValue4359, nodeValue4362, nodeValue4510, nodeValue4678, nodeValue4683, nodeValue4691, nodeValue4694, nodeValue4702, nodeValue4762, nodeValue4832, nodeValue4836, nodeValue4837, nodeValue4844, nodeValue4845, nodeValue4897, nodeValue4899, nodeValue5222, nodeValue5235, nodeValue5261, nodeValue5268]; ring

noncomputable def reducedSource1874 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue1348 x + ((1 : ℝ) * Sparse.eval nodeValue1349 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((2 : ℝ) * Sparse.eval nodeValue1828 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((2 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3031 x + ((2 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((2 : ℝ) * Sparse.eval nodeValue3062 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((2 : ℝ) * Sparse.eval nodeValue3143 x + ((1 : ℝ) * Sparse.eval nodeValue3145 x + ((1 : ℝ) * Sparse.eval nodeValue3215 x + 0))))))))))))))))))))

def numericRow1874 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, -40), (Sum.inl 2, -550), (Sum.inl 35, -160), (Sum.inl 13, -160), (Sum.inl 1, -20), (Sum.inr 1347, 2880), (Sum.inr 1348, 1440), (Sum.inr 1828, 2880), (Sum.inr 1832, 1440), (Sum.inr 2136, 1440), (Sum.inr 2716, 2880), (Sum.inr 2734, 1440), (Sum.inr 3031, 2880), (Sum.inr 3033, 2880), (Sum.inr 3046, 1440), (Sum.inr 3062, 2880)]

theorem reindexCheck1874 : Integer.Sparse.reindex keyMap MixedData.row1874 = numericRow1874 := by decide +kernel

theorem numericCheck1874 (x : Master → ℝ) : Integer.Sparse.eval numericRow1874 x =
    (1440 : ℝ) * reducedSource1874 x := by
  norm_num [numericRow1874, reducedSource1874, Integer.Sparse.eval, Sparse.eval, nodeValue1347, nodeValue1348, nodeValue1349, nodeValue1454, nodeValue1828, nodeValue1832, nodeValue2136, nodeValue2716, nodeValue2734, nodeValue2778, nodeValue3031, nodeValue3033, nodeValue3046, nodeValue3062, nodeValue3082, nodeValue3090, nodeValue3095, nodeValue3114, nodeValue3143, nodeValue3145, nodeValue3215]; ring

noncomputable def reducedSource1875 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1683 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((2 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((1 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2171 x + ((2 : ℝ) * Sparse.eval nodeValue2180 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + 0))))))))))))))))))))

def numericRow1875 : Integer.Sparse Master := [(Sum.inr 1669, 2), (Sum.inr 1683, 1), (Sum.inr 1687, 1), (Sum.inr 1741, 1), (Sum.inr 2143, 2), (Sum.inr 2146, 2), (Sum.inr 2159, 1), (Sum.inr 2163, 1), (Sum.inr 2171, 2), (Sum.inr 2180, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 2), (Sum.inr 2218, 2), (Sum.inr 2222, 1), (Sum.inr 2281, 1), (Sum.inr 2664, 2), (Sum.inr 2680, 1), (Sum.inr 2726, 1), (Sum.inr 2734, 1)]

theorem reindexCheck1875 : Integer.Sparse.reindex keyMap MixedData.row1875 = numericRow1875 := by decide +kernel

theorem numericCheck1875 (x : Master → ℝ) : Integer.Sparse.eval numericRow1875 x =
    (1 : ℝ) * reducedSource1875 x := by
  norm_num [numericRow1875, reducedSource1875, Integer.Sparse.eval, Sparse.eval, nodeValue1669, nodeValue1683, nodeValue1687, nodeValue1741, nodeValue2143, nodeValue2146, nodeValue2159, nodeValue2163, nodeValue2171, nodeValue2180, nodeValue2193, nodeValue2197, nodeValue2208, nodeValue2218, nodeValue2222, nodeValue2268, nodeValue2281, nodeValue2664, nodeValue2680, nodeValue2726, nodeValue2734]

noncomputable def reducedSource1876 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1809 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow1876 : Integer.Sparse Master := [(Sum.inr 1809, 2), (Sum.inr 1817, 1), (Sum.inr 1820, 1), (Sum.inr 2065, 1), (Sum.inr 3396, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1876 : Integer.Sparse.reindex keyMap MixedData.row1876 = numericRow1876 := by decide +kernel

theorem numericCheck1876 (x : Master → ℝ) : Integer.Sparse.eval numericRow1876 x =
    (1 : ℝ) * reducedSource1876 x := by
  norm_num [numericRow1876, reducedSource1876, Integer.Sparse.eval, Sparse.eval, nodeValue1809, nodeValue1817, nodeValue1820, nodeValue2065, nodeValue3396, nodeValue4085]

noncomputable def reducedSource1877 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4763 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + 0))))))))))))))))))))

def numericRow1877 : Integer.Sparse Master := [(Sum.inr 927, -2), (Sum.inr 938, -1), (Sum.inr 939, -1), (Sum.inr 1675, -2), (Sum.inr 1693, -1), (Sum.inr 1694, -1), (Sum.inr 1810, -2), (Sum.inr 1818, -1), (Sum.inr 1819, -1), (Sum.inr 1963, -2), (Sum.inr 1969, -2), (Sum.inr 1970, -2), (Sum.inr 2054, -2), (Sum.inr 2062, -1), (Sum.inr 2152, -2), (Sum.inr 2168, -1), (Sum.inr 2169, -1), (Sum.inr 2174, -2), (Sum.inr 2185, -2), (Sum.inr 2186, -2), (Sum.inr 2206, -2), (Sum.inr 2230, -1), (Sum.inr 2686, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -1), (Sum.inr 3397, -1), (Sum.inr 3498, -2), (Sum.inr 3548, -1), (Sum.inr 4084, 4)]

theorem reindexCheck1877 : Integer.Sparse.reindex keyMap MixedData.row1877 = numericRow1877 := by decide +kernel

theorem numericCheck1877 (x : Master → ℝ) : Integer.Sparse.eval numericRow1877 x =
    (4 : ℝ) * reducedSource1877 x := by
  norm_num [numericRow1877, reducedSource1877, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4349, nodeValue4360, nodeValue4361, nodeValue4511, nodeValue4684, nodeValue4692, nodeValue4693, nodeValue4763, nodeValue4769, nodeValue4770, nodeValue4834, nodeValue4835, nodeValue4841, nodeValue4843, nodeValue4846, nodeValue4901, nodeValue5238, nodeValue5248, nodeValue5274, nodeValue5275]; ring

noncomputable def reducedSource1878 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1675 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue2174 x + ((2 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((2 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))))))))))

def numericRow1878 : Integer.Sparse Master := [(Sum.inr 1675, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2174, 2), (Sum.inr 2185, 2), (Sum.inr 2186, 2), (Sum.inr 2206, 2), (Sum.inr 2230, 1), (Sum.inr 2686, 1), (Sum.inr 2705, 2), (Sum.inr 2743, 1), (Sum.inr 4084, 1)]

theorem reindexCheck1878 : Integer.Sparse.reindex keyMap MixedData.row1878 = numericRow1878 := by decide +kernel

theorem numericCheck1878 (x : Master → ℝ) : Integer.Sparse.eval numericRow1878 x =
    (1 : ℝ) * reducedSource1878 x := by
  norm_num [numericRow1878, reducedSource1878, Integer.Sparse.eval, Sparse.eval, nodeValue1675, nodeValue1693, nodeValue1694, nodeValue1755, nodeValue2152, nodeValue2168, nodeValue2169, nodeValue2174, nodeValue2185, nodeValue2186, nodeValue2205, nodeValue2206, nodeValue2228, nodeValue2229, nodeValue2230, nodeValue2293, nodeValue2686, nodeValue2705, nodeValue2742, nodeValue2743, nodeValue4084]

noncomputable def reducedSource1879 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1879 : Integer.Sparse Master := [(Sum.inr 1810, 2), (Sum.inr 1818, 1), (Sum.inr 1819, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1879 : Integer.Sparse.reindex keyMap MixedData.row1879 = numericRow1879 := by decide +kernel

theorem numericCheck1879 (x : Master → ℝ) : Integer.Sparse.eval numericRow1879 x =
    (1 : ℝ) * reducedSource1879 x := by
  norm_num [numericRow1879, reducedSource1879, Integer.Sparse.eval, Sparse.eval, nodeValue1810, nodeValue1818, nodeValue1819, nodeValue2066, nodeValue3397, nodeValue4084]

noncomputable def reducedSource1880 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4296 x + ((1 : ℝ) * Sparse.eval nodeValue4311 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4632 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4652 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4715 x + ((1 : ℝ) * Sparse.eval nodeValue4722 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4727 x + ((1 : ℝ) * Sparse.eval nodeValue4736 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4752 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + 0)))))))))))))))))))))))))))))

def numericRow1880 : Integer.Sparse Master := [(Sum.inr 866, -1), (Sum.inr 873, -1), (Sum.inr 874, -1), (Sum.inr 985, -1), (Sum.inr 1554, -1), (Sum.inr 1569, -1), (Sum.inr 1570, -1), (Sum.inr 1618, -1), (Sum.inr 1761, -1), (Sum.inr 1766, -1), (Sum.inr 1767, -1), (Sum.inr 1837, -1), (Sum.inr 1850, -1), (Sum.inr 1851, -1), (Sum.inr 1860, -1), (Sum.inr 1861, -1), (Sum.inr 1876, -1), (Sum.inr 1880, -1), (Sum.inr 1881, -1), (Sum.inr 1888, -1), (Sum.inr 1889, -1), (Sum.inr 1906, -1), (Sum.inr 1909, -2), (Sum.inr 1915, -1), (Sum.inr 1938, -1), (Sum.inr 1939, -1), (Sum.inr 1946, -1), (Sum.inr 1990, -1), (Sum.inr 1997, -1), (Sum.inr 2048, -1), (Sum.inr 2054, -1), (Sum.inr 2082, -1), (Sum.inr 2206, -1), (Sum.inr 2400, -1), (Sum.inr 2459, -1), (Sum.inr 2505, -1), (Sum.inr 2512, -1), (Sum.inr 3344, -1), (Sum.inr 3429, -1), (Sum.inr 3448, -1), (Sum.inr 3471, -1), (Sum.inr 4080, 4)]

theorem reindexCheck1880 : Integer.Sparse.reindex keyMap MixedData.row1880 = numericRow1880 := by decide +kernel

theorem numericCheck1880 (x : Master → ℝ) : Integer.Sparse.eval numericRow1880 x =
    (4 : ℝ) * reducedSource1880 x := by
  norm_num [numericRow1880, reducedSource1880, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4288, nodeValue4295, nodeValue4296, nodeValue4311, nodeValue4404, nodeValue4632, nodeValue4637, nodeValue4638, nodeValue4652, nodeValue4706, nodeValue4707, nodeValue4715, nodeValue4722, nodeValue4726, nodeValue4727, nodeValue4736, nodeValue4737, nodeValue4741, nodeValue4742, nodeValue4752, nodeValue4782, nodeValue4828, nodeValue4834, nodeValue4835, nodeValue5015, nodeValue5056, nodeValue5095, nodeValue5101, nodeValue5102]; ring

noncomputable def reducedSource1881 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4082 x + ((1 : ℝ) * Sparse.eval nodeValue4298 x + ((1 : ℝ) * Sparse.eval nodeValue4303 x + ((1 : ℝ) * Sparse.eval nodeValue4305 x + ((1 : ℝ) * Sparse.eval nodeValue4313 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4640 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4646 x + ((1 : ℝ) * Sparse.eval nodeValue4653 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4711 x + ((1 : ℝ) * Sparse.eval nodeValue4716 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4749 x + ((1 : ℝ) * Sparse.eval nodeValue4750 x + ((1 : ℝ) * Sparse.eval nodeValue4753 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + 0))))))))))))))))))))))))))))

def numericRow1881 : Integer.Sparse Master := [(Sum.inr 876, -1), (Sum.inr 881, -1), (Sum.inr 891, -1), (Sum.inr 1000, -1), (Sum.inr 1552, -1), (Sum.inr 1559, -1), (Sum.inr 1565, -1), (Sum.inr 1605, -1), (Sum.inr 1769, -1), (Sum.inr 1773, -1), (Sum.inr 1781, -1), (Sum.inr 1835, -1), (Sum.inr 1841, -1), (Sum.inr 1846, -1), (Sum.inr 1863, -1), (Sum.inr 1870, -1), (Sum.inr 1883, -1), (Sum.inr 1886, -1), (Sum.inr 1900, -1), (Sum.inr 1901, -1), (Sum.inr 1917, -1), (Sum.inr 1921, -1), (Sum.inr 1924, -1), (Sum.inr 1928, -2), (Sum.inr 1929, -1), (Sum.inr 1941, -1), (Sum.inr 1949, -1), (Sum.inr 1990, -1), (Sum.inr 1997, -1), (Sum.inr 2028, -1), (Sum.inr 2029, -1), (Sum.inr 2215, -1), (Sum.inr 2225, -1), (Sum.inr 2388, -1), (Sum.inr 2452, -1), (Sum.inr 2488, -1), (Sum.inr 2489, -1), (Sum.inr 3354, -1), (Sum.inr 3433, -1), (Sum.inr 3478, -1), (Sum.inr 3482, -1), (Sum.inr 4082, 4)]

theorem reindexCheck1881 : Integer.Sparse.reindex keyMap MixedData.row1881 = numericRow1881 := by decide +kernel

theorem numericCheck1881 (x : Master → ℝ) : Integer.Sparse.eval numericRow1881 x =
    (4 : ℝ) * reducedSource1881 x := by
  norm_num [numericRow1881, reducedSource1881, Integer.Sparse.eval, Sparse.eval, nodeValue4082, nodeValue4298, nodeValue4303, nodeValue4305, nodeValue4313, nodeValue4419, nodeValue4640, nodeValue4644, nodeValue4646, nodeValue4653, nodeValue4709, nodeValue4711, nodeValue4716, nodeValue4731, nodeValue4732, nodeValue4744, nodeValue4745, nodeValue4749, nodeValue4750, nodeValue4753, nodeValue4782, nodeValue4810, nodeValue4811, nodeValue4846, nodeValue5003, nodeValue5050, nodeValue5080, nodeValue5081, nodeValue5111]; ring

noncomputable def reducedSource1882 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4065 x + ((2 : ℝ) * Sparse.eval nodeValue4067 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((4 : ℝ) * Sparse.eval nodeValue4074 x + ((2 : ℝ) * Sparse.eval nodeValue4075 x + ((2 : ℝ) * Sparse.eval nodeValue4076 x + ((2 : ℝ) * Sparse.eval nodeValue4078 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))))))))))

def numericRow1882 : Integer.Sparse Master := [(Sum.inr 4065, 2), (Sum.inr 4067, 2), (Sum.inr 4071, 1), (Sum.inr 4074, 4), (Sum.inr 4075, 2), (Sum.inr 4076, 2), (Sum.inr 4078, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 2), (Sum.inr 4089, 1), (Sum.inr 4092, 2)]

theorem reindexCheck1882 : Integer.Sparse.reindex keyMap MixedData.row1882 = numericRow1882 := by decide +kernel

theorem numericCheck1882 (x : Master → ℝ) : Integer.Sparse.eval numericRow1882 x =
    (1 : ℝ) * reducedSource1882 x := by
  norm_num [numericRow1882, reducedSource1882, Integer.Sparse.eval, Sparse.eval, nodeValue4065, nodeValue4067, nodeValue4071, nodeValue4074, nodeValue4075, nodeValue4076, nodeValue4078, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4084, nodeValue4088, nodeValue4089, nodeValue4092]

noncomputable def reducedSource1883 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1806 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1883 : Integer.Sparse Master := [(Sum.inr 923, 1), (Sum.inr 1806, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2051, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1883 : Integer.Sparse.reindex keyMap MixedData.row1883 = numericRow1883 := by decide +kernel

theorem numericCheck1883 (x : Master → ℝ) : Integer.Sparse.eval numericRow1883 x =
    (1 : ℝ) * reducedSource1883 x := by
  norm_num [numericRow1883, reducedSource1883, Integer.Sparse.eval, Sparse.eval, nodeValue923, nodeValue1806, nodeValue2021, nodeValue2034, nodeValue2051, nodeValue2058, nodeValue4084]

noncomputable def reducedSource1884 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2440 x + ((1 : ℝ) * Sparse.eval nodeValue3062 x + ((1 : ℝ) * Sparse.eval nodeValue3189 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1884 : Integer.Sparse Master := [(Sum.inr 2440, 1), (Sum.inr 3062, 1), (Sum.inr 3189, 1), (Sum.inr 3202, 2), (Sum.inr 3789, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1884 : Integer.Sparse.reindex keyMap MixedData.row1884 = numericRow1884 := by decide +kernel

theorem numericCheck1884 (x : Master → ℝ) : Integer.Sparse.eval numericRow1884 x =
    (1 : ℝ) * reducedSource1884 x := by
  norm_num [numericRow1884, reducedSource1884, Integer.Sparse.eval, Sparse.eval, nodeValue2440, nodeValue3062, nodeValue3189, nodeValue3202, nodeValue3789, nodeValue4091]

noncomputable def reducedSource1885 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue920 x + ((1 : ℝ) * Sparse.eval nodeValue1803 x + ((1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1885 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 2033, 1), (Sum.inr 2051, 1), (Sum.inr 2054, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1885 : Integer.Sparse.reindex keyMap MixedData.row1885 = numericRow1885 := by decide +kernel

theorem numericCheck1885 (x : Master → ℝ) : Integer.Sparse.eval numericRow1885 x =
    (1 : ℝ) * reducedSource1885 x := by
  norm_num [numericRow1885, reducedSource1885, Integer.Sparse.eval, Sparse.eval, nodeValue920, nodeValue1803, nodeValue2033, nodeValue2051, nodeValue2054, nodeValue4084]

noncomputable def reducedSource1886 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2895 x + ((2 : ℝ) * Sparse.eval nodeValue3164 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1886 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 3164, 2), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1886 : Integer.Sparse.reindex keyMap MixedData.row1886 = numericRow1886 := by decide +kernel

theorem numericCheck1886 (x : Master → ℝ) : Integer.Sparse.eval numericRow1886 x =
    (1 : ℝ) * reducedSource1886 x := by
  norm_num [numericRow1886, reducedSource1886, Integer.Sparse.eval, Sparse.eval, nodeValue2895, nodeValue3164, nodeValue3172, nodeValue3197, nodeValue3964, nodeValue4091]

noncomputable def reducedSource1887 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue3162 x + ((1 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1887 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 3162, 1), (Sum.inr 3163, 1), (Sum.inr 3170, 1), (Sum.inr 3196, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1887 : Integer.Sparse.reindex keyMap MixedData.row1887 = numericRow1887 := by decide +kernel

theorem numericCheck1887 (x : Master → ℝ) : Integer.Sparse.eval numericRow1887 x =
    (1 : ℝ) * reducedSource1887 x := by
  norm_num [numericRow1887, reducedSource1887, Integer.Sparse.eval, Sparse.eval, nodeValue2430, nodeValue3162, nodeValue3163, nodeValue3170, nodeValue3196, nodeValue3782, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
