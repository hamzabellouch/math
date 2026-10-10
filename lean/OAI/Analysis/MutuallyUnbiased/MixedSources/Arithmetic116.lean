import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1856 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1641 x + ((2 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((2 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2066 x + ((2 : ℝ) * Sparse.eval nodeValue2073 x + ((4 : ℝ) * Sparse.eval nodeValue2082 x + ((4 : ℝ) * Sparse.eval nodeValue2094 x + ((2 : ℝ) * Sparse.eval nodeValue2115 x + ((2 : ℝ) * Sparse.eval nodeValue2123 x + ((2 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue2621 x + ((2 : ℝ) * Sparse.eval nodeValue2644 x + 0)))))))))))))

def numericRow1856 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, 120), (Sum.inl 2, -60), (Sum.inl 8, 160), (Sum.inl 51, -960), (Sum.inl 1, 100), (Sum.inr 1641, 8640), (Sum.inr 1653, 8640), (Sum.inr 1661, 4320), (Sum.inr 2029, 8640), (Sum.inr 2073, 8640), (Sum.inr 2082, 17280), (Sum.inr 2094, 17280), (Sum.inr 2115, 8640), (Sum.inr 2123, 8640), (Sum.inr 2138, 8640), (Sum.inr 2621, 8640)]

theorem reindexCheck1856 : Integer.Sparse.reindex keyMap MixedData.row1856 = numericRow1856 := by decide +kernel

theorem numericCheck1856 (x : Master → ℝ) : Integer.Sparse.eval numericRow1856 x =
    (4320 : ℝ) * reducedSource1856 x := by
  norm_num [numericRow1856, reducedSource1856, Integer.Sparse.eval, Sparse.eval, nodeValue1641, nodeValue1653, nodeValue1661, nodeValue2029, nodeValue2066, nodeValue2073, nodeValue2082, nodeValue2094, nodeValue2115, nodeValue2123, nodeValue2138, nodeValue2605, nodeValue2621, nodeValue2644]
  ring

noncomputable def reducedSource1857 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1876 x + ((1 : ℝ) * Sparse.eval nodeValue1880 x + ((1 : ℝ) * Sparse.eval nodeValue1881 x + ((1 : ℝ) * Sparse.eval nodeValue1918 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue3448 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1857 : Integer.Sparse Master := [(Sum.inr 1876, 1), (Sum.inr 1880, 1), (Sum.inr 1881, 1), (Sum.inr 2082, 1), (Sum.inr 3448, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1857 : Integer.Sparse.reindex keyMap MixedData.row1857 = numericRow1857 := by decide +kernel

theorem numericCheck1857 (x : Master → ℝ) : Integer.Sparse.eval numericRow1857 x =
    (1 : ℝ) * reducedSource1857 x := by
  norm_num [numericRow1857, reducedSource1857, Integer.Sparse.eval, Sparse.eval, nodeValue1876, nodeValue1880, nodeValue1881, nodeValue1918, nodeValue2082, nodeValue3448, nodeValue4080]

noncomputable def reducedSource1858 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4336 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4665 x + ((1 : ℝ) * Sparse.eval nodeValue4667 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4671 x + ((1 : ℝ) * Sparse.eval nodeValue4687 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4773 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + 0)))))))))))))))))))))))))))))

def numericRow1858 : Integer.Sparse Master := [(Sum.inr 932, -1), (Sum.inr 1049, -1), (Sum.inr 1681, -1), (Sum.inr 1738, -1), (Sum.inr 1814, -1), (Sum.inr 1966, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -1), (Sum.inr 2028, -1), (Sum.inr 2058, -1), (Sum.inr 2115, -1), (Sum.inr 2157, -1), (Sum.inr 2177, -1), (Sum.inr 2190, -1), (Sum.inr 2203, -1), (Sum.inr 2215, -1), (Sum.inr 2216, -1), (Sum.inr 2266, -1), (Sum.inr 2276, -1), (Sum.inr 2278, -1), (Sum.inr 2722, -1), (Sum.inr 3533, -1), (Sum.inr 4328, 4), (Sum.inr 4334, 4), (Sum.inr 4336, 4), (Sum.inr 4665, 4), (Sum.inr 4667, 4), (Sum.inr 4669, 4), (Sum.inr 4671, 4), (Sum.inr 4687, 4), (Sum.inr 4756, 4), (Sum.inr 4773, 4), (Sum.inr 4776, 4), (Sum.inr 4803, 4), (Sum.inr 4808, 4), (Sum.inr 5232, 4), (Sum.inr 5243, 4), (Sum.inr 5264, 4), (Sum.inr 5266, 4)]

theorem reindexCheck1858 : Integer.Sparse.reindex keyMap MixedData.row1858 = numericRow1858 := by decide +kernel

theorem numericCheck1858 (x : Master → ℝ) : Integer.Sparse.eval numericRow1858 x =
    (4 : ℝ) * reducedSource1858 x := by
  norm_num [numericRow1858, reducedSource1858, Integer.Sparse.eval, Sparse.eval, nodeValue4328, nodeValue4334, nodeValue4336, nodeValue4354, nodeValue4466, nodeValue4665, nodeValue4667, nodeValue4669, nodeValue4671, nodeValue4687, nodeValue4688, nodeValue4756, nodeValue4766, nodeValue4773, nodeValue4776, nodeValue4801, nodeValue4803, nodeValue4804, nodeValue4808, nodeValue4810, nodeValue4834, nodeValue4839, nodeValue4874, nodeValue4894, nodeValue4896, nodeValue5232, nodeValue5243, nodeValue5258, nodeValue5264, nodeValue5266]
  ring

noncomputable def reducedSource1859 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1332 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1343 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1793 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3141 x + ((1 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3190 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0)))))))))))))))))))))))))))))

def numericRow1859 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, -60), (Sum.inl 2, 155), (Sum.inl 7, 80), (Sum.inl 35, 80), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 54, -240), (Sum.inl 1, 125), (Sum.inr 1330, 1440), (Sum.inr 1332, 1440), (Sum.inr 1334, 1440), (Sum.inr 1793, 1440), (Sum.inr 1797, 1440), (Sum.inr 1813, 1440), (Sum.inr 2092, 1440), (Sum.inr 2800, 1440), (Sum.inr 2803, 1440), (Sum.inr 2816, 1440), (Sum.inr 3030, 1440), (Sum.inr 3039, 1440), (Sum.inr 3040, 1440), (Sum.inr 3045, 1440), (Sum.inr 3134, 1440), (Sum.inr 3163, 1440), (Sum.inr 3202, 1440)]

theorem reindexCheck1859 : Integer.Sparse.reindex keyMap MixedData.row1859 = numericRow1859 := by decide +kernel

theorem numericCheck1859 (x : Master → ℝ) : Integer.Sparse.eval numericRow1859 x =
    (1440 : ℝ) * reducedSource1859 x := by
  norm_num [numericRow1859, reducedSource1859, Integer.Sparse.eval, Sparse.eval, nodeValue1330, nodeValue1332, nodeValue1334, nodeValue1343, nodeValue1419, nodeValue1793, nodeValue1797, nodeValue1813, nodeValue2092, nodeValue2800, nodeValue2803, nodeValue2816, nodeValue2941, nodeValue3030, nodeValue3039, nodeValue3040, nodeValue3045, nodeValue3089, nodeValue3134, nodeValue3141, nodeValue3163, nodeValue3187, nodeValue3190, nodeValue3202, nodeValue3205, nodeValue3206, nodeValue3210, nodeValue3214, nodeValue3225, nodeValue3230]
  ring

noncomputable def reducedSource1860 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1681 x + ((1 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2160 x + ((1 : ℝ) * Sparse.eval nodeValue2161 x + ((1 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2177 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2194 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + 0)))))))))))))))))))))))))))))

def numericRow1860 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1679, 1), (Sum.inr 1681, 1), (Sum.inr 1685, 1), (Sum.inr 1738, 1), (Sum.inr 2144, 1), (Sum.inr 2155, 1), (Sum.inr 2157, 1), (Sum.inr 2160, 1), (Sum.inr 2161, 1), (Sum.inr 2162, 1), (Sum.inr 2176, 1), (Sum.inr 2177, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 1), (Sum.inr 2195, 1), (Sum.inr 2203, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2677, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1)]

theorem reindexCheck1860 : Integer.Sparse.reindex keyMap MixedData.row1860 = numericRow1860 := by decide +kernel

theorem numericCheck1860 (x : Master → ℝ) : Integer.Sparse.eval numericRow1860 x =
    (1 : ℝ) * reducedSource1860 x := by
  norm_num [numericRow1860, reducedSource1860, Integer.Sparse.eval, Sparse.eval, nodeValue1667, nodeValue1679, nodeValue1681, nodeValue1685, nodeValue1738, nodeValue2144, nodeValue2155, nodeValue2157, nodeValue2160, nodeValue2161, nodeValue2162, nodeValue2176, nodeValue2177, nodeValue2190, nodeValue2194, nodeValue2195, nodeValue2203, nodeValue2205, nodeValue2212, nodeValue2215, nodeValue2216, nodeValue2220, nodeValue2264, nodeValue2276, nodeValue2278, nodeValue2677, nodeValue2697, nodeValue2722, nodeValue2729, nodeValue2731]

noncomputable def reducedSource1861 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1791 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1861 : Integer.Sparse Master := [(Sum.inr 1791, 1), (Sum.inr 1795, 1), (Sum.inr 1797, 1), (Sum.inr 1814, 1), (Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1861 : Integer.Sparse.reindex keyMap MixedData.row1861 = numericRow1861 := by decide +kernel

theorem numericCheck1861 (x : Master → ℝ) : Integer.Sparse.eval numericRow1861 x =
    (1 : ℝ) * reducedSource1861 x := by
  norm_num [numericRow1861, reducedSource1861, Integer.Sparse.eval, Sparse.eval, nodeValue1791, nodeValue1795, nodeValue1797, nodeValue1814, nodeValue2028, nodeValue3379, nodeValue4084]

noncomputable def reducedSource1862 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1966 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1862 : Integer.Sparse Master := [(Sum.inr 932, 1), (Sum.inr 1814, 1), (Sum.inr 1966, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1862 : Integer.Sparse.reindex keyMap MixedData.row1862 = numericRow1862 := by decide +kernel

theorem numericCheck1862 (x : Master → ℝ) : Integer.Sparse.eval numericRow1862 x =
    (1 : ℝ) * reducedSource1862 x := by
  norm_num [numericRow1862, reducedSource1862, Integer.Sparse.eval, Sparse.eval, nodeValue932, nodeValue1814, nodeValue1966, nodeValue2028, nodeValue2053, nodeValue2058, nodeValue4084]

noncomputable def reducedSource1863 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue1791 x + ((1 : ℝ) * Sparse.eval nodeValue1974 x + ((1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1863 : Integer.Sparse Master := [(Sum.inr 906, 1), (Sum.inr 1791, 1), (Sum.inr 1974, 1), (Sum.inr 2019, 1), (Sum.inr 2021, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1863 : Integer.Sparse.reindex keyMap MixedData.row1863 = numericRow1863 := by decide +kernel

theorem numericCheck1863 (x : Master → ℝ) : Integer.Sparse.eval numericRow1863 x =
    (1 : ℝ) * reducedSource1863 x := by
  norm_num [numericRow1863, reducedSource1863, Integer.Sparse.eval, Sparse.eval, nodeValue906, nodeValue1791, nodeValue1974, nodeValue2019, nodeValue2021, nodeValue2028, nodeValue4084]

noncomputable def reducedSource1864 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4200 x + ((1 : ℝ) * Sparse.eval nodeValue4203 x + ((1 : ℝ) * Sparse.eval nodeValue4205 x + ((1 : ℝ) * Sparse.eval nodeValue4223 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((1 : ℝ) * Sparse.eval nodeValue4634 x + ((1 : ℝ) * Sparse.eval nodeValue4636 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4653 x + ((1 : ℝ) * Sparse.eval nodeValue4658 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4716 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((1 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + 0)))))))))))))))))))))))))))))

def numericRow1864 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 5, 60), (Sum.inl 2, 30), (Sum.inl 7, 240), (Sum.inl 3, 960), (Sum.inl 23, -720), (Sum.inl 12, 720), (Sum.inl 27, -180), (Sum.inl 1, -120), (Sum.inr 703, -12960), (Sum.inr 706, -12960), (Sum.inr 708, -12960), (Sum.inr 724, -12960), (Sum.inr 754, -12960), (Sum.inr 755, -12960), (Sum.inr 758, -12960), (Sum.inr 764, -12960), (Sum.inr 789, -12960), (Sum.inr 823, -12960), (Sum.inr 1763, -12960), (Sum.inr 1765, -12960), (Sum.inr 1767, -12960), (Sum.inr 1781, -12960), (Sum.inr 1784, -12960), (Sum.inr 1804, -12960), (Sum.inr 1842, -12960), (Sum.inr 1843, -12960), (Sum.inr 1846, -12960), (Sum.inr 1851, -12960), (Sum.inr 1861, -12960), (Sum.inr 1870, -12960), (Sum.inr 1884, -12960), (Sum.inr 1886, -12960), (Sum.inr 1889, -12960), (Sum.inr 1900, -12960), (Sum.inr 1921, -12960), (Sum.inr 1966, -12960), (Sum.inr 1970, -12960), (Sum.inr 2016, -12960), (Sum.inr 2018, -25920), (Sum.inr 2023, -12960), (Sum.inr 2025, -12960), (Sum.inr 2028, -12960), (Sum.inr 2048, -12960), (Sum.inr 2058, -12960), (Sum.inr 2075, -12960), (Sum.inr 2082, -12960), (Sum.inr 2106, -12960), (Sum.inr 2143, -12960), (Sum.inr 2177, -12960), (Sum.inr 2186, -12960), (Sum.inr 2214, -12960), (Sum.inr 2215, -12960), (Sum.inr 2216, -12960), (Sum.inr 2224, -12960), (Sum.inr 2242, -12960), (Sum.inr 2245, -12960), (Sum.inr 2277, -12960), (Sum.inr 3693, -12960), (Sum.inr 3719, -12960), (Sum.inr 3770, -12960), (Sum.inr 3795, -12960), (Sum.inr 3850, -25920), (Sum.inr 3891, -12960), (Sum.inr 3906, -12960)]

theorem reindexCheck1864 : Integer.Sparse.reindex keyMap MixedData.row1864 = numericRow1864 := by decide +kernel

theorem numericCheck1864 (x : Master → ℝ) : Integer.Sparse.eval numericRow1864 x =
    (51840 : ℝ) * reducedSource1864 x := by
  norm_num [numericRow1864, reducedSource1864, Integer.Sparse.eval, Sparse.eval, nodeValue4200, nodeValue4203, nodeValue4205, nodeValue4223, nodeValue4255, nodeValue4634, nodeValue4636, nodeValue4638, nodeValue4653, nodeValue4658, nodeValue4678, nodeValue4707, nodeValue4716, nodeValue4731, nodeValue4766, nodeValue4770, nodeValue4798, nodeValue4800, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4828, nodeValue4839, nodeValue4865, nodeValue4889, nodeValue5355, nodeValue5378, nodeValue5387, nodeValue5432, nodeValue5435]
  ring

noncomputable def reducedSource1865 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4329 x + ((2 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4666 x + ((2 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4767 x + ((1 : ℝ) * Sparse.eval nodeValue4774 x + ((2 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5246 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + 0))))))))))))))))))))

def numericRow1865 : Integer.Sparse Master := [(Sum.inr 933, -1), (Sum.inr 1050, -1), (Sum.inr 1691, -1), (Sum.inr 1751, -1), (Sum.inr 1815, -1), (Sum.inr 1967, -1), (Sum.inr 2020, -2), (Sum.inr 2025, -2), (Sum.inr 2029, -1), (Sum.inr 2116, -1), (Sum.inr 2166, -1), (Sum.inr 2183, -1), (Sum.inr 2202, -2), (Sum.inr 2224, -2), (Sum.inr 2225, -1), (Sum.inr 2288, -1), (Sum.inr 2739, -2), (Sum.inr 3534, -2), (Sum.inr 4335, 8), (Sum.inr 4666, 4), (Sum.inr 4670, 8), (Sum.inr 4757, 8), (Sum.inr 4774, 4), (Sum.inr 4777, 8), (Sum.inr 5236, 4), (Sum.inr 5269, 4)]

theorem reindexCheck1865 : Integer.Sparse.reindex keyMap MixedData.row1865 = numericRow1865 := by decide +kernel

theorem numericCheck1865 (x : Master → ℝ) : Integer.Sparse.eval numericRow1865 x =
    (4 : ℝ) * reducedSource1865 x := by
  norm_num [numericRow1865, reducedSource1865, Integer.Sparse.eval, Sparse.eval, nodeValue4329, nodeValue4335, nodeValue4355, nodeValue4467, nodeValue4666, nodeValue4670, nodeValue4689, nodeValue4757, nodeValue4767, nodeValue4774, nodeValue4777, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4875, nodeValue4895, nodeValue5236, nodeValue5246, nodeValue5269, nodeValue5271]
  ring

noncomputable def reducedSource1866 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1331 x + ((2 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1344 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue2323 x + ((2 : ℝ) * Sparse.eval nodeValue2327 x + ((2 : ℝ) * Sparse.eval nodeValue2340 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue3104 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3142 x + ((1 : ℝ) * Sparse.eval nodeValue3164 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((1 : ℝ) * Sparse.eval nodeValue3191 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3213 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

def numericRow1866 : Integer.Sparse Master := [(Sum.inl 0, -196), (Sum.inl 5, -160), (Sum.inl 2, -160), (Sum.inl 8, 160), (Sum.inl 56, -480), (Sum.inl 1, -220), (Sum.inr 1333, 4320), (Sum.inr 2323, 4320), (Sum.inr 2327, 4320), (Sum.inr 2340, 4320), (Sum.inr 3108, 2160), (Sum.inr 3115, 2160), (Sum.inr 3135, 2160), (Sum.inr 3164, 2160)]

theorem reindexCheck1866 : Integer.Sparse.reindex keyMap MixedData.row1866 = numericRow1866 := by decide +kernel

theorem numericCheck1866 (x : Master → ℝ) : Integer.Sparse.eval numericRow1866 x =
    (2160 : ℝ) * reducedSource1866 x := by
  norm_num [numericRow1866, reducedSource1866, Integer.Sparse.eval, Sparse.eval, nodeValue1331, nodeValue1333, nodeValue1344, nodeValue1420, nodeValue2323, nodeValue2327, nodeValue2340, nodeValue2574, nodeValue3104, nodeValue3108, nodeValue3109, nodeValue3115, nodeValue3135, nodeValue3142, nodeValue3164, nodeValue3188, nodeValue3191, nodeValue3204, nodeValue3207, nodeValue3213, nodeValue3229]
  ring

noncomputable def reducedSource1867 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1671 x + ((2 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1691 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue2148 x + ((2 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((2 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2183 x + ((1 : ℝ) * Sparse.eval nodeValue2199 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + 0))))))))))))))))))))

def numericRow1867 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1691, 1), (Sum.inr 1751, 1), (Sum.inr 2148, 1), (Sum.inr 2164, 2), (Sum.inr 2166, 1), (Sum.inr 2181, 2), (Sum.inr 2183, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2288, 1), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 2739, 2)]

theorem reindexCheck1867 : Integer.Sparse.reindex keyMap MixedData.row1867 = numericRow1867 := by decide +kernel

theorem numericCheck1867 (x : Master → ℝ) : Integer.Sparse.eval numericRow1867 x =
    (1 : ℝ) * reducedSource1867 x := by
  norm_num [numericRow1867, reducedSource1867, Integer.Sparse.eval, Sparse.eval, nodeValue1671, nodeValue1689, nodeValue1691, nodeValue1751, nodeValue2148, nodeValue2164, nodeValue2166, nodeValue2181, nodeValue2183, nodeValue2199, nodeValue2202, nodeValue2223, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2288, nodeValue2291, nodeValue2682, nodeValue2701, nodeValue2736, nodeValue2739]

noncomputable def reducedSource1868 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1792 x + ((2 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1815 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1868 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1796, 2), (Sum.inr 1815, 1), (Sum.inr 2029, 1), (Sum.inr 3380, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1868 : Integer.Sparse.reindex keyMap MixedData.row1868 = numericRow1868 := by decide +kernel

theorem numericCheck1868 (x : Master → ℝ) : Integer.Sparse.eval numericRow1868 x =
    (1 : ℝ) * reducedSource1868 x := by
  norm_num [numericRow1868, reducedSource1868, Integer.Sparse.eval, Sparse.eval, nodeValue1792, nodeValue1796, nodeValue1815, nodeValue2029, nodeValue3380, nodeValue4083]

noncomputable def reducedSource1869 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1815 x + ((1 : ℝ) * Sparse.eval nodeValue1967 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2057 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1869 : Integer.Sparse Master := [(Sum.inr 933, 1), (Sum.inr 1815, 1), (Sum.inr 1967, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1869 : Integer.Sparse.reindex keyMap MixedData.row1869 = numericRow1869 := by decide +kernel

theorem numericCheck1869 (x : Master → ℝ) : Integer.Sparse.eval numericRow1869 x =
    (1 : ℝ) * reducedSource1869 x := by
  norm_num [numericRow1869, reducedSource1869, Integer.Sparse.eval, Sparse.eval, nodeValue933, nodeValue1815, nodeValue1967, nodeValue2029, nodeValue2057, nodeValue4083]

noncomputable def reducedSource1870 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue907 x + ((1 : ℝ) * Sparse.eval nodeValue1792 x + ((1 : ℝ) * Sparse.eval nodeValue1975 x + ((2 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1870 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1975, 1), (Sum.inr 2020, 2), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1870 : Integer.Sparse.reindex keyMap MixedData.row1870 = numericRow1870 := by decide +kernel

theorem numericCheck1870 (x : Master → ℝ) : Integer.Sparse.eval numericRow1870 x =
    (1 : ℝ) * reducedSource1870 x := by
  norm_num [numericRow1870, reducedSource1870, Integer.Sparse.eval, Sparse.eval, nodeValue907, nodeValue1792, nodeValue1975, nodeValue2020, nodeValue2029, nodeValue4083]

noncomputable def reducedSource1871 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4201 x + ((2 : ℝ) * Sparse.eval nodeValue4204 x + ((1 : ℝ) * Sparse.eval nodeValue4224 x + ((1 : ℝ) * Sparse.eval nodeValue4256 x + ((1 : ℝ) * Sparse.eval nodeValue4635 x + ((2 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4654 x + ((2 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4717 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((1 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + 0))))))))))))))))))))

def numericRow1871 : Integer.Sparse Master := [(Sum.inl 0, 216), (Sum.inl 5, 30), (Sum.inl 2, 75), (Sum.inl 8, 120), (Sum.inl 3, 240), (Sum.inl 24, -360), (Sum.inl 4, 240), (Sum.inl 27, -90), (Sum.inl 1, -165), (Sum.inr 704, -6480), (Sum.inr 707, -12960), (Sum.inr 725, -6480), (Sum.inr 761, -6480), (Sum.inr 763, -12960), (Sum.inr 771, -6480), (Sum.inr 790, -6480), (Sum.inr 848, -6480), (Sum.inr 1764, -6480), (Sum.inr 1766, -12960), (Sum.inr 1782, -6480), (Sum.inr 1848, -6480), (Sum.inr 1850, -12960), (Sum.inr 1855, -6480), (Sum.inr 1860, -12960), (Sum.inr 1871, -6480), (Sum.inr 1888, -12960), (Sum.inr 1892, -6480), (Sum.inr 1901, -6480), (Sum.inr 1941, -6480), (Sum.inr 1967, -6480), (Sum.inr 1969, -12960), (Sum.inr 2020, -12960), (Sum.inr 2022, -12960), (Sum.inr 2029, -6480), (Sum.inr 2054, -12960), (Sum.inr 2183, -6480), (Sum.inr 2185, -12960), (Sum.inr 2202, -12960), (Sum.inr 2203, -12960), (Sum.inr 2206, -12960), (Sum.inr 2225, -6480), (Sum.inr 2244, -12960), (Sum.inr 2262, -12960), (Sum.inr 3694, -6480), (Sum.inr 3773, -6480), (Sum.inr 3779, -6480), (Sum.inr 3797, -6480), (Sum.inr 3898, -6480), (Sum.inr 3903, -12960)]

theorem reindexCheck1871 : Integer.Sparse.reindex keyMap MixedData.row1871 = numericRow1871 := by decide +kernel

theorem numericCheck1871 (x : Master → ℝ) : Integer.Sparse.eval numericRow1871 x =
    (25920 : ℝ) * reducedSource1871 x := by
  norm_num [numericRow1871, reducedSource1871, Integer.Sparse.eval, Sparse.eval, nodeValue4201, nodeValue4204, nodeValue4224, nodeValue4256, nodeValue4635, nodeValue4637, nodeValue4654, nodeValue4706, nodeValue4717, nodeValue4732, nodeValue4767, nodeValue4769, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4835, nodeValue4888, nodeValue5356, nodeValue5393, nodeValue5418, nodeValue5434]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
