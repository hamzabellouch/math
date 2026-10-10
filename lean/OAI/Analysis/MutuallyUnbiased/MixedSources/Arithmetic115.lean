import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1840 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((2 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((2 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3131 x + ((2 : ℝ) * Sparse.eval nodeValue3163 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow1840 : Integer.Sparse Master := [(Sum.inl 0, -120), (Sum.inl 5, -40), (Sum.inl 2, 170), (Sum.inl 54, 480), (Sum.inl 1, 290), (Sum.inr 1321, 4320), (Sum.inr 1323, 2160), (Sum.inr 1325, 2160), (Sum.inr 1813, 4320), (Sum.inr 1820, 2160), (Sum.inr 2113, 2160), (Sum.inr 2816, 4320), (Sum.inr 2821, 2160), (Sum.inr 3040, 4320), (Sum.inr 3055, 2160), (Sum.inr 3056, 2160), (Sum.inr 3131, 4320), (Sum.inr 3163, 4320), (Sum.inr 3180, 4320)]

theorem reindexCheck1840 : Integer.Sparse.reindex keyMap MixedData.row1840 = numericRow1840 := by decide +kernel

theorem numericCheck1840 (x : Master → ℝ) : Integer.Sparse.eval numericRow1840 x =
    (2160 : ℝ) * reducedSource1840 x := by
  norm_num [numericRow1840, reducedSource1840, Integer.Sparse.eval, Sparse.eval, nodeValue1321, nodeValue1323, nodeValue1325, nodeValue1419, nodeValue1813, nodeValue1820, nodeValue2113, nodeValue2816, nodeValue2821, nodeValue2966, nodeValue3040, nodeValue3055, nodeValue3056, nodeValue3103, nodeValue3131, nodeValue3163, nodeValue3180, nodeValue3185, nodeValue3206, nodeValue3225, nodeValue3230]
  ring

noncomputable def reducedSource1841 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1712 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((2 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2194 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((2 : ℝ) * Sparse.eval nodeValue2242 x + ((2 : ℝ) * Sparse.eval nodeValue2249 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + 0))))))))))))))))))))

def numericRow1841 : Integer.Sparse Master := [(Sum.inr 1712, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1743, 1), (Sum.inr 2162, 2), (Sum.inr 2163, 1), (Sum.inr 2194, 2), (Sum.inr 2212, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 2), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 1), (Sum.inr 2273, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2729, 2), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1)]

theorem reindexCheck1841 : Integer.Sparse.reindex keyMap MixedData.row1841 = numericRow1841 := by decide +kernel

theorem numericCheck1841 (x : Master → ℝ) : Integer.Sparse.eval numericRow1841 x =
    (1 : ℝ) * reducedSource1841 x := by
  norm_num [numericRow1841, reducedSource1841, Integer.Sparse.eval, Sparse.eval, nodeValue1712, nodeValue1735, nodeValue1738, nodeValue1743, nodeValue2162, nodeValue2163, nodeValue2194, nodeValue2212, nodeValue2215, nodeValue2242, nodeValue2249, nodeValue2251, nodeValue2261, nodeValue2264, nodeValue2273, nodeValue2278, nodeValue2282, nodeValue2729, nodeValue2765, nodeValue2771, nodeValue2774]

noncomputable def reducedSource1842 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1826 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((1 : ℝ) * Sparse.eval nodeValue1832 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1842 : Integer.Sparse Master := [(Sum.inr 1826, 2), (Sum.inr 1830, 1), (Sum.inr 1832, 1), (Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1842 : Integer.Sparse.reindex keyMap MixedData.row1842 = numericRow1842 := by decide +kernel

theorem numericCheck1842 (x : Master → ℝ) : Integer.Sparse.eval numericRow1842 x =
    (1 : ℝ) * reducedSource1842 x := by
  norm_num [numericRow1842, reducedSource1842, Integer.Sparse.eval, Sparse.eval, nodeValue1826, nodeValue1830, nodeValue1832, nodeValue2115, nodeValue3056, nodeValue4084]

noncomputable def reducedSource1843 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1826 x + ((1 : ℝ) * Sparse.eval nodeValue1974 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1843 : Integer.Sparse Master := [(Sum.inr 946, 1), (Sum.inr 1826, 1), (Sum.inr 1974, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1843 : Integer.Sparse.reindex keyMap MixedData.row1843 = numericRow1843 := by decide +kernel

theorem numericCheck1843 (x : Master → ℝ) : Integer.Sparse.eval numericRow1843 x =
    (1 : ℝ) * reducedSource1843 x := by
  norm_num [numericRow1843, reducedSource1843, Integer.Sparse.eval, Sparse.eval, nodeValue946, nodeValue1826, nodeValue1974, nodeValue2106, nodeValue2108, nodeValue2115, nodeValue4084]

noncomputable def reducedSource1844 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4238 x + ((1 : ℝ) * Sparse.eval nodeValue4241 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((2 : ℝ) * Sparse.eval nodeValue4673 x + ((2 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4724 x + ((2 : ℝ) * Sparse.eval nodeValue4727 x + ((2 : ℝ) * Sparse.eval nodeValue4749 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((1 : ℝ) * Sparse.eval nodeValue4862 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + 0))))))))))))))))))))

def numericRow1844 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 23, 720), (Sum.inl 12, -240), (Sum.inl 27, 180), (Sum.inl 1, 510), (Sum.inr 738, -12960), (Sum.inr 741, -6480), (Sum.inr 743, -6480), (Sum.inr 819, -12960), (Sum.inr 820, -6480), (Sum.inr 830, -12960), (Sum.inr 844, -6480), (Sum.inr 1799, -12960), (Sum.inr 1814, -12960), (Sum.inr 1817, -6480), (Sum.inr 1819, -6480), (Sum.inr 1878, -12960), (Sum.inr 1881, -12960), (Sum.inr 1919, -12960), (Sum.inr 1920, -12960), (Sum.inr 1928, -25920), (Sum.inr 1939, -12960), (Sum.inr 2101, -25920), (Sum.inr 2103, -12960), (Sum.inr 2110, -12960), (Sum.inr 2112, -6480), (Sum.inr 2115, -6480), (Sum.inr 2157, -12960), (Sum.inr 2159, -6480), (Sum.inr 2169, -6480), (Sum.inr 2275, -12960), (Sum.inr 2276, -6480), (Sum.inr 2279, -12960), (Sum.inr 2287, -6480), (Sum.inr 3732, -12960), (Sum.inr 3811, -12960), (Sum.inr 3886, -12960), (Sum.inr 3893, -6480), (Sum.inr 3907, -6480)]

theorem reindexCheck1844 : Integer.Sparse.reindex keyMap MixedData.row1844 = numericRow1844 := by decide +kernel

theorem numericCheck1844 (x : Master → ℝ) : Integer.Sparse.eval numericRow1844 x =
    (25920 : ℝ) * reducedSource1844 x := by
  norm_num [numericRow1844, reducedSource1844, Integer.Sparse.eval, Sparse.eval, nodeValue4238, nodeValue4241, nodeValue4243, nodeValue4278, nodeValue4673, nodeValue4688, nodeValue4691, nodeValue4693, nodeValue4724, nodeValue4727, nodeValue4749, nodeValue4860, nodeValue4862, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue5384, nodeValue5389, nodeValue5443, nodeValue5449]
  ring

noncomputable def reducedSource1845 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((2 : ℝ) * Sparse.eval nodeValue1799 x + ((2 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1878 x + ((2 : ℝ) * Sparse.eval nodeValue1881 x + ((2 : ℝ) * Sparse.eval nodeValue1928 x + ((2 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2103 x + ((2 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow1845 : Integer.Sparse Master := [(Sum.inl 0, -81), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 23, -720), (Sum.inl 12, 240), (Sum.inl 27, -180), (Sum.inl 1, -510), (Sum.inr 738, 12960), (Sum.inr 741, 6480), (Sum.inr 743, 6480), (Sum.inr 830, 6480), (Sum.inr 1799, 12960), (Sum.inr 1814, 12960), (Sum.inr 1817, 6480), (Sum.inr 1819, 6480), (Sum.inr 1878, 12960), (Sum.inr 1881, 12960), (Sum.inr 1928, 12960), (Sum.inr 2101, 12960), (Sum.inr 2103, 6480), (Sum.inr 2110, 12960), (Sum.inr 2112, 6480), (Sum.inr 2276, 6480), (Sum.inr 2279, 6480), (Sum.inr 3732, 12960), (Sum.inr 3886, 6480)]

theorem reindexCheck1845 : Integer.Sparse.reindex keyMap MixedData.row1845 = numericRow1845 := by decide +kernel

theorem numericCheck1845 (x : Master → ℝ) : Integer.Sparse.eval numericRow1845 x =
    (6480 : ℝ) * reducedSource1845 x := by
  norm_num [numericRow1845, reducedSource1845, Integer.Sparse.eval, Sparse.eval, nodeValue738, nodeValue741, nodeValue743, nodeValue830, nodeValue1799, nodeValue1814, nodeValue1817, nodeValue1819, nodeValue1878, nodeValue1881, nodeValue1928, nodeValue2101, nodeValue2103, nodeValue2110, nodeValue2112, nodeValue2276, nodeValue2279, nodeValue3732, nodeValue3740, nodeValue3886, nodeValue3889]
  ring

noncomputable def reducedSource1846 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1653 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((2 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((2 : ℝ) * Sparse.eval nodeValue2072 x + ((2 : ℝ) * Sparse.eval nodeValue2081 x + ((2 : ℝ) * Sparse.eval nodeValue2082 x + ((2 : ℝ) * Sparse.eval nodeValue2093 x + ((2 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2114 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((2 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2137 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + 0))))))))))))))))))))

def numericRow1846 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 5, 160), (Sum.inl 2, -80), (Sum.inl 7, 320), (Sum.inl 51, -960), (Sum.inl 3, 320), (Sum.inl 1, -220), (Sum.inr 1640, 17280), (Sum.inr 1652, 8640), (Sum.inr 1653, 8640), (Sum.inr 1660, 8640), (Sum.inr 2028, 17280), (Sum.inr 2065, 8640), (Sum.inr 2072, 17280), (Sum.inr 2081, 17280), (Sum.inr 2082, 17280), (Sum.inr 2093, 17280), (Sum.inr 2094, 17280), (Sum.inr 2114, 8640), (Sum.inr 2116, 8640), (Sum.inr 2122, 17280), (Sum.inr 2137, 8640), (Sum.inr 2138, 8640), (Sum.inr 2620, 17280), (Sum.inr 2643, 8640)]

theorem reindexCheck1846 : Integer.Sparse.reindex keyMap MixedData.row1846 = numericRow1846 := by decide +kernel

theorem numericCheck1846 (x : Master → ℝ) : Integer.Sparse.eval numericRow1846 x =
    (8640 : ℝ) * reducedSource1846 x := by
  norm_num [numericRow1846, reducedSource1846, Integer.Sparse.eval, Sparse.eval, nodeValue1640, nodeValue1652, nodeValue1653, nodeValue1660, nodeValue2028, nodeValue2065, nodeValue2066, nodeValue2072, nodeValue2081, nodeValue2082, nodeValue2093, nodeValue2094, nodeValue2114, nodeValue2116, nodeValue2122, nodeValue2137, nodeValue2138, nodeValue2604, nodeValue2620, nodeValue2643, nodeValue2644]
  ring

noncomputable def reducedSource1847 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((1 : ℝ) * Sparse.eval nodeValue1374 x + ((1 : ℝ) * Sparse.eval nodeValue1444 x + ((2 : ℝ) * Sparse.eval nodeValue2867 x + ((2 : ℝ) * Sparse.eval nodeValue2872 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3095 x + ((2 : ℝ) * Sparse.eval nodeValue3151 x + ((2 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3160 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((2 : ℝ) * Sparse.eval nodeValue3168 x + ((2 : ℝ) * Sparse.eval nodeValue3174 x + ((2 : ℝ) * Sparse.eval nodeValue3178 x + ((1 : ℝ) * Sparse.eval nodeValue3188 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

def numericRow1847 : Integer.Sparse Master := [(Sum.inl 0, -120), (Sum.inl 5, 200), (Sum.inl 2, -130), (Sum.inl 54, 480), (Sum.inl 1, -10), (Sum.inr 1371, 4320), (Sum.inr 1373, 2160), (Sum.inr 1374, 2160), (Sum.inr 2867, 4320), (Sum.inr 2872, 4320), (Sum.inr 2887, 2160), (Sum.inr 2888, 2160), (Sum.inr 2889, 2160), (Sum.inr 3151, 4320), (Sum.inr 3159, 4320), (Sum.inr 3160, 2160), (Sum.inr 3161, 2160), (Sum.inr 3168, 4320), (Sum.inr 3174, 4320)]

theorem reindexCheck1847 : Integer.Sparse.reindex keyMap MixedData.row1847 = numericRow1847 := by decide +kernel

theorem numericCheck1847 (x : Master → ℝ) : Integer.Sparse.eval numericRow1847 x =
    (2160 : ℝ) * reducedSource1847 x := by
  norm_num [numericRow1847, reducedSource1847, Integer.Sparse.eval, Sparse.eval, nodeValue1371, nodeValue1373, nodeValue1374, nodeValue1444, nodeValue2867, nodeValue2872, nodeValue2887, nodeValue2888, nodeValue2889, nodeValue2968, nodeValue3095, nodeValue3151, nodeValue3159, nodeValue3160, nodeValue3161, nodeValue3168, nodeValue3174, nodeValue3178, nodeValue3188, nodeValue3206, nodeValue3216]
  ring

noncomputable def reducedSource1848 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4369 x + ((2 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((2 : ℝ) * Sparse.eval nodeValue4701 x + ((2 : ℝ) * Sparse.eval nodeValue4705 x + ((2 : ℝ) * Sparse.eval nodeValue4774 x + ((4 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + 0)))))))))))))

def numericRow1848 : Integer.Sparse Master := [(Sum.inr 1050, -1), (Sum.inr 1751, -1), (Sum.inr 2029, -2), (Sum.inr 2107, -4), (Sum.inr 2112, -2), (Sum.inr 2225, -2), (Sum.inr 2260, -4), (Sum.inr 2287, -2), (Sum.inr 2782, -2), (Sum.inr 3583, -2), (Sum.inr 4369, 8), (Sum.inr 4374, 8), (Sum.inr 4701, 8), (Sum.inr 4705, 8), (Sum.inr 4774, 8), (Sum.inr 4777, 16), (Sum.inr 5269, 8), (Sum.inr 5303, 4)]

theorem reindexCheck1848 : Integer.Sparse.reindex keyMap MixedData.row1848 = numericRow1848 := by decide +kernel

theorem numericCheck1848 (x : Master → ℝ) : Integer.Sparse.eval numericRow1848 x =
    (4 : ℝ) * reducedSource1848 x := by
  norm_num [numericRow1848, reducedSource1848, Integer.Sparse.eval, Sparse.eval, nodeValue4369, nodeValue4374, nodeValue4467, nodeValue4701, nodeValue4705, nodeValue4774, nodeValue4777, nodeValue4811, nodeValue4866, nodeValue4871, nodeValue4895, nodeValue5269, nodeValue5303, nodeValue5304]
  ring

noncomputable def reducedSource1849 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1322 x + ((2 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((4 : ℝ) * Sparse.eval nodeValue2340 x + ((2 : ℝ) * Sparse.eval nodeValue2346 x + ((2 : ℝ) * Sparse.eval nodeValue2602 x + ((2 : ℝ) * Sparse.eval nodeValue3108 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((2 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3132 x + ((2 : ℝ) * Sparse.eval nodeValue3164 x + ((4 : ℝ) * Sparse.eval nodeValue3184 x + ((2 : ℝ) * Sparse.eval nodeValue3207 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

def numericRow1849 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, -40), (Sum.inl 2, -80), (Sum.inl 56, 480), (Sum.inl 1, -160), (Sum.inr 1322, 2880), (Sum.inr 1324, 2880), (Sum.inr 2340, 5760), (Sum.inr 2346, 2880), (Sum.inr 3108, 2880), (Sum.inr 3118, 1440), (Sum.inr 3132, 2880), (Sum.inr 3164, 2880)]

theorem reindexCheck1849 : Integer.Sparse.reindex keyMap MixedData.row1849 = numericRow1849 := by decide +kernel

theorem numericCheck1849 (x : Master → ℝ) : Integer.Sparse.eval numericRow1849 x =
    (1440 : ℝ) * reducedSource1849 x := by
  norm_num [numericRow1849, reducedSource1849, Integer.Sparse.eval, Sparse.eval, nodeValue1322, nodeValue1324, nodeValue1420, nodeValue2340, nodeValue2346, nodeValue2602, nodeValue3108, nodeValue3118, nodeValue3119, nodeValue3132, nodeValue3164, nodeValue3184, nodeValue3207, nodeValue3229]
  ring

noncomputable def reducedSource1850 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1721 x + ((2 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue2199 x + ((4 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2257 x + ((4 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2287 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + 0)))))))))))))

def numericRow1850 : Integer.Sparse Master := [(Sum.inr 1721, 2), (Sum.inr 1748, 2), (Sum.inr 1751, 1), (Sum.inr 2199, 2), (Sum.inr 2223, 4), (Sum.inr 2225, 2), (Sum.inr 2257, 2), (Sum.inr 2260, 4), (Sum.inr 2286, 2), (Sum.inr 2287, 2), (Sum.inr 2736, 2), (Sum.inr 2779, 1), (Sum.inr 2782, 2)]

theorem reindexCheck1850 : Integer.Sparse.reindex keyMap MixedData.row1850 = numericRow1850 := by decide +kernel

theorem numericCheck1850 (x : Master → ℝ) : Integer.Sparse.eval numericRow1850 x =
    (1 : ℝ) * reducedSource1850 x := by
  norm_num [numericRow1850, reducedSource1850, Integer.Sparse.eval, Sparse.eval, nodeValue1721, nodeValue1748, nodeValue1751, nodeValue2199, nodeValue2223, nodeValue2225, nodeValue2257, nodeValue2260, nodeValue2286, nodeValue2287, nodeValue2291, nodeValue2736, nodeValue2779, nodeValue2782]

noncomputable def reducedSource1851 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1827 x + ((2 : ℝ) * Sparse.eval nodeValue1831 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1851 : Integer.Sparse Master := [(Sum.inr 1827, 2), (Sum.inr 1831, 2), (Sum.inr 2116, 1), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1851 : Integer.Sparse.reindex keyMap MixedData.row1851 = numericRow1851 := by decide +kernel

theorem numericCheck1851 (x : Master → ℝ) : Integer.Sparse.eval numericRow1851 x =
    (1 : ℝ) * reducedSource1851 x := by
  norm_num [numericRow1851, reducedSource1851, Integer.Sparse.eval, Sparse.eval, nodeValue1827, nodeValue1831, nodeValue2116, nodeValue3118, nodeValue4083]

noncomputable def reducedSource1852 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue947 x + ((1 : ℝ) * Sparse.eval nodeValue1827 x + ((1 : ℝ) * Sparse.eval nodeValue1975 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1852 : Integer.Sparse Master := [(Sum.inr 947, 1), (Sum.inr 1827, 1), (Sum.inr 1975, 1), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1852 : Integer.Sparse.reindex keyMap MixedData.row1852 = numericRow1852 := by decide +kernel

theorem numericCheck1852 (x : Master → ℝ) : Integer.Sparse.eval numericRow1852 x =
    (1 : ℝ) * reducedSource1852 x := by
  norm_num [numericRow1852, reducedSource1852, Integer.Sparse.eval, Sparse.eval, nodeValue947, nodeValue1827, nodeValue1975, nodeValue2107, nodeValue2116, nodeValue4083]

noncomputable def reducedSource1853 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4239 x + ((2 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4725 x + ((4 : ℝ) * Sparse.eval nodeValue4726 x + ((2 : ℝ) * Sparse.eval nodeValue4750 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + 0)))))))))))))

def numericRow1853 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 24, 360), (Sum.inl 4, -240), (Sum.inl 27, 90), (Sum.inl 1, -120), (Sum.inr 739, -6480), (Sum.inr 742, -6480), (Sum.inr 831, -3240), (Sum.inr 841, -6480), (Sum.inr 843, -6480), (Sum.inr 858, -3240), (Sum.inr 1815, -6480), (Sum.inr 1818, -6480), (Sum.inr 1879, -6480), (Sum.inr 1880, -12960), (Sum.inr 1929, -6480), (Sum.inr 1936, -6480), (Sum.inr 1938, -12960), (Sum.inr 1949, -6480), (Sum.inr 2107, -12960), (Sum.inr 2109, -6480), (Sum.inr 2166, -6480), (Sum.inr 2168, -6480), (Sum.inr 2260, -12960), (Sum.inr 2261, -6480), (Sum.inr 2266, -6480), (Sum.inr 2278, -6480), (Sum.inr 3790, -6480), (Sum.inr 3815, -6480), (Sum.inr 3894, -3240), (Sum.inr 3913, -6480)]

theorem reindexCheck1853 : Integer.Sparse.reindex keyMap MixedData.row1853 = numericRow1853 := by decide +kernel

theorem numericCheck1853 (x : Master → ℝ) : Integer.Sparse.eval numericRow1853 x =
    (12960 : ℝ) * reducedSource1853 x := by
  norm_num [numericRow1853, reducedSource1853, Integer.Sparse.eval, Sparse.eval, nodeValue4239, nodeValue4242, nodeValue4279, nodeValue4689, nodeValue4692, nodeValue4725, nodeValue4726, nodeValue4750, nodeValue4866, nodeValue4868, nodeValue4896, nodeValue5390, nodeValue5404, nodeValue5451]
  ring

noncomputable def reducedSource1854 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue739 x + ((2 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((2 : ℝ) * Sparse.eval nodeValue1815 x + ((2 : ℝ) * Sparse.eval nodeValue1818 x + ((2 : ℝ) * Sparse.eval nodeValue1879 x + ((4 : ℝ) * Sparse.eval nodeValue1880 x + ((2 : ℝ) * Sparse.eval nodeValue1929 x + ((4 : ℝ) * Sparse.eval nodeValue2107 x + ((2 : ℝ) * Sparse.eval nodeValue2109 x + ((2 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + 0)))))))))))))

def numericRow1854 : Integer.Sparse Master := [(Sum.inl 0, -81), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 24, -360), (Sum.inl 4, 240), (Sum.inl 27, -90), (Sum.inl 1, 120), (Sum.inr 739, 6480), (Sum.inr 742, 6480), (Sum.inr 831, 3240), (Sum.inr 1815, 6480), (Sum.inr 1818, 6480), (Sum.inr 1879, 6480), (Sum.inr 1880, 12960), (Sum.inr 1929, 6480), (Sum.inr 2107, 12960), (Sum.inr 2109, 6480), (Sum.inr 2278, 6480), (Sum.inr 3790, 6480)]

theorem reindexCheck1854 : Integer.Sparse.reindex keyMap MixedData.row1854 = numericRow1854 := by decide +kernel

theorem numericCheck1854 (x : Master → ℝ) : Integer.Sparse.eval numericRow1854 x =
    (3240 : ℝ) * reducedSource1854 x := by
  norm_num [numericRow1854, reducedSource1854, Integer.Sparse.eval, Sparse.eval, nodeValue739, nodeValue742, nodeValue831, nodeValue1815, nodeValue1818, nodeValue1879, nodeValue1880, nodeValue1929, nodeValue2107, nodeValue2109, nodeValue2278, nodeValue3741, nodeValue3790, nodeValue3888]
  ring

noncomputable def reducedSource1855 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4487 x + ((2 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4506 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4825 x + ((4 : ℝ) * Sparse.eval nodeValue4828 x + ((2 : ℝ) * Sparse.eval nodeValue4842 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((4 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4884 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))))

def numericRow1855 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 1075, -1080), (Sum.inr 1653, -1080), (Sum.inr 2029, -1080), (Sum.inr 2048, -2160), (Sum.inr 2082, -2160), (Sum.inr 2115, -1080), (Sum.inr 2225, -1080), (Sum.inr 2276, -1080), (Sum.inr 2889, -1080), (Sum.inr 3616, -540), (Sum.inr 3631, -1080), (Sum.inr 4487, 4320), (Sum.inr 4506, 2160), (Sum.inr 4825, 4320), (Sum.inr 4842, 4320), (Sum.inr 4856, 8640), (Sum.inr 4884, 4320), (Sum.inr 5189, 4320)]

theorem reindexCheck1855 : Integer.Sparse.reindex keyMap MixedData.row1855 = numericRow1855 := by decide +kernel

theorem numericCheck1855 (x : Master → ℝ) : Integer.Sparse.eval numericRow1855 x =
    (2160 : ℝ) * reducedSource1855 x := by
  norm_num [numericRow1855, reducedSource1855, Integer.Sparse.eval, Sparse.eval, nodeValue4487, nodeValue4491, nodeValue4506, nodeValue4811, nodeValue4825, nodeValue4828, nodeValue4842, nodeValue4846, nodeValue4856, nodeValue4874, nodeValue4884, nodeValue5177, nodeValue5189, nodeValue5207]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
