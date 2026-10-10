import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2000 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1665 x + ((1 : ℝ) * Sparse.eval nodeValue1675 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2174 x + ((1 : ℝ) * Sparse.eval nodeValue2175 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + 0))))))))))))))))))))))))))))

def numericRow2000 : Integer.Sparse Master := [(Sum.inr 1675, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1728, 1), (Sum.inr 2142, 1), (Sum.inr 2152, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2174, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2206, 2), (Sum.inr 2207, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2230, 1), (Sum.inr 2266, 1), (Sum.inr 2673, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2743, 1)]

theorem reindexCheck2000 : Integer.Sparse.reindex keyMap MixedData.row2000 = numericRow2000 := by decide +kernel

theorem numericCheck2000 (x : Master → ℝ) : Integer.Sparse.eval numericRow2000 x =
    (1 : ℝ) * reducedSource2000 x := by
  norm_num [numericRow2000, reducedSource2000, Integer.Sparse.eval, Sparse.eval, nodeValue1665, nodeValue1675, nodeValue1676, nodeValue1682, nodeValue1728, nodeValue2142, nodeValue2152, nodeValue2153, nodeValue2158, nodeValue2174, nodeValue2175, nodeValue2178, nodeValue2191, nodeValue2192, nodeValue2205, nodeValue2206, nodeValue2207, nodeValue2216, nodeValue2217, nodeValue2229, nodeValue2230, nodeValue2265, nodeValue2266, nodeValue2293, nodeValue2673, nodeValue2695, nodeValue2723, nodeValue2724, nodeValue2743]

noncomputable def reducedSource2001 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1803 x + ((1 : ℝ) * Sparse.eval nodeValue1808 x + ((1 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1816 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow2001 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 1808, 1), (Sum.inr 1810, 1), (Sum.inr 1816, 1), (Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 4084, -1)]

theorem reindexCheck2001 : Integer.Sparse.reindex keyMap MixedData.row2001 = numericRow2001 := by decide +kernel

theorem numericCheck2001 (x : Master → ℝ) : Integer.Sparse.eval numericRow2001 x =
    (1 : ℝ) * reducedSource2001 x := by
  norm_num [numericRow2001, reducedSource2001, Integer.Sparse.eval, Sparse.eval, nodeValue1803, nodeValue1808, nodeValue1810, nodeValue1816, nodeValue2054, nodeValue3392, nodeValue4084]

noncomputable def reducedSource2002 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4210 x + ((1 : ℝ) * Sparse.eval nodeValue4212 x + ((1 : ℝ) * Sparse.eval nodeValue4213 x + ((1 : ℝ) * Sparse.eval nodeValue4224 x + ((1 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4642 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4645 x + ((1 : ℝ) * Sparse.eval nodeValue4654 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4710 x + ((1 : ℝ) * Sparse.eval nodeValue4717 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + 0))))))))))))))))))))))))))

def numericRow2002 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 20), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, 155), (Sum.inr 713, -4320), (Sum.inr 715, -4320), (Sum.inr 716, -4320), (Sum.inr 725, -4320), (Sum.inr 751, -4320), (Sum.inr 752, -4320), (Sum.inr 753, -4320), (Sum.inr 771, -4320), (Sum.inr 807, -8640), (Sum.inr 1771, -4320), (Sum.inr 1773, -4320), (Sum.inr 1774, -4320), (Sum.inr 1782, -4320), (Sum.inr 1838, -4320), (Sum.inr 1840, -4320), (Sum.inr 1841, -4320), (Sum.inr 1855, -4320), (Sum.inr 1863, -4320), (Sum.inr 1864, -4320), (Sum.inr 1871, -4320), (Sum.inr 1882, -4320), (Sum.inr 1883, -4320), (Sum.inr 1892, -4320), (Sum.inr 1909, -8640), (Sum.inr 2000, -8640), (Sum.inr 2003, -8640), (Sum.inr 2006, -8640), (Sum.inr 2020, -4320), (Sum.inr 2022, -4320), (Sum.inr 2029, -4320), (Sum.inr 2051, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -8640), (Sum.inr 2191, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -4320), (Sum.inr 2203, -4320), (Sum.inr 2206, -8640), (Sum.inr 2225, -4320), (Sum.inr 2244, -8640), (Sum.inr 2262, -8640), (Sum.inr 3705, -4320), (Sum.inr 3767, -4320), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320)]

theorem reindexCheck2002 : Integer.Sparse.reindex keyMap MixedData.row2002 = numericRow2002 := by decide +kernel

theorem numericCheck2002 (x : Master → ℝ) : Integer.Sparse.eval numericRow2002 x =
    (17280 : ℝ) * reducedSource2002 x := by
  norm_num [numericRow2002, reducedSource2002, Integer.Sparse.eval, Sparse.eval, nodeValue4210, nodeValue4212, nodeValue4213, nodeValue4224, nodeValue4265, nodeValue4642, nodeValue4644, nodeValue4645, nodeValue4654, nodeValue4709, nodeValue4710, nodeValue4717, nodeValue4737, nodeValue4787, nodeValue4788, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4831, nodeValue4832, nodeValue4835, nodeValue4888, nodeValue5368, nodeValue5395, nodeValue5428, nodeValue5434, nodeValue5439]
  ring

noncomputable def reducedSource2003 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4397 x + ((1 : ℝ) * Sparse.eval nodeValue4402 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4752 x + ((1 : ℝ) * Sparse.eval nodeValue4780 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4829 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4861 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + 0))))))))))))))))))))))))))))

def numericRow2003 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -20), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1909, -8640), (Sum.inr 1915, -4320), (Sum.inr 1946, -4320), (Sum.inr 1990, -4320), (Sum.inr 1997, -4320), (Sum.inr 2000, -8640), (Sum.inr 2020, -4320), (Sum.inr 2048, -4320), (Sum.inr 2058, -4320), (Sum.inr 2082, -4320), (Sum.inr 2107, -4320), (Sum.inr 2202, -4320), (Sum.inr 2216, -4320), (Sum.inr 2260, -4320), (Sum.inr 2512, -4320), (Sum.inr 2954, -4320), (Sum.inr 3471, -4320), (Sum.inr 3606, -4320), (Sum.inr 3607, -4320), (Sum.inr 4402, 17280), (Sum.inr 4453, 17280), (Sum.inr 4780, 17280), (Sum.inr 4799, 34560), (Sum.inr 4803, 17280), (Sum.inr 4829, 17280), (Sum.inr 4836, 17280), (Sum.inr 4861, 17280), (Sum.inr 4867, 17280), (Sum.inr 5164, 17280)]

theorem reindexCheck2003 : Integer.Sparse.reindex keyMap MixedData.row2003 = numericRow2003 := by decide +kernel

theorem numericCheck2003 (x : Master → ℝ) : Integer.Sparse.eval numericRow2003 x =
    (17280 : ℝ) * reducedSource2003 x := by
  norm_num [numericRow2003, reducedSource2003, Integer.Sparse.eval, Sparse.eval, nodeValue4397, nodeValue4402, nodeValue4404, nodeValue4424, nodeValue4453, nodeValue4737, nodeValue4742, nodeValue4745, nodeValue4752, nodeValue4780, nodeValue4782, nodeValue4787, nodeValue4799, nodeValue4802, nodeValue4803, nodeValue4828, nodeValue4829, nodeValue4834, nodeValue4836, nodeValue4838, nodeValue4839, nodeValue4861, nodeValue4866, nodeValue4867, nodeValue5102, nodeValue5135, nodeValue5164, nodeValue5169, nodeValue5170]
  ring

noncomputable def reducedSource2004 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((2 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0)))))))))))))))))))

def numericRow2004 : Integer.Sparse Master := [(Sum.inr 922, -1), (Sum.inr 930, -1), (Sum.inr 933, -2), (Sum.inr 1673, -1), (Sum.inr 1690, -1), (Sum.inr 1691, -2), (Sum.inr 1805, -1), (Sum.inr 1812, -1), (Sum.inr 1815, -2), (Sum.inr 1964, -1), (Sum.inr 1967, -2), (Sum.inr 2020, -2), (Sum.inr 2025, -2), (Sum.inr 2029, -2), (Sum.inr 2150, -1), (Sum.inr 2165, -1), (Sum.inr 2166, -2), (Sum.inr 2182, -1), (Sum.inr 2183, -2), (Sum.inr 2202, -2), (Sum.inr 2224, -2), (Sum.inr 2225, -2), (Sum.inr 2684, -1), (Sum.inr 2703, -1), (Sum.inr 2739, -2), (Sum.inr 3394, -1), (Sum.inr 3496, -1), (Sum.inr 3534, -2), (Sum.inr 4083, 4)]

theorem reindexCheck2004 : Integer.Sparse.reindex keyMap MixedData.row2004 = numericRow2004 := by decide +kernel

theorem numericCheck2004 (x : Master → ℝ) : Integer.Sparse.eval numericRow2004 x =
    (4 : ℝ) * reducedSource2004 x := by
  norm_num [numericRow2004, reducedSource2004, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4344, nodeValue4352, nodeValue4355, nodeValue4502, nodeValue4679, nodeValue4686, nodeValue4689, nodeValue4764, nodeValue4767, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4833, nodeValue4838, nodeValue4895, nodeValue5237, nodeValue5247, nodeValue5271, nodeValue5273]
  ring

noncomputable def reducedSource2005 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))))))))))

def numericRow2005 : Integer.Sparse Master := [(Sum.inr 919, -1), (Sum.inr 924, -1), (Sum.inr 927, -1), (Sum.inr 932, -1), (Sum.inr 1664, -1), (Sum.inr 1674, -1), (Sum.inr 1675, -1), (Sum.inr 1681, -1), (Sum.inr 1802, -1), (Sum.inr 1807, -1), (Sum.inr 1810, -1), (Sum.inr 1814, -1), (Sum.inr 1960, -1), (Sum.inr 1963, -1), (Sum.inr 1966, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -1), (Sum.inr 2028, -1), (Sum.inr 2051, -1), (Sum.inr 2054, -1), (Sum.inr 2058, -1), (Sum.inr 2141, -1), (Sum.inr 2151, -1), (Sum.inr 2152, -1), (Sum.inr 2157, -1), (Sum.inr 2173, -1), (Sum.inr 2174, -1), (Sum.inr 2177, -1), (Sum.inr 2190, -1), (Sum.inr 2191, -1), (Sum.inr 2203, -1), (Sum.inr 2206, -1), (Sum.inr 2215, -1), (Sum.inr 2216, -1), (Sum.inr 2672, -1), (Sum.inr 2694, -1), (Sum.inr 2722, -1), (Sum.inr 2723, -1), (Sum.inr 3391, -1), (Sum.inr 3493, -1), (Sum.inr 3533, -1), (Sum.inr 3544, -1), (Sum.inr 4084, 4)]

theorem reindexCheck2005 : Integer.Sparse.reindex keyMap MixedData.row2005 = numericRow2005 := by decide +kernel

theorem numericCheck2005 (x : Master → ℝ) : Integer.Sparse.eval numericRow2005 x =
    (4 : ℝ) * reducedSource2005 x := by
  norm_num [numericRow2005, reducedSource2005, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4341, nodeValue4346, nodeValue4349, nodeValue4354, nodeValue4498, nodeValue4676, nodeValue4681, nodeValue4684, nodeValue4688, nodeValue4760, nodeValue4763, nodeValue4766, nodeValue4801, nodeValue4804, nodeValue4810, nodeValue4831, nodeValue4834, nodeValue4835, nodeValue4839, nodeValue4841, nodeValue4846, nodeValue4894, nodeValue4895, nodeValue5228, nodeValue5241, nodeValue5258, nodeValue5259, nodeValue5274]
  ring

noncomputable def reducedSource2006 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4340 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4675 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4759 x + ((2 : ℝ) * Sparse.eval nodeValue4762 x + ((1 : ℝ) * Sparse.eval nodeValue4830 x + ((3 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4836 x + ((2 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5239 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5261 x + 0)))))))))))))))))))

def numericRow2006 : Integer.Sparse Master := [(Sum.inr 921, -1), (Sum.inr 1080, -1), (Sum.inr 1666, -1), (Sum.inr 1710, -1), (Sum.inr 1804, -1), (Sum.inr 1959, -1), (Sum.inr 2052, -3), (Sum.inr 2065, -2), (Sum.inr 2143, -1), (Sum.inr 2170, -1), (Sum.inr 2193, -3), (Sum.inr 2218, -2), (Sum.inr 2247, -1), (Sum.inr 2290, -1), (Sum.inr 2726, -2), (Sum.inr 3545, -2), (Sum.inr 4348, 8), (Sum.inr 4675, 4), (Sum.inr 4683, 8), (Sum.inr 4762, 8), (Sum.inr 4830, 4), (Sum.inr 4836, 8), (Sum.inr 5222, 4), (Sum.inr 5252, 4)]

theorem reindexCheck2006 : Integer.Sparse.reindex keyMap MixedData.row2006 = numericRow2006 := by decide +kernel

theorem numericCheck2006 (x : Master → ℝ) : Integer.Sparse.eval numericRow2006 x =
    (4 : ℝ) * reducedSource2006 x := by
  norm_num [numericRow2006, reducedSource2006, Integer.Sparse.eval, Sparse.eval, nodeValue4340, nodeValue4343, nodeValue4348, nodeValue4496, nodeValue4675, nodeValue4678, nodeValue4683, nodeValue4759, nodeValue4762, nodeValue4830, nodeValue4832, nodeValue4836, nodeValue4837, nodeValue4845, nodeValue4890, nodeValue4897, nodeValue5222, nodeValue5239, nodeValue5252, nodeValue5261]
  ring

noncomputable def reducedSource2007 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1662 x + ((1 : ℝ) * Sparse.eval nodeValue1666 x + ((2 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2139 x + ((1 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2170 x + ((2 : ℝ) * Sparse.eval nodeValue2171 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((3 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2197 x + ((2 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2691 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2726 x + 0)))))))))))))))))))

def numericRow2007 : Integer.Sparse Master := [(Sum.inr 1666, 1), (Sum.inr 1669, 2), (Sum.inr 1710, 1), (Sum.inr 2139, 1), (Sum.inr 2143, 1), (Sum.inr 2146, 2), (Sum.inr 2170, 1), (Sum.inr 2171, 2), (Sum.inr 2187, 1), (Sum.inr 2193, 3), (Sum.inr 2197, 2), (Sum.inr 2218, 2), (Sum.inr 2247, 1), (Sum.inr 2664, 1), (Sum.inr 2712, 1), (Sum.inr 2726, 2)]

theorem reindexCheck2007 : Integer.Sparse.reindex keyMap MixedData.row2007 = numericRow2007 := by decide +kernel

theorem numericCheck2007 (x : Master → ℝ) : Integer.Sparse.eval numericRow2007 x =
    (1 : ℝ) * reducedSource2007 x := by
  norm_num [numericRow2007, reducedSource2007, Integer.Sparse.eval, Sparse.eval, nodeValue1662, nodeValue1666, nodeValue1669, nodeValue1710, nodeValue2139, nodeValue2143, nodeValue2146, nodeValue2170, nodeValue2171, nodeValue2187, nodeValue2193, nodeValue2197, nodeValue2208, nodeValue2218, nodeValue2247, nodeValue2268, nodeValue2664, nodeValue2691, nodeValue2712, nodeValue2726]

noncomputable def reducedSource2008 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1801 x + ((1 : ℝ) * Sparse.eval nodeValue1804 x + ((2 : ℝ) * Sparse.eval nodeValue1809 x + ((1 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow2008 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 1804, 1), (Sum.inr 1809, 2), (Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 4085, -1)]

theorem reindexCheck2008 : Integer.Sparse.reindex keyMap MixedData.row2008 = numericRow2008 := by decide +kernel

theorem numericCheck2008 (x : Master → ℝ) : Integer.Sparse.eval numericRow2008 x =
    (1 : ℝ) * reducedSource2008 x := by
  norm_num [numericRow2008, reducedSource2008, Integer.Sparse.eval, Sparse.eval, nodeValue1801, nodeValue1804, nodeValue1809, nodeValue2052, nodeValue3389, nodeValue4085]

noncomputable def reducedSource2009 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue918 x + ((1 : ℝ) * Sparse.eval nodeValue1801 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((3 : ℝ) * Sparse.eval nodeValue2052 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow2009 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 2050, 1), (Sum.inr 2052, 3), (Sum.inr 4085, -1)]

theorem reindexCheck2009 : Integer.Sparse.reindex keyMap MixedData.row2009 = numericRow2009 := by decide +kernel

theorem numericCheck2009 (x : Master → ℝ) : Integer.Sparse.eval numericRow2009 x =
    (1 : ℝ) * reducedSource2009 x := by
  norm_num [numericRow2009, reducedSource2009, Integer.Sparse.eval, Sparse.eval, nodeValue918, nodeValue1801, nodeValue2050, nodeValue2052, nodeValue4085]

noncomputable def reducedSource2010 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4322 x + ((2 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4423 x + ((1 : ℝ) * Sparse.eval nodeValue4660 x + ((2 : ℝ) * Sparse.eval nodeValue4661 x + ((1 : ℝ) * Sparse.eval nodeValue4672 x + ((1 : ℝ) * Sparse.eval nodeValue4712 x + ((2 : ℝ) * Sparse.eval nodeValue4715 x + ((2 : ℝ) * Sparse.eval nodeValue4779 x + ((2 : ℝ) * Sparse.eval nodeValue4782 x + ((2 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue5058 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + 0))))))))))))))))))))

def numericRow2010 : Integer.Sparse Master := [(Sum.inr 900, -1), (Sum.inr 901, -2), (Sum.inr 915, -1), (Sum.inr 1588, -1), (Sum.inr 1589, -2), (Sum.inr 1632, -1), (Sum.inr 1786, -1), (Sum.inr 1787, -2), (Sum.inr 1798, -1), (Sum.inr 1982, -1), (Sum.inr 1983, -2), (Sum.inr 1987, -2), (Sum.inr 1990, -2), (Sum.inr 1996, -2), (Sum.inr 1997, -2), (Sum.inr 2000, -4), (Sum.inr 2016, -2), (Sum.inr 2046, -1), (Sum.inr 2067, -1), (Sum.inr 2075, -2), (Sum.inr 2077, -1), (Sum.inr 2536, -1), (Sum.inr 2553, -2), (Sum.inr 2556, -1), (Sum.inr 3370, -1), (Sum.inr 3514, -2), (Sum.inr 3521, -1), (Sum.inr 4080, 4)]

theorem reindexCheck2010 : Integer.Sparse.reindex keyMap MixedData.row2010 = numericRow2010 := by decide +kernel

theorem numericCheck2010 (x : Master → ℝ) : Integer.Sparse.eval numericRow2010 x =
    (4 : ℝ) * reducedSource2010 x := by
  norm_num [numericRow2010, reducedSource2010, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4322, nodeValue4323, nodeValue4337, nodeValue4423, nodeValue4660, nodeValue4661, nodeValue4672, nodeValue4712, nodeValue4715, nodeValue4779, nodeValue4782, nodeValue4787, nodeValue4798, nodeValue4826, nodeValue4834, nodeValue4838, nodeValue5058, nodeValue5123, nodeValue5134, nodeValue5137]
  ring

noncomputable def reducedSource2011 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4300 x + ((2 : ℝ) * Sparse.eval nodeValue4301 x + ((1 : ℝ) * Sparse.eval nodeValue4307 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4641 x + ((2 : ℝ) * Sparse.eval nodeValue4642 x + ((1 : ℝ) * Sparse.eval nodeValue4648 x + ((2 : ℝ) * Sparse.eval nodeValue4736 x + ((2 : ℝ) * Sparse.eval nodeValue4737 x + ((4 : ℝ) * Sparse.eval nodeValue4740 x + ((1 : ℝ) * Sparse.eval nodeValue4746 x + ((2 : ℝ) * Sparse.eval nodeValue4752 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + 0)))))))))))))))))))

def numericRow2011 : Integer.Sparse Master := [(Sum.inr 879, -2), (Sum.inr 885, -1), (Sum.inr 998, -1), (Sum.inr 1556, -2), (Sum.inr 1563, -1), (Sum.inr 1600, -1), (Sum.inr 1771, -2), (Sum.inr 1776, -1), (Sum.inr 1838, -2), (Sum.inr 1844, -1), (Sum.inr 1909, -4), (Sum.inr 1913, -4), (Sum.inr 1922, -4), (Sum.inr 1925, -2), (Sum.inr 2020, -2), (Sum.inr 2023, -1), (Sum.inr 2202, -2), (Sum.inr 2214, -1), (Sum.inr 2383, -1), (Sum.inr 2480, -2), (Sum.inr 2483, -1), (Sum.inr 3352, -1), (Sum.inr 3467, -2), (Sum.inr 3477, -1), (Sum.inr 4080, 4)]

theorem reindexCheck2011 : Integer.Sparse.reindex keyMap MixedData.row2011 = numericRow2011 := by decide +kernel

theorem numericCheck2011 (x : Master → ℝ) : Integer.Sparse.eval numericRow2011 x =
    (4 : ℝ) * reducedSource2011 x := by
  norm_num [numericRow2011, reducedSource2011, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4300, nodeValue4301, nodeValue4307, nodeValue4417, nodeValue4641, nodeValue4642, nodeValue4648, nodeValue4736, nodeValue4737, nodeValue4740, nodeValue4746, nodeValue4752, nodeValue4802, nodeValue4805, nodeValue4838, nodeValue4998, nodeValue5073, nodeValue5076, nodeValue5104]
  ring

noncomputable def reducedSource2012 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4063 x + ((1 : ℝ) * Sparse.eval nodeValue4064 x + ((2 : ℝ) * Sparse.eval nodeValue4065 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4073 x + ((1 : ℝ) * Sparse.eval nodeValue4074 x + ((2 : ℝ) * Sparse.eval nodeValue4075 x + ((1 : ℝ) * Sparse.eval nodeValue4077 x + ((2 : ℝ) * Sparse.eval nodeValue4078 x + ((1 : ℝ) * Sparse.eval nodeValue4079 x + ((5 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4090 x + ((1 : ℝ) * Sparse.eval nodeValue4091 x + ((2 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))))))))

def numericRow2012 : Integer.Sparse Master := [(Sum.inr 4063, 1), (Sum.inr 4064, 1), (Sum.inr 4065, 2), (Sum.inr 4069, 1), (Sum.inr 4073, 1), (Sum.inr 4074, 1), (Sum.inr 4075, 2), (Sum.inr 4077, 1), (Sum.inr 4078, 2), (Sum.inr 4079, 1), (Sum.inr 4080, 5), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2), (Sum.inr 4088, 1), (Sum.inr 4090, 1), (Sum.inr 4091, 1), (Sum.inr 4092, 2)]

theorem reindexCheck2012 : Integer.Sparse.reindex keyMap MixedData.row2012 = numericRow2012 := by decide +kernel

theorem numericCheck2012 (x : Master → ℝ) : Integer.Sparse.eval numericRow2012 x =
    (1 : ℝ) * reducedSource2012 x := by
  norm_num [numericRow2012, reducedSource2012, Integer.Sparse.eval, Sparse.eval, nodeValue4063, nodeValue4064, nodeValue4065, nodeValue4069, nodeValue4073, nodeValue4074, nodeValue4075, nodeValue4077, nodeValue4078, nodeValue4079, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4083, nodeValue4084, nodeValue4088, nodeValue4090, nodeValue4091, nodeValue4092]

noncomputable def reducedSource2013 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue3128 x + ((1 : ℝ) * Sparse.eval nodeValue3130 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow2013 : Integer.Sparse Master := [(Sum.inr 3128, 3), (Sum.inr 3130, 1), (Sum.inr 3155, 1), (Sum.inr 3390, 1), (Sum.inr 4083, -1)]

theorem reindexCheck2013 : Integer.Sparse.reindex keyMap MixedData.row2013 = numericRow2013 := by decide +kernel

theorem numericCheck2013 (x : Master → ℝ) : Integer.Sparse.eval numericRow2013 x =
    (1 : ℝ) * reducedSource2013 x := by
  norm_num [numericRow2013, reducedSource2013, Integer.Sparse.eval, Sparse.eval, nodeValue3128, nodeValue3130, nodeValue3155, nodeValue3390, nodeValue4083]

noncomputable def reducedSource2014 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4968 x + ((2 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue5148 x + ((4 : ℝ) * Sparse.eval nodeValue5149 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + 0)))))))))))))

def numericRow2014 : Integer.Sparse Master := [(Sum.inl 0, 489), (Sum.inl 5, -60), (Sum.inl 6, -45), (Sum.inl 2, 280), (Sum.inl 8, 480), (Sum.inl 3, -640), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -480), (Sum.inl 4, -640), (Sum.inl 27, 180), (Sum.inl 1, -140), (Sum.inr 1126, -8640), (Sum.inr 1129, -8640), (Sum.inr 2807, -8640), (Sum.inr 2809, -8640), (Sum.inr 2924, -17280), (Sum.inr 3256, -8640), (Sum.inr 3263, -8640), (Sum.inr 3307, -4320), (Sum.inr 3587, -8640), (Sum.inr 3590, -8640), (Sum.inr 3605, -17280), (Sum.inr 3607, -17280), (Sum.inr 3613, -8640), (Sum.inr 3622, -8640), (Sum.inr 3890, -4320), (Sum.inr 3901, -8640)]

theorem reindexCheck2014 : Integer.Sparse.reindex keyMap MixedData.row2014 = numericRow2014 := by decide +kernel

theorem numericCheck2014 (x : Master → ℝ) : Integer.Sparse.eval numericRow2014 x =
    (17280 : ℝ) * reducedSource2014 x := by
  norm_num [numericRow2014, reducedSource2014, Integer.Sparse.eval, Sparse.eval, nodeValue4541, nodeValue4544, nodeValue4622, nodeValue4968, nodeValue4971, nodeValue5148, nodeValue5149, nodeValue5169, nodeValue5172, nodeValue5292, nodeValue5307, nodeValue5386, nodeValue5433, nodeValue5440]
  ring

noncomputable def reducedSource2015 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4939 x + ((2 : ℝ) * Sparse.eval nodeValue4941 x + ((4 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))

def numericRow2015 : Integer.Sparse Master := [(Sum.inl 0, 504), (Sum.inl 5, -60), (Sum.inl 6, -30), (Sum.inl 2, 110), (Sum.inl 7, 160), (Sum.inl 8, 80), (Sum.inl 3, 160), (Sum.inl 24, 240), (Sum.inl 4, -320), (Sum.inl 27, 180), (Sum.inl 1, 740), (Sum.inl 30, 480), (Sum.inr 919, -8640), (Sum.inr 922, -8640), (Sum.inr 1039, -4320), (Sum.inr 1664, -8640), (Sum.inr 1673, -8640), (Sum.inr 1706, -4320), (Sum.inr 2330, -8640), (Sum.inr 2332, -8640), (Sum.inr 2553, -17280), (Sum.inr 2556, -8640), (Sum.inr 2721, -8640), (Sum.inr 3404, -8640), (Sum.inr 3410, -8640), (Sum.inr 3514, -17280), (Sum.inr 3521, -8640), (Sum.inr 3532, -8640), (Sum.inr 3603, -8640), (Sum.inr 3607, -17280), (Sum.inr 3622, -8640), (Sum.inr 4041, -4320), (Sum.inr 4046, -8640)]

theorem reindexCheck2015 : Integer.Sparse.reindex keyMap MixedData.row2015 = numericRow2015 := by decide +kernel

theorem numericCheck2015 (x : Master → ℝ) : Integer.Sparse.eval numericRow2015 x =
    (17280 : ℝ) * reducedSource2015 x := by
  norm_num [numericRow2015, reducedSource2015, Integer.Sparse.eval, Sparse.eval, nodeValue4341, nodeValue4344, nodeValue4456, nodeValue4939, nodeValue4941, nodeValue5134, nodeValue5137, nodeValue5168, nodeValue5169, nodeValue5257, nodeValue5292, nodeValue5464, nodeValue5482, nodeValue5486]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
