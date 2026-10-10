import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2016 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4540 x + ((3 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((3 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((6 : ℝ) * Sparse.eval nodeValue5145 x + ((3 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + 0))))))))))))

def numericRow2016 : Integer.Sparse Master := [(Sum.inr 1293, -1), (Sum.inr 2556, -3), (Sum.inr 2764, -3), (Sum.inr 3304, -1), (Sum.inr 3521, -3), (Sum.inr 3581, -3), (Sum.inr 3731, -1), (Sum.inr 3849, -3), (Sum.inr 3867, -1), (Sum.inr 3875, -3), (Sum.inr 4540, 4), (Sum.inr 4542, 12), (Sum.inr 4964, 12), (Sum.inr 4975, 4), (Sum.inr 5145, 24), (Sum.inr 5150, 12)]

theorem reindexCheck2016 : Integer.Sparse.reindex keyMap MixedData.row2016 = numericRow2016 := by decide +kernel

theorem numericCheck2016 (x : Master → ℝ) : Integer.Sparse.eval numericRow2016 x =
    (4 : ℝ) * reducedSource2016 x := by
  norm_num [numericRow2016, reducedSource2016, Integer.Sparse.eval, Sparse.eval, nodeValue4540, nodeValue4542, nodeValue4618, nodeValue4964, nodeValue4975, nodeValue5137, nodeValue5145, nodeValue5150, nodeValue5273, nodeValue5290, nodeValue5383, nodeValue5427, nodeValue5431]
  ring

noncomputable def reducedSource2017 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2688 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((3 : ℝ) * Sparse.eval nodeValue2700 x + ((3 : ℝ) * Sparse.eval nodeValue3257 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((3 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((3 : ℝ) * Sparse.eval nodeValue3554 x + ((6 : ℝ) * Sparse.eval nodeValue3562 x + ((3 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((3 : ℝ) * Sparse.eval nodeValue3875 x + 0))))))))))))

def numericRow2017 : Integer.Sparse Master := [(Sum.inr 2688, 1), (Sum.inr 2690, 1), (Sum.inr 2700, 3), (Sum.inr 3257, 3), (Sum.inr 3304, 1), (Sum.inr 3521, 3), (Sum.inr 3554, 3), (Sum.inr 3562, 6), (Sum.inr 3581, 3), (Sum.inr 3867, 1), (Sum.inr 3875, 3)]

theorem reindexCheck2017 : Integer.Sparse.reindex keyMap MixedData.row2017 = numericRow2017 := by decide +kernel

theorem numericCheck2017 (x : Master → ℝ) : Integer.Sparse.eval numericRow2017 x =
    (1 : ℝ) * reducedSource2017 x := by
  norm_num [numericRow2017, reducedSource2017, Integer.Sparse.eval, Sparse.eval, nodeValue2688, nodeValue2690, nodeValue2700, nodeValue3257, nodeValue3304, nodeValue3521, nodeValue3546, nodeValue3554, nodeValue3562, nodeValue3581, nodeValue3844, nodeValue3867, nodeValue3875]

noncomputable def reducedSource2018 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((3 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((3 : ℝ) * Sparse.eval nodeValue5123 x + ((6 : ℝ) * Sparse.eval nodeValue5163 x + ((3 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))

def numericRow2018 : Integer.Sparse Master := [(Sum.inl 0, 86), (Sum.inl 6, -5), (Sum.inl 2, 45), (Sum.inl 7, 80), (Sum.inl 3, 240), (Sum.inl 4, 160), (Sum.inl 1, -120), (Sum.inr 915, -4320), (Sum.inr 929, -1440), (Sum.inr 1034, -1440), (Sum.inr 1632, -4320), (Sum.inr 1644, -1440), (Sum.inr 1680, -1440), (Sum.inr 2328, -4320), (Sum.inr 2338, -1440), (Sum.inr 2536, -4320), (Sum.inr 2590, -8640), (Sum.inr 2671, -1440), (Sum.inr 2764, -4320), (Sum.inr 3370, -4320), (Sum.inr 3390, -1440), (Sum.inr 3401, -4320), (Sum.inr 3416, -1440), (Sum.inr 3564, -8640), (Sum.inr 3581, -4320), (Sum.inr 3613, -4320), (Sum.inr 3909, -1440), (Sum.inr 4010, -4320), (Sum.inr 4025, -1440)]

theorem reindexCheck2018 : Integer.Sparse.reindex keyMap MixedData.row2018 = numericRow2018 := by decide +kernel

theorem numericCheck2018 (x : Master → ℝ) : Integer.Sparse.eval numericRow2018 x =
    (5760 : ℝ) * reducedSource2018 x := by
  norm_num [numericRow2018, reducedSource2018, Integer.Sparse.eval, Sparse.eval, nodeValue4337, nodeValue4351, nodeValue4451, nodeValue4936, nodeValue4947, nodeValue5123, nodeValue5163, nodeValue5172, nodeValue5227, nodeValue5290, nodeValue5447, nodeValue5462, nodeValue5485]
  ring

noncomputable def reducedSource2019 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4364 x + ((2 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4696 x + ((2 : ℝ) * Sparse.eval nodeValue4698 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((4 : ℝ) * Sparse.eval nodeValue4852 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + 0)))))))))))))

def numericRow2019 : Integer.Sparse Master := [(Sum.inr 1039, -1), (Sum.inr 1706, -1), (Sum.inr 2107, -4), (Sum.inr 2110, -2), (Sum.inr 2243, -4), (Sum.inr 2260, -4), (Sum.inr 2275, -2), (Sum.inr 2764, -2), (Sum.inr 3581, -2), (Sum.inr 4364, 8), (Sum.inr 4366, 8), (Sum.inr 4696, 8), (Sum.inr 4698, 8), (Sum.inr 4851, 8), (Sum.inr 4852, 16), (Sum.inr 5278, 4), (Sum.inr 5281, 8)]

theorem reindexCheck2019 : Integer.Sparse.reindex keyMap MixedData.row2019 = numericRow2019 := by decide +kernel

theorem numericCheck2019 (x : Master → ℝ) : Integer.Sparse.eval numericRow2019 x =
    (4 : ℝ) * reducedSource2019 x := by
  norm_num [numericRow2019, reducedSource2019, Integer.Sparse.eval, Sparse.eval, nodeValue4364, nodeValue4366, nodeValue4456, nodeValue4696, nodeValue4698, nodeValue4851, nodeValue4852, nodeValue4866, nodeValue4869, nodeValue4887, nodeValue4893, nodeValue5278, nodeValue5281, nodeValue5290]
  ring

noncomputable def reducedSource2020 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1711 x + ((2 : ℝ) * Sparse.eval nodeValue2238 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2248 x + ((4 : ℝ) * Sparse.eval nodeValue2250 x + ((4 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + 0)))))))))))))

def numericRow2020 : Integer.Sparse Master := [(Sum.inr 1703, 2), (Sum.inr 1706, 1), (Sum.inr 1711, 2), (Sum.inr 2238, 2), (Sum.inr 2240, 2), (Sum.inr 2243, 2), (Sum.inr 2248, 2), (Sum.inr 2250, 4), (Sum.inr 2260, 4), (Sum.inr 2275, 2), (Sum.inr 2747, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 2)]

theorem reindexCheck2020 : Integer.Sparse.reindex keyMap MixedData.row2020 = numericRow2020 := by decide +kernel

theorem numericCheck2020 (x : Master → ℝ) : Integer.Sparse.eval numericRow2020 x =
    (1 : ℝ) * reducedSource2020 x := by
  norm_num [numericRow2020, reducedSource2020, Integer.Sparse.eval, Sparse.eval, nodeValue1703, nodeValue1706, nodeValue1711, nodeValue2238, nodeValue2240, nodeValue2243, nodeValue2248, nodeValue2250, nodeValue2260, nodeValue2263, nodeValue2275, nodeValue2747, nodeValue2750, nodeValue2764]

noncomputable def reducedSource2021 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4230 x + ((2 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4676 x + ((2 : ℝ) * Sparse.eval nodeValue4679 x + ((4 : ℝ) * Sparse.eval nodeValue4798 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4826 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0)))))))))))))

def numericRow2021 : Integer.Sparse Master := [(Sum.inl 0, 106), (Sum.inl 5, -60), (Sum.inl 2, 20), (Sum.inl 7, -240), (Sum.inl 3, -320), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 27, 180), (Sum.inl 1, -190), (Sum.inr 730, -8640), (Sum.inr 732, -8640), (Sum.inr 780, -8640), (Sum.inr 786, -4320), (Sum.inr 798, -8640), (Sum.inr 822, -4320), (Sum.inr 1802, -8640), (Sum.inr 1805, -8640), (Sum.inr 2016, -17280), (Sum.inr 2023, -8640), (Sum.inr 2046, -8640), (Sum.inr 2075, -17280), (Sum.inr 2077, -8640), (Sum.inr 2106, -8640), (Sum.inr 2107, -17280), (Sum.inr 2141, -8640), (Sum.inr 2150, -8640), (Sum.inr 2214, -8640), (Sum.inr 2242, -8640), (Sum.inr 2245, -8640), (Sum.inr 2260, -17280), (Sum.inr 2277, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3890, -4320), (Sum.inr 3910, -8640)]

theorem reindexCheck2021 : Integer.Sparse.reindex keyMap MixedData.row2021 = numericRow2021 := by decide +kernel

theorem numericCheck2021 (x : Master → ℝ) : Integer.Sparse.eval numericRow2021 x =
    (17280 : ℝ) * reducedSource2021 x := by
  norm_num [numericRow2021, reducedSource2021, Integer.Sparse.eval, Sparse.eval, nodeValue4230, nodeValue4232, nodeValue4252, nodeValue4676, nodeValue4679, nodeValue4798, nodeValue4805, nodeValue4826, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue5386, nodeValue5431, nodeValue5450]
  ring

noncomputable def reducedSource2022 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4441 x + ((2 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4833 x + ((4 : ℝ) * Sparse.eval nodeValue4849 x + ((2 : ℝ) * Sparse.eval nodeValue4854 x + ((2 : ℝ) * Sparse.eval nodeValue4859 x + ((2 : ℝ) * Sparse.eval nodeValue4863 x + ((4 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5202 x + 0)))))))))))))

def numericRow2022 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 6, 15), (Sum.inl 2, -110), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, -70), (Sum.inr 1034, -8640), (Sum.inr 1644, -8640), (Sum.inr 2051, -8640), (Sum.inr 2100, -17280), (Sum.inr 2105, -17280), (Sum.inr 2191, -8640), (Sum.inr 2241, -17280), (Sum.inr 2880, -8640), (Sum.inr 3602, -4320), (Sum.inr 3617, -8640), (Sum.inr 4436, 34560), (Sum.inr 4441, 17280), (Sum.inr 4849, 69120), (Sum.inr 4854, 34560), (Sum.inr 4863, 34560), (Sum.inr 4878, 34560), (Sum.inr 5197, 34560)]

theorem reindexCheck2022 : Integer.Sparse.reindex keyMap MixedData.row2022 = numericRow2022 := by decide +kernel

theorem numericCheck2022 (x : Master → ℝ) : Integer.Sparse.eval numericRow2022 x =
    (17280 : ℝ) * reducedSource2022 x := by
  norm_num [numericRow2022, reducedSource2022, Integer.Sparse.eval, Sparse.eval, nodeValue4436, nodeValue4441, nodeValue4451, nodeValue4831, nodeValue4833, nodeValue4849, nodeValue4854, nodeValue4859, nodeValue4863, nodeValue4864, nodeValue4878, nodeValue5167, nodeValue5197, nodeValue5202]
  ring

noncomputable def reducedSource2023 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4677 x + ((2 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + 0))))))))))))))))))))

def numericRow2023 : Integer.Sparse Master := [(Sum.inr 919, -1), (Sum.inr 1079, -1), (Sum.inr 1664, -1), (Sum.inr 1708, -1), (Sum.inr 1802, -1), (Sum.inr 2019, -1), (Sum.inr 2054, -2), (Sum.inr 2058, -2), (Sum.inr 2141, -1), (Sum.inr 2190, -1), (Sum.inr 2206, -2), (Sum.inr 2216, -2), (Sum.inr 2244, -1), (Sum.inr 2245, -1), (Sum.inr 2262, -1), (Sum.inr 2277, -1), (Sum.inr 2723, -2), (Sum.inr 3544, -2), (Sum.inr 4345, 8), (Sum.inr 4677, 4), (Sum.inr 4680, 8), (Sum.inr 4803, 8), (Sum.inr 4815, 4), (Sum.inr 4816, 8), (Sum.inr 5220, 4), (Sum.inr 5251, 4)]

theorem reindexCheck2023 : Integer.Sparse.reindex keyMap MixedData.row2023 = numericRow2023 := by decide +kernel

theorem numericCheck2023 (x : Master → ℝ) : Integer.Sparse.eval numericRow2023 x =
    (4 : ℝ) * reducedSource2023 x := by
  norm_num [numericRow2023, reducedSource2023, Integer.Sparse.eval, Sparse.eval, nodeValue4341, nodeValue4342, nodeValue4345, nodeValue4495, nodeValue4676, nodeValue4677, nodeValue4680, nodeValue4801, nodeValue4803, nodeValue4815, nodeValue4816, nodeValue4834, nodeValue4835, nodeValue4839, nodeValue4888, nodeValue4889, nodeValue4895, nodeValue5220, nodeValue5250, nodeValue5251, nodeValue5259]
  ring

noncomputable def reducedSource2024 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1664 x + ((1 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue2141 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((2 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + 0))))))))))))))))))))

def numericRow2024 : Integer.Sparse Master := [(Sum.inr 1664, 1), (Sum.inr 1668, 2), (Sum.inr 1708, 1), (Sum.inr 2141, 1), (Sum.inr 2142, 1), (Sum.inr 2145, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 2195, 2), (Sum.inr 2196, 2), (Sum.inr 2206, 2), (Sum.inr 2216, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2662, 1), (Sum.inr 2710, 1), (Sum.inr 2723, 2)]

theorem reindexCheck2024 : Integer.Sparse.reindex keyMap MixedData.row2024 = numericRow2024 := by decide +kernel

theorem numericCheck2024 (x : Master → ℝ) : Integer.Sparse.eval numericRow2024 x =
    (1 : ℝ) * reducedSource2024 x := by
  norm_num [numericRow2024, reducedSource2024, Integer.Sparse.eval, Sparse.eval, nodeValue1664, nodeValue1665, nodeValue1668, nodeValue1708, nodeValue2141, nodeValue2142, nodeValue2145, nodeValue2190, nodeValue2192, nodeValue2195, nodeValue2196, nodeValue2205, nodeValue2206, nodeValue2216, nodeValue2244, nodeValue2245, nodeValue2265, nodeValue2662, nodeValue2709, nodeValue2710, nodeValue2723]

noncomputable def reducedSource2025 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4063 x + ((1 : ℝ) * Sparse.eval nodeValue4068 x + ((4 : ℝ) * Sparse.eval nodeValue4073 x + ((12 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow2025 : Integer.Sparse Master := [(Sum.inr 4063, 4), (Sum.inr 4068, 1), (Sum.inr 4073, 4), (Sum.inr 4080, 12), (Sum.inr 4083, 4), (Sum.inr 4087, 1), (Sum.inr 4091, 4)]

theorem reindexCheck2025 : Integer.Sparse.reindex keyMap MixedData.row2025 = numericRow2025 := by decide +kernel

theorem numericCheck2025 (x : Master → ℝ) : Integer.Sparse.eval numericRow2025 x =
    (1 : ℝ) * reducedSource2025 x := by
  norm_num [numericRow2025, reducedSource2025, Integer.Sparse.eval, Sparse.eval, nodeValue4063, nodeValue4068, nodeValue4073, nodeValue4080, nodeValue4083, nodeValue4087, nodeValue4091]

noncomputable def reducedSource2026 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue3131 x + ((1 : ℝ) * Sparse.eval nodeValue3365 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow2026 : Integer.Sparse Master := [(Sum.inr 1814, 1), (Sum.inr 3131, 1), (Sum.inr 3365, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

theorem reindexCheck2026 : Integer.Sparse.reindex keyMap MixedData.row2026 = numericRow2026 := by decide +kernel

theorem numericCheck2026 (x : Master → ℝ) : Integer.Sparse.eval numericRow2026 x =
    (1 : ℝ) * reducedSource2026 x := by
  norm_num [numericRow2026, reducedSource2026, Integer.Sparse.eval, Sparse.eval, nodeValue1814, nodeValue3131, nodeValue3365, nodeValue3379, nodeValue3391, nodeValue3395, nodeValue4084]

noncomputable def reducedSource2027 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue3032 x + ((1 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2027 : Integer.Sparse Master := [(Sum.inr 2362, 1), (Sum.inr 3032, 1), (Sum.inr 3033, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2027 : Integer.Sparse.reindex keyMap MixedData.row2027 = numericRow2027 := by decide +kernel

theorem numericCheck2027 (x : Master → ℝ) : Integer.Sparse.eval numericRow2027 x =
    (1 : ℝ) * reducedSource2027 x := by
  norm_num [numericRow2027, reducedSource2027, Integer.Sparse.eval, Sparse.eval, nodeValue2362, nodeValue3032, nodeValue3033, nodeValue3040, nodeValue3045, nodeValue3732, nodeValue4092]

noncomputable def reducedSource2028 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue3673 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2028 : Integer.Sparse Master := [(Sum.inr 2343, 1), (Sum.inr 2819, 1), (Sum.inr 3673, 1), (Sum.inr 3699, 1), (Sum.inr 3705, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2028 : Integer.Sparse.reindex keyMap MixedData.row2028 = numericRow2028 := by decide +kernel

theorem numericCheck2028 (x : Master → ℝ) : Integer.Sparse.eval numericRow2028 x =
    (1 : ℝ) * reducedSource2028 x := by
  norm_num [numericRow2028, reducedSource2028, Integer.Sparse.eval, Sparse.eval, nodeValue2343, nodeValue2819, nodeValue3673, nodeValue3699, nodeValue3705, nodeValue3706, nodeValue4092]

noncomputable def reducedSource2029 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue3676 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow2029 : Integer.Sparse Master := [(Sum.inr 2324, 1), (Sum.inr 2801, 1), (Sum.inr 3676, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

theorem reindexCheck2029 : Integer.Sparse.reindex keyMap MixedData.row2029 = numericRow2029 := by decide +kernel

theorem numericCheck2029 (x : Master → ℝ) : Integer.Sparse.eval numericRow2029 x =
    (1 : ℝ) * reducedSource2029 x := by
  norm_num [numericRow2029, reducedSource2029, Integer.Sparse.eval, Sparse.eval, nodeValue2324, nodeValue2801, nodeValue3676, nodeValue3685, nodeValue3690, nodeValue3692, nodeValue4091]

noncomputable def reducedSource2030 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3708 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2030 : Integer.Sparse Master := [(Sum.inr 2350, 1), (Sum.inr 3134, 1), (Sum.inr 3708, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3722, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2030 : Integer.Sparse.reindex keyMap MixedData.row2030 = numericRow2030 := by decide +kernel

theorem numericCheck2030 (x : Master → ℝ) : Integer.Sparse.eval numericRow2030 x =
    (1 : ℝ) * reducedSource2030 x := by
  norm_num [numericRow2030, reducedSource2030, Integer.Sparse.eval, Sparse.eval, nodeValue2350, nodeValue3134, nodeValue3708, nodeValue3715, nodeValue3719, nodeValue3722, nodeValue4092]

noncomputable def reducedSource2031 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue3709 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow2031 : Integer.Sparse Master := [(Sum.inr 2824, 2), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3779, 1), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

theorem reindexCheck2031 : Integer.Sparse.reindex keyMap MixedData.row2031 = numericRow2031 := by decide +kernel

theorem numericCheck2031 (x : Master → ℝ) : Integer.Sparse.eval numericRow2031 x =
    (1 : ℝ) * reducedSource2031 x := by
  norm_num [numericRow2031, reducedSource2031, Integer.Sparse.eval, Sparse.eval, nodeValue2824, nodeValue3709, nodeValue3716, nodeValue3779, nodeValue3922, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
