import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
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

noncomputable def reducedSource656 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + 0)))))))))))))))))))

def numericRow656 : Integer.Sparse Master := [(Sum.inl 0, 301), (Sum.inl 2, -110), (Sum.inl 3, -160), (Sum.inl 12, 40), (Sum.inl 1, -395), (Sum.inr 1235, -2160), (Sum.inr 1236, -4320), (Sum.inr 1240, -2160), (Sum.inr 2880, -2160), (Sum.inr 2881, -4320), (Sum.inr 2884, -2160), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3292, -2160), (Sum.inr 3293, -4320), (Sum.inr 3299, -2160), (Sum.inr 3307, -2160), (Sum.inr 3602, -2160), (Sum.inr 3605, -4320), (Sum.inr 3617, -2160), (Sum.inr 3621, -2160), (Sum.inr 3622, -6480), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3627, -4320), (Sum.inr 3632, -4320), (Sum.inr 3901, -2160), (Sum.inr 3910, -2160)]

theorem reindexCheck656 : Integer.Sparse.reindex keyMap MixedData.row656 = numericRow656 := by decide +kernel

theorem numericCheck656 (x : Master → ℝ) : Integer.Sparse.eval numericRow656 x =
    (8640 : ℝ) * reducedSource656 x := by
  norm_num [numericRow656, reducedSource656, Integer.Sparse.eval, Sparse.eval, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4622, nodeValue5148, nodeValue5149, nodeValue5167, nodeValue5202, nodeValue5203, nodeValue5204, nodeValue5283, nodeValue5284, nodeValue5292, nodeValue5293, nodeValue5294, nodeValue5307, nodeValue5433, nodeValue5450, nodeValue5452, nodeValue5454]
  ring

noncomputable def reducedSource657 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1235 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + ((2 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))))))))

def numericRow657 : Integer.Sparse Master := [(Sum.inl 0, -133), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, 160), (Sum.inr 1235, 1080), (Sum.inr 1236, 2160), (Sum.inr 1240, 1080), (Sum.inr 2880, 1080), (Sum.inr 2881, 2160), (Sum.inr 2884, 1080), (Sum.inr 2924, 2160), (Sum.inr 3077, 2160)]

theorem reindexCheck657 : Integer.Sparse.reindex keyMap MixedData.row657 = numericRow657 := by decide +kernel

theorem numericCheck657 (x : Master → ℝ) : Integer.Sparse.eval numericRow657 x =
    (1080 : ℝ) * reducedSource657 x := by
  norm_num [numericRow657, reducedSource657, Integer.Sparse.eval, Sparse.eval, nodeValue1235, nodeValue1236, nodeValue1240, nodeValue1299, nodeValue2880, nodeValue2881, nodeValue2884, nodeValue2924, nodeValue2927, nodeValue2958, nodeValue3076, nodeValue3077, nodeValue3100, nodeValue3101, nodeValue3102, nodeValue3122, nodeValue4029, nodeValue4033, nodeValue4039, nodeValue4040]
  ring

noncomputable def reducedSource658 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

def numericRow658 : Integer.Sparse Master := [(Sum.inl 0, 677), (Sum.inl 2, -165), (Sum.inl 3, -240), (Sum.inl 4, 160), (Sum.inl 1, 90), (Sum.inr 1039, -4320), (Sum.inr 1040, -4320), (Sum.inr 1041, -8640), (Sum.inr 1079, -4320), (Sum.inr 1706, -4320), (Sum.inr 1707, -4320), (Sum.inr 1708, -4320), (Sum.inr 1724, -8640), (Sum.inr 2479, -4320), (Sum.inr 2480, -8640), (Sum.inr 2508, -4320), (Sum.inr 2721, -8640), (Sum.inr 2722, -8640), (Sum.inr 2723, -8640), (Sum.inr 2739, -8640), (Sum.inr 3459, -4320), (Sum.inr 3460, -4320), (Sum.inr 3467, -8640), (Sum.inr 3532, -8640), (Sum.inr 3533, -8640), (Sum.inr 3534, -8640), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -8640), (Sum.inr 3622, -4320), (Sum.inr 3623, -4320), (Sum.inr 3627, -8640), (Sum.inr 4046, -4320)]

theorem reindexCheck658 : Integer.Sparse.reindex keyMap MixedData.row658 = numericRow658 := by decide +kernel

theorem numericCheck658 (x : Master → ℝ) : Integer.Sparse.eval numericRow658 x =
    (17280 : ℝ) * reducedSource658 x := by
  norm_num [numericRow658, reducedSource658, Integer.Sparse.eval, Sparse.eval, nodeValue4456, nodeValue4457, nodeValue4458, nodeValue4495, nodeValue5072, nodeValue5073, nodeValue5098, nodeValue5167, nodeValue5168, nodeValue5169, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5293, nodeValue5306, nodeValue5482, nodeValue5486, nodeValue5490, nodeValue5493]
  ring

noncomputable def reducedSource659 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1039 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

def numericRow659 : Integer.Sparse Master := [(Sum.inl 0, -181), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -80), (Sum.inr 1039, 1440), (Sum.inr 1040, 1440), (Sum.inr 1041, 2880), (Sum.inr 1079, 1440), (Sum.inr 2479, 1440), (Sum.inr 2480, 2880), (Sum.inr 2508, 1440), (Sum.inr 2721, 2880), (Sum.inr 2722, 2880), (Sum.inr 2723, 2880), (Sum.inr 2739, 2880)]

theorem reindexCheck659 : Integer.Sparse.reindex keyMap MixedData.row659 = numericRow659 := by decide +kernel

theorem numericCheck659 (x : Master → ℝ) : Integer.Sparse.eval numericRow659 x =
    (1440 : ℝ) * reducedSource659 x := by
  norm_num [numericRow659, reducedSource659, Integer.Sparse.eval, Sparse.eval, nodeValue1039, nodeValue1040, nodeValue1041, nodeValue1079, nodeValue2479, nodeValue2480, nodeValue2508, nodeValue2593, nodeValue2594, nodeValue2595, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2739, nodeValue2766, nodeValue2767, nodeValue2784, nodeValue3980, nodeValue3999, nodeValue4013, nodeValue4018]
  ring

noncomputable def reducedSource660 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))

def numericRow660 : Integer.Sparse Master := [(Sum.inl 0, 179), (Sum.inl 2, 175), (Sum.inl 3, 80), (Sum.inl 1, 160), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2277, -4320), (Sum.inr 2721, -12960), (Sum.inr 2739, -8640), (Sum.inr 2764, -8640), (Sum.inr 3053, -4320), (Sum.inr 3532, -12960), (Sum.inr 3534, -8640), (Sum.inr 3581, -8640), (Sum.inr 3619, -4320), (Sum.inr 3622, -12960), (Sum.inr 3623, -4320), (Sum.inr 5265, 17280), (Sum.inr 5281, 34560), (Sum.inr 5289, 34560), (Sum.inr 5299, 34560)]

theorem reindexCheck660 : Integer.Sparse.reindex keyMap MixedData.row660 = numericRow660 := by decide +kernel

theorem numericCheck660 (x : Master → ℝ) : Integer.Sparse.eval numericRow660 x =
    (17280 : ℝ) * reducedSource660 x := by
  norm_num [numericRow660, reducedSource660, Integer.Sparse.eval, Sparse.eval, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5256, nodeValue5257, nodeValue5265, nodeValue5271, nodeValue5273, nodeValue5281, nodeValue5283, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5299, nodeValue5301, nodeValue5306, nodeValue5307]
  ring

noncomputable def reducedSource661 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((1 : ℝ) * Sparse.eval nodeValue3628 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow661 : Integer.Sparse Master := [(Sum.inr 3532, 1), (Sum.inr 3534, 2), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

theorem reindexCheck661 : Integer.Sparse.reindex keyMap MixedData.row661 = numericRow661 := by decide +kernel

theorem numericCheck661 (x : Master → ℝ) : Integer.Sparse.eval numericRow661 x =
    (1 : ℝ) * reducedSource661 x := by
  norm_num [numericRow661, reducedSource661, Integer.Sparse.eval, Sparse.eval, nodeValue3532, nodeValue3534, nodeValue3546, nodeValue3622, nodeValue3628, nodeValue4083]

noncomputable def reducedSource662 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3618 x + ((2 : ℝ) * Sparse.eval nodeValue3622 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow662 : Integer.Sparse Master := [(Sum.inr 2243, 1), (Sum.inr 3571, 2), (Sum.inr 3622, 2), (Sum.inr 4083, -1)]

theorem reindexCheck662 : Integer.Sparse.reindex keyMap MixedData.row662 = numericRow662 := by decide +kernel

theorem numericCheck662 (x : Master → ℝ) : Integer.Sparse.eval numericRow662 x =
    (1 : ℝ) * reducedSource662 x := by
  norm_num [numericRow662, reducedSource662, Integer.Sparse.eval, Sparse.eval, nodeValue2243, nodeValue3571, nodeValue3618, nodeValue3622, nodeValue4083]

noncomputable def reducedSource663 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0)))))))))))))))))))))))))))))

def numericRow663 : Integer.Sparse Master := [(Sum.inl 0, -252), (Sum.inl 2, -200), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 180), (Sum.inr 1183, 8640), (Sum.inr 1184, 8640), (Sum.inr 1185, 8640), (Sum.inr 1189, 8640), (Sum.inr 1291, 8640), (Sum.inr 2836, 8640), (Sum.inr 2837, 8640), (Sum.inr 2838, 8640), (Sum.inr 2841, 8640), (Sum.inr 2906, 8640), (Sum.inr 2907, 8640), (Sum.inr 2909, 8640), (Sum.inr 2951, 8640), (Sum.inr 3023, 8640), (Sum.inr 3024, 8640), (Sum.inr 3025, 8640), (Sum.inr 3037, 8640), (Sum.inr 3038, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3052, 8640), (Sum.inr 3055, 8640), (Sum.inr 3097, 8640), (Sum.inr 3535, 8640), (Sum.inr 3809, 8640), (Sum.inr 3839, 8640)]

theorem reindexCheck663 : Integer.Sparse.reindex keyMap MixedData.row663 = numericRow663 := by decide +kernel

theorem numericCheck663 (x : Master → ℝ) : Integer.Sparse.eval numericRow663 x =
    (8640 : ℝ) * reducedSource663 x := by
  norm_num [numericRow663, reducedSource663, Integer.Sparse.eval, Sparse.eval, nodeValue1183, nodeValue1184, nodeValue1185, nodeValue1189, nodeValue1291, nodeValue2836, nodeValue2837, nodeValue2838, nodeValue2841, nodeValue2906, nodeValue2907, nodeValue2909, nodeValue2951, nodeValue3023, nodeValue3024, nodeValue3025, nodeValue3037, nodeValue3038, nodeValue3039, nodeValue3051, nodeValue3052, nodeValue3055, nodeValue3097, nodeValue3109, nodeValue3119, nodeValue3535, nodeValue3809, nodeValue3839, nodeValue3853, nodeValue3862]
  ring

noncomputable def reducedSource664 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2465 x + ((1 : ℝ) * Sparse.eval nodeValue2466 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0)))))))))))))))))))))))))))))

def numericRow664 : Integer.Sparse Master := [(Sum.inl 0, -88), (Sum.inl 2, -60), (Sum.inl 3, -240), (Sum.inl 13, -80), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 180), (Sum.inr 2463, 4320), (Sum.inr 2465, 4320), (Sum.inr 2466, 4320), (Sum.inr 2513, 4320), (Sum.inr 2744, 4320), (Sum.inr 2834, 4320), (Sum.inr 2835, 4320), (Sum.inr 2841, 4320), (Sum.inr 3039, 4320), (Sum.inr 3239, 4320), (Sum.inr 3240, 4320), (Sum.inr 3246, 4320), (Sum.inr 3303, 4320), (Sum.inr 3526, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3541, 4320), (Sum.inr 3558, 4320), (Sum.inr 3559, 4320), (Sum.inr 3561, 4320), (Sum.inr 3567, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3577, 4320), (Sum.inr 3583, 4320), (Sum.inr 3584, 4320), (Sum.inr 3872, 4320)]

theorem reindexCheck664 : Integer.Sparse.reindex keyMap MixedData.row664 = numericRow664 := by decide +kernel

theorem numericCheck664 (x : Master → ℝ) : Integer.Sparse.eval numericRow664 x =
    (4320 : ℝ) * reducedSource664 x := by
  norm_num [numericRow664, reducedSource664, Integer.Sparse.eval, Sparse.eval, nodeValue2463, nodeValue2465, nodeValue2466, nodeValue2513, nodeValue2744, nodeValue2834, nodeValue2835, nodeValue2841, nodeValue3039, nodeValue3239, nodeValue3240, nodeValue3246, nodeValue3303, nodeValue3526, nodeValue3534, nodeValue3535, nodeValue3541, nodeValue3558, nodeValue3559, nodeValue3561, nodeValue3567, nodeValue3572, nodeValue3573, nodeValue3577, nodeValue3583, nodeValue3584, nodeValue3853, nodeValue3872, nodeValue3883, nodeValue3889]
  ring

noncomputable def reducedSource665 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1276 x + ((1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue1278 x + ((1 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow665 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 1277, 1), (Sum.inr 1278, 1), (Sum.inr 1280, 1), (Sum.inr 1291, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem reindexCheck665 : Integer.Sparse.reindex keyMap MixedData.row665 = numericRow665 := by decide +kernel

theorem numericCheck665 (x : Master → ℝ) : Integer.Sparse.eval numericRow665 x =
    (1 : ℝ) * reducedSource665 x := by
  norm_num [numericRow665, reducedSource665, Integer.Sparse.eval, Sparse.eval, nodeValue1276, nodeValue1277, nodeValue1278, nodeValue1280, nodeValue1291, nodeValue2773, nodeValue4092]

noncomputable def reducedSource666 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4469 x + ((1 : ℝ) * Sparse.eval nodeValue4470 x + ((1 : ℝ) * Sparse.eval nodeValue4471 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue5082 x + ((1 : ℝ) * Sparse.eval nodeValue5083 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5091 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow666 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2881, -2160), (Sum.inr 3054, -2160), (Sum.inr 3624, -2160), (Sum.inr 3626, -2160), (Sum.inr 3850, -4320), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4469, 8640), (Sum.inr 4470, 8640), (Sum.inr 4471, 8640), (Sum.inr 4475, 8640), (Sum.inr 4486, 8640), (Sum.inr 5082, 8640), (Sum.inr 5083, 8640), (Sum.inr 5086, 8640), (Sum.inr 5091, 8640), (Sum.inr 5151, 8640), (Sum.inr 5173, 8640), (Sum.inr 5197, 8640), (Sum.inr 5198, 8640), (Sum.inr 5199, 8640), (Sum.inr 5231, 8640), (Sum.inr 5232, 8640), (Sum.inr 5233, 8640), (Sum.inr 5263, 8640), (Sum.inr 5264, 8640), (Sum.inr 5267, 8640), (Sum.inr 5295, 8640), (Sum.inr 5299, 8640), (Sum.inr 5300, 8640), (Sum.inr 5430, 8640)]

theorem reindexCheck666 : Integer.Sparse.reindex keyMap MixedData.row666 = numericRow666 := by decide +kernel

theorem numericCheck666 (x : Master → ℝ) : Integer.Sparse.eval numericRow666 x =
    (8640 : ℝ) * reducedSource666 x := by
  norm_num [numericRow666, reducedSource666, Integer.Sparse.eval, Sparse.eval, nodeValue4469, nodeValue4470, nodeValue4471, nodeValue4475, nodeValue4486, nodeValue5082, nodeValue5083, nodeValue5086, nodeValue5091, nodeValue5151, nodeValue5173, nodeValue5197, nodeValue5198, nodeValue5199, nodeValue5204, nodeValue5231, nodeValue5232, nodeValue5233, nodeValue5263, nodeValue5264, nodeValue5267, nodeValue5295, nodeValue5299, nodeValue5300, nodeValue5302, nodeValue5430, nodeValue5432, nodeValue5438, nodeValue5451, nodeValue5473]
  ring

noncomputable def reducedSource667 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

def numericRow667 : Integer.Sparse Master := [(Sum.inl 0, -232), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -90), (Sum.inl 51, 480), (Sum.inl 3, 160), (Sum.inl 13, 160), (Sum.inl 52, -160), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 100), (Sum.inl 31, 480), (Sum.inr 1052, 8640), (Sum.inr 1053, 8640), (Sum.inr 1054, 8640), (Sum.inr 1058, 8640), (Sum.inr 1070, 8640), (Sum.inr 2490, 8640), (Sum.inr 2491, 8640), (Sum.inr 2494, 8640), (Sum.inr 2500, 8640), (Sum.inr 2631, 8640), (Sum.inr 2632, 8640), (Sum.inr 2633, 8640), (Sum.inr 2676, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2681, 8640), (Sum.inr 2728, 8640), (Sum.inr 2729, 8640), (Sum.inr 2732, 8640), (Sum.inr 2735, 8640), (Sum.inr 2773, 8640), (Sum.inr 2774, 8640), (Sum.inr 2781, 8640), (Sum.inr 3850, 8640), (Sum.inr 3871, 8640), (Sum.inr 3876, 8640)]

theorem reindexCheck667 : Integer.Sparse.reindex keyMap MixedData.row667 = numericRow667 := by decide +kernel

theorem numericCheck667 (x : Master → ℝ) : Integer.Sparse.eval numericRow667 x =
    (8640 : ℝ) * reducedSource667 x := by
  norm_num [numericRow667, reducedSource667, Integer.Sparse.eval, Sparse.eval, nodeValue1052, nodeValue1053, nodeValue1054, nodeValue1058, nodeValue1070, nodeValue2490, nodeValue2491, nodeValue2494, nodeValue2500, nodeValue2631, nodeValue2632, nodeValue2633, nodeValue2638, nodeValue2676, nodeValue2677, nodeValue2678, nodeValue2681, nodeValue2728, nodeValue2729, nodeValue2732, nodeValue2735, nodeValue2773, nodeValue2774, nodeValue2776, nodeValue2781, nodeValue3850, nodeValue3871, nodeValue3876, nodeValue3888, nodeValue3995]
  ring

noncomputable def reducedSource668 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1638 x + ((1 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1640 x + ((1 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3441 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

def numericRow668 : Integer.Sparse Master := [(Sum.inl 0, -80), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -80), (Sum.inl 25, 240), (Sum.inl 26, -160), (Sum.inl 4, -80), (Sum.inl 1, 175), (Sum.inr 1638, 4320), (Sum.inr 1639, 4320), (Sum.inr 1640, 4320), (Sum.inr 1649, 4320), (Sum.inr 1715, 4320), (Sum.inr 2921, 4320), (Sum.inr 2930, 4320), (Sum.inr 2952, 4320), (Sum.inr 3098, 4320), (Sum.inr 3378, 4320), (Sum.inr 3379, 4320), (Sum.inr 3395, 4320), (Sum.inr 3441, 4320), (Sum.inr 3447, 4320), (Sum.inr 3464, 4320), (Sum.inr 3505, 4320), (Sum.inr 3506, 4320), (Sum.inr 3541, 4320), (Sum.inr 3569, 4320), (Sum.inr 3570, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3584, 4320), (Sum.inr 3624, 4320), (Sum.inr 3626, 4320), (Sum.inr 3958, 4320), (Sum.inr 3972, 4320)]

theorem reindexCheck668 : Integer.Sparse.reindex keyMap MixedData.row668 = numericRow668 := by decide +kernel

theorem numericCheck668 (x : Master → ℝ) : Integer.Sparse.eval numericRow668 x =
    (4320 : ℝ) * reducedSource668 x := by
  norm_num [numericRow668, reducedSource668, Integer.Sparse.eval, Sparse.eval, nodeValue1638, nodeValue1639, nodeValue1640, nodeValue1649, nodeValue1715, nodeValue2921, nodeValue2930, nodeValue2952, nodeValue3098, nodeValue3378, nodeValue3379, nodeValue3395, nodeValue3441, nodeValue3447, nodeValue3464, nodeValue3505, nodeValue3506, nodeValue3541, nodeValue3569, nodeValue3570, nodeValue3573, nodeValue3578, nodeValue3584, nodeValue3624, nodeValue3626, nodeValue3958, nodeValue3972, nodeValue3987, nodeValue3993, nodeValue4027]
  ring

noncomputable def reducedSource669 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow669 : Integer.Sparse Master := [(Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 3850, 1), (Sum.inr 3857, 1), (Sum.inr 3913, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem reindexCheck669 : Integer.Sparse.reindex keyMap MixedData.row669 = numericRow669 := by decide +kernel

theorem numericCheck669 (x : Master → ℝ) : Integer.Sparse.eval numericRow669 x =
    (1 : ℝ) * reducedSource669 x := by
  norm_num [numericRow669, reducedSource669, Integer.Sparse.eval, Sparse.eval, nodeValue3051, nodeValue3848, nodeValue3850, nodeValue3857, nodeValue3913, nodeValue3961, nodeValue4092]

noncomputable def reducedSource670 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1364 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow670 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1371, 1), (Sum.inr 1433, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

theorem reindexCheck670 : Integer.Sparse.reindex keyMap MixedData.row670 = numericRow670 := by decide +kernel

theorem numericCheck670 (x : Master → ℝ) : Integer.Sparse.eval numericRow670 x =
    (1 : ℝ) * reducedSource670 x := by
  norm_num [numericRow670, reducedSource670, Integer.Sparse.eval, Sparse.eval, nodeValue1364, nodeValue1367, nodeValue1368, nodeValue1371, nodeValue1433, nodeValue3051, nodeValue4092]

noncomputable def reducedSource671 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1364 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow671 : Integer.Sparse Master := [(Sum.inr 1364, 1), (Sum.inr 2878, 1), (Sum.inr 3036, 1), (Sum.inr 3043, 1), (Sum.inr 3051, 2), (Sum.inr 4092, -1)]

theorem reindexCheck671 : Integer.Sparse.reindex keyMap MixedData.row671 = numericRow671 := by decide +kernel

theorem numericCheck671 (x : Master → ℝ) : Integer.Sparse.eval numericRow671 x =
    (1 : ℝ) * reducedSource671 x := by
  norm_num [numericRow671, reducedSource671, Integer.Sparse.eval, Sparse.eval, nodeValue1364, nodeValue2878, nodeValue3036, nodeValue3043, nodeValue3051, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
