import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
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

noncomputable def reducedSource2096 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4090 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((2 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4960 x + ((2 : ℝ) * Sparse.eval nodeValue4961 x + ((1 : ℝ) * Sparse.eval nodeValue4969 x + ((1 : ℝ) * Sparse.eval nodeValue5029 x + ((2 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5058 x + ((1 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5332 x + ((2 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5392 x + ((2 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + 0))))))))))))))))))))

def numericRow2096 : Integer.Sparse Master := [(Sum.inr 2317, -1), (Sum.inr 2318, -2), (Sum.inr 2328, -1), (Sum.inr 2412, -1), (Sum.inr 2452, -2), (Sum.inr 2796, -2), (Sum.inr 2804, -1), (Sum.inr 2853, -1), (Sum.inr 3399, -1), (Sum.inr 3400, -2), (Sum.inr 3401, -1), (Sum.inr 3426, -1), (Sum.inr 3433, -2), (Sum.inr 3586, -1), (Sum.inr 3589, -2), (Sum.inr 3620, -1), (Sum.inr 3678, -2), (Sum.inr 3683, -2), (Sum.inr 3687, -2), (Sum.inr 3701, -1), (Sum.inr 3744, -2), (Sum.inr 3746, -2), (Sum.inr 3749, -2), (Sum.inr 3751, -1), (Sum.inr 3781, -2), (Sum.inr 3794, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 4090, 4)]

theorem reindexCheck2096 : Integer.Sparse.reindex keyMap MixedData.row2096 = numericRow2096 := by decide +kernel

theorem numericCheck2096 (x : Master → ℝ) : Integer.Sparse.eval numericRow2096 x =
    (4 : ℝ) * reducedSource2096 x := by
  norm_num [numericRow2096, reducedSource2096, Integer.Sparse.eval, Sparse.eval, nodeValue4090, nodeValue4927, nodeValue4928, nodeValue4936, nodeValue4960, nodeValue4961, nodeValue4969, nodeValue5029, nodeValue5050, nodeValue5058, nodeValue5192, nodeValue5332, nodeValue5341, nodeValue5346, nodeValue5349, nodeValue5363, nodeValue5392, nodeValue5394, nodeValue5395, nodeValue5396, nodeValue5469]; ring

noncomputable def reducedSource2097 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((2 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue5017 x + ((1 : ℝ) * Sparse.eval nodeValue5025 x + ((1 : ℝ) * Sparse.eval nodeValue5030 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((2 : ℝ) * Sparse.eval nodeValue5314 x + ((2 : ℝ) * Sparse.eval nodeValue5333 x + ((2 : ℝ) * Sparse.eval nodeValue5344 x + ((1 : ℝ) * Sparse.eval nodeValue5345 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5391 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + 0))))))))))))))))))))

def numericRow2097 : Integer.Sparse Master := [(Sum.inr 2371, -1), (Sum.inr 2372, -2), (Sum.inr 2419, -1), (Sum.inr 2459, -2), (Sum.inr 2536, -1), (Sum.inr 3335, -1), (Sum.inr 3336, -2), (Sum.inr 3370, -1), (Sum.inr 3425, -1), (Sum.inr 3429, -2), (Sum.inr 3668, -2), (Sum.inr 3677, -2), (Sum.inr 3681, -4), (Sum.inr 3683, -2), (Sum.inr 3713, -2), (Sum.inr 3719, -2), (Sum.inr 3721, -1), (Sum.inr 3746, -2), (Sum.inr 3776, -1), (Sum.inr 3778, -1), (Sum.inr 3779, -2), (Sum.inr 3795, -2), (Sum.inr 3797, -2), (Sum.inr 3836, -1), (Sum.inr 4088, 4)]

theorem reindexCheck2097 : Integer.Sparse.reindex keyMap MixedData.row2097 = numericRow2097 := by decide +kernel

theorem numericCheck2097 (x : Master → ℝ) : Integer.Sparse.eval numericRow2097 x =
    (4 : ℝ) * reducedSource2097 x := by
  norm_num [numericRow2097, reducedSource2097, Integer.Sparse.eval, Sparse.eval, nodeValue4088, nodeValue4986, nodeValue4987, nodeValue5017, nodeValue5025, nodeValue5030, nodeValue5056, nodeValue5123, nodeValue5314, nodeValue5333, nodeValue5344, nodeValue5345, nodeValue5346, nodeValue5367, nodeValue5369, nodeValue5374, nodeValue5378, nodeValue5380, nodeValue5391, nodeValue5393, nodeValue5460]; ring

noncomputable def reducedSource2098 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4073 x + ((2 : ℝ) * Sparse.eval nodeValue4074 x + ((4 : ℝ) * Sparse.eval nodeValue4075 x + ((1 : ℝ) * Sparse.eval nodeValue4078 x + ((2 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4086 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((2 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4090 x + ((2 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

def numericRow2098 : Integer.Sparse Master := [(Sum.inr 4073, 2), (Sum.inr 4074, 2), (Sum.inr 4075, 4), (Sum.inr 4078, 1), (Sum.inr 4080, 2), (Sum.inr 4082, 2), (Sum.inr 4086, 2), (Sum.inr 4087, 1), (Sum.inr 4088, 4), (Sum.inr 4089, 2), (Sum.inr 4090, 2), (Sum.inr 4091, 2), (Sum.inr 4092, 4)]

theorem reindexCheck2098 : Integer.Sparse.reindex keyMap MixedData.row2098 = numericRow2098 := by decide +kernel

theorem numericCheck2098 (x : Master → ℝ) : Integer.Sparse.eval numericRow2098 x =
    (1 : ℝ) * reducedSource2098 x := by
  norm_num [numericRow2098, reducedSource2098, Integer.Sparse.eval, Sparse.eval, nodeValue4073, nodeValue4074, nodeValue4075, nodeValue4078, nodeValue4080, nodeValue4082, nodeValue4086, nodeValue4087, nodeValue4088, nodeValue4089, nodeValue4090, nodeValue4091, nodeValue4092]

noncomputable def reducedSource2099 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4672 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4859 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((3 : ℝ) * Sparse.eval nodeValue4969 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((3 : ℝ) * Sparse.eval nodeValue5374 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((6 : ℝ) * Sparse.eval nodeValue5384 x + ((3 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((3 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5448 x + 0))))))))))))

def numericRow2099 : Integer.Sparse Master := [(Sum.inl 0, 189), (Sum.inl 5, 60), (Sum.inl 2, -45), (Sum.inl 7, 240), (Sum.inl 3, 720), (Sum.inl 23, -720), (Sum.inl 12, 480), (Sum.inl 27, -180), (Sum.inl 1, 930), (Sum.inr 1798, -12960), (Sum.inr 1811, -4320), (Sum.inr 2067, -12960), (Sum.inr 2100, -8640), (Sum.inr 2156, -4320), (Sum.inr 2804, -12960), (Sum.inr 2814, -4320), (Sum.inr 3585, -4320), (Sum.inr 3586, -12960), (Sum.inr 3713, -25920), (Sum.inr 3731, -4320), (Sum.inr 3732, -25920), (Sum.inr 3811, -25920), (Sum.inr 3867, -4320), (Sum.inr 3885, -25920), (Sum.inr 3891, -12960), (Sum.inr 3899, -8640), (Sum.inr 3902, -12960)]

theorem reindexCheck2099 : Integer.Sparse.reindex keyMap MixedData.row2099 = numericRow2099 := by decide +kernel

theorem numericCheck2099 (x : Master → ℝ) : Integer.Sparse.eval numericRow2099 x =
    (17280 : ℝ) * reducedSource2099 x := by
  norm_num [numericRow2099, reducedSource2099, Integer.Sparse.eval, Sparse.eval, nodeValue4672, nodeValue4685, nodeValue4859, nodeValue4967, nodeValue4969, nodeValue5166, nodeValue5374, nodeValue5383, nodeValue5384, nodeValue5387, nodeValue5437, nodeValue5439, nodeValue5448]; ring

noncomputable def reducedSource2100 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4675 x + ((3 : ℝ) * Sparse.eval nodeValue4677 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((3 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5243 x + ((6 : ℝ) * Sparse.eval nodeValue5379 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + 0))))))))))))

def numericRow2100 : Integer.Sparse Master := [(Sum.inr 2589, -1), (Sum.inr 3563, -1), (Sum.inr 3721, -3), (Sum.inr 3836, -3), (Sum.inr 3849, -3), (Sum.inr 3875, -3), (Sum.inr 3909, -1), (Sum.inr 4025, -1), (Sum.inr 4675, 4), (Sum.inr 4677, 12), (Sum.inr 4863, 4), (Sum.inr 4964, 12), (Sum.inr 4975, 4), (Sum.inr 5243, 12), (Sum.inr 5379, 24), (Sum.inr 5429, 12)]

theorem reindexCheck2100 : Integer.Sparse.reindex keyMap MixedData.row2100 = numericRow2100 := by decide +kernel

theorem numericCheck2100 (x : Master → ℝ) : Integer.Sparse.eval numericRow2100 x =
    (4 : ℝ) * reducedSource2100 x := by
  norm_num [numericRow2100, reducedSource2100, Integer.Sparse.eval, Sparse.eval, nodeValue4675, nodeValue4677, nodeValue4863, nodeValue4964, nodeValue4975, nodeValue5162, nodeValue5243, nodeValue5379, nodeValue5380, nodeValue5427, nodeValue5429, nodeValue5431, nodeValue5447]; ring

noncomputable def reducedSource2101 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2139 x + ((3 : ℝ) * Sparse.eval nodeValue2142 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((3 : ℝ) * Sparse.eval nodeValue2697 x + ((3 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((6 : ℝ) * Sparse.eval nodeValue3832 x + ((3 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((3 : ℝ) * Sparse.eval nodeValue3846 x + ((3 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))

def numericRow2101 : Integer.Sparse Master := [(Sum.inr 2139, 1), (Sum.inr 2142, 3), (Sum.inr 2232, 1), (Sum.inr 2690, 1), (Sum.inr 2697, 3), (Sum.inr 3554, 3), (Sum.inr 3563, 1), (Sum.inr 3832, 6), (Sum.inr 3836, 3), (Sum.inr 3846, 3), (Sum.inr 3875, 3), (Sum.inr 3909, 1)]

theorem reindexCheck2101 : Integer.Sparse.reindex keyMap MixedData.row2101 = numericRow2101 := by decide +kernel

theorem numericCheck2101 (x : Master → ℝ) : Integer.Sparse.eval numericRow2101 x =
    (1 : ℝ) * reducedSource2101 x := by
  norm_num [numericRow2101, reducedSource2101, Integer.Sparse.eval, Sparse.eval, nodeValue2139, nodeValue2142, nodeValue2232, nodeValue2690, nodeValue2697, nodeValue3554, nodeValue3563, nodeValue3832, nodeValue3836, nodeValue3844, nodeValue3846, nodeValue3875, nodeValue3909]

noncomputable def reducedSource2102 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4676 x + ((2 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4968 x + ((2 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((4 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0)))))))))))))

def numericRow2102 : Integer.Sparse Master := [(Sum.inl 0, 391), (Sum.inl 5, 120), (Sum.inl 6, 15), (Sum.inl 2, -280), (Sum.inl 7, 400), (Sum.inl 8, -160), (Sum.inl 3, 640), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 4, 320), (Sum.inl 27, -360), (Sum.inl 1, -270), (Sum.inr 1802, -8640), (Sum.inr 1805, -8640), (Sum.inr 2105, -4320), (Sum.inr 2141, -8640), (Sum.inr 2150, -8640), (Sum.inr 2241, -4320), (Sum.inr 2807, -8640), (Sum.inr 2809, -8640), (Sum.inr 3587, -8640), (Sum.inr 3590, -8640), (Sum.inr 3602, -4320), (Sum.inr 3719, -17280), (Sum.inr 3721, -8640), (Sum.inr 3795, -17280), (Sum.inr 3836, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3891, -8640), (Sum.inr 3892, -17280), (Sum.inr 3901, -8640), (Sum.inr 3910, -8640)]

theorem reindexCheck2102 : Integer.Sparse.reindex keyMap MixedData.row2102 = numericRow2102 := by decide +kernel

theorem numericCheck2102 (x : Master → ℝ) : Integer.Sparse.eval numericRow2102 x =
    (17280 : ℝ) * reducedSource2102 x := by
  norm_num [numericRow2102, reducedSource2102, Integer.Sparse.eval, Sparse.eval, nodeValue4676, nodeValue4679, nodeValue4864, nodeValue4968, nodeValue4971, nodeValue5167, nodeValue5378, nodeValue5380, nodeValue5387, nodeValue5388, nodeValue5431, nodeValue5433, nodeValue5440, nodeValue5450]; ring

noncomputable def reducedSource2103 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4695 x + ((3 : ℝ) * Sparse.eval nodeValue4696 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((6 : ℝ) * Sparse.eval nodeValue5226 x + ((3 : ℝ) * Sparse.eval nodeValue5231 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))

def numericRow2103 : Integer.Sparse Master := [(Sum.inr 1805, -3), (Sum.inr 1811, -1), (Sum.inr 2150, -3), (Sum.inr 2156, -1), (Sum.inr 2684, -3), (Sum.inr 2721, -3), (Sum.inr 3053, -1), (Sum.inr 3394, -3), (Sum.inr 3532, -3), (Sum.inr 3619, -1), (Sum.inr 4695, 4), (Sum.inr 4696, 12), (Sum.inr 4878, 4), (Sum.inr 5226, 24), (Sum.inr 5231, 12), (Sum.inr 5265, 12)]

theorem reindexCheck2103 : Integer.Sparse.reindex keyMap MixedData.row2103 = numericRow2103 := by decide +kernel

theorem numericCheck2103 (x : Master → ℝ) : Integer.Sparse.eval numericRow2103 x =
    (4 : ℝ) * reducedSource2103 x := by
  norm_num [numericRow2103, reducedSource2103, Integer.Sparse.eval, Sparse.eval, nodeValue4679, nodeValue4685, nodeValue4695, nodeValue4696, nodeValue4833, nodeValue4878, nodeValue5226, nodeValue5231, nodeValue5237, nodeValue5257, nodeValue5265, nodeValue5273, nodeValue5301]; ring

noncomputable def reducedSource2104 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2150 x + ((1 : ℝ) * Sparse.eval nodeValue2156 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((1 : ℝ) * Sparse.eval nodeValue2231 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((3 : ℝ) * Sparse.eval nodeValue2238 x + ((6 : ℝ) * Sparse.eval nodeValue2669 x + ((3 : ℝ) * Sparse.eval nodeValue2676 x + ((3 : ℝ) * Sparse.eval nodeValue2684 x + ((3 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + 0))))))))))))

def numericRow2104 : Integer.Sparse Master := [(Sum.inr 2150, 3), (Sum.inr 2156, 1), (Sum.inr 2231, 1), (Sum.inr 2234, 1), (Sum.inr 2238, 3), (Sum.inr 2669, 6), (Sum.inr 2676, 3), (Sum.inr 2684, 3), (Sum.inr 2721, 3), (Sum.inr 3037, 3), (Sum.inr 3053, 1)]

theorem reindexCheck2104 : Integer.Sparse.reindex keyMap MixedData.row2104 = numericRow2104 := by decide +kernel

theorem numericCheck2104 (x : Master → ℝ) : Integer.Sparse.eval numericRow2104 x =
    (1 : ℝ) * reducedSource2104 x := by
  norm_num [numericRow2104, reducedSource2104, Integer.Sparse.eval, Sparse.eval, nodeValue2150, nodeValue2156, nodeValue2204, nodeValue2231, nodeValue2234, nodeValue2238, nodeValue2669, nodeValue2676, nodeValue2684, nodeValue2721, nodeValue2741, nodeValue3037, nodeValue3053]

noncomputable def reducedSource2105 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4939 x + ((4 : ℝ) * Sparse.eval nodeValue4941 x + ((2 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5460 x + ((4 : ℝ) * Sparse.eval nodeValue5465 x + ((4 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))

def numericRow2105 : Integer.Sparse Master := [(Sum.inl 0, 319), (Sum.inl 5, 60), (Sum.inl 6, 15), (Sum.inl 2, -220), (Sum.inl 7, -80), (Sum.inl 8, 80), (Sum.inl 3, -320), (Sum.inl 24, -240), (Sum.inl 4, -320), (Sum.inl 27, -180), (Sum.inl 1, 430), (Sum.inl 30, -480), (Sum.inr 2330, -8640), (Sum.inr 2332, -8640), (Sum.inr 3404, -8640), (Sum.inr 3410, -8640), (Sum.inr 3602, -4320), (Sum.inr 3779, -8640), (Sum.inr 3797, -8640), (Sum.inr 3898, -4320), (Sum.inr 4042, -8640), (Sum.inr 4046, -8640)]

theorem reindexCheck2105 : Integer.Sparse.reindex keyMap MixedData.row2105 = numericRow2105 := by decide +kernel

theorem numericCheck2105 (x : Master → ℝ) : Integer.Sparse.eval numericRow2105 x =
    (8640 : ℝ) * reducedSource2105 x := by
  norm_num [numericRow2105, reducedSource2105, Integer.Sparse.eval, Sparse.eval, nodeValue4939, nodeValue4941, nodeValue5167, nodeValue5393, nodeValue5418, nodeValue5460, nodeValue5465, nodeValue5482, nodeValue5486]; ring

noncomputable def reducedSource2106 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4073 x + ((2 : ℝ) * Sparse.eval nodeValue4079 x + ((12 : ℝ) * Sparse.eval nodeValue4088 x + ((8 : ℝ) * Sparse.eval nodeValue4091 x + 0)))

def numericRow2106 : Integer.Sparse Master := [(Sum.inr 4073, 8), (Sum.inr 4079, 2), (Sum.inr 4088, 12), (Sum.inr 4091, 8)]

theorem reindexCheck2106 : Integer.Sparse.reindex keyMap MixedData.row2106 = numericRow2106 := by decide +kernel

theorem numericCheck2106 (x : Master → ℝ) : Integer.Sparse.eval numericRow2106 x =
    (1 : ℝ) * reducedSource2106 x := by
  norm_num [numericRow2106, reducedSource2106, Integer.Sparse.eval, Sparse.eval, nodeValue4073, nodeValue4079, nodeValue4088, nodeValue4091]

noncomputable def reducedSource2107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5113 x + ((4 : ℝ) * Sparse.eval nodeValue5114 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5372 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((4 : ℝ) * Sparse.eval nodeValue5403 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + 0))))))))

def numericRow2107 : Integer.Sparse Master := [(Sum.inl 0, 303), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, -60), (Sum.inl 7, 480), (Sum.inl 3, 960), (Sum.inl 23, -720), (Sum.inl 12, 480), (Sum.inl 27, -180), (Sum.inl 1, 1500), (Sum.inr 2896, -12960), (Sum.inr 3597, -12960), (Sum.inr 3603, -12960), (Sum.inr 3708, -12960), (Sum.inr 3789, -12960), (Sum.inr 3791, -12960), (Sum.inr 3810, -12960), (Sum.inr 3891, -12960), (Sum.inr 3902, -12960)]

theorem reindexCheck2107 : Integer.Sparse.reindex keyMap MixedData.row2107 = numericRow2107 := by decide +kernel

theorem numericCheck2107 (x : Master → ℝ) : Integer.Sparse.eval numericRow2107 x =
    (12960 : ℝ) * reducedSource2107 x := by
  norm_num [numericRow2107, reducedSource2107, Integer.Sparse.eval, Sparse.eval, nodeValue5113, nodeValue5114, nodeValue5168, nodeValue5372, nodeValue5387, nodeValue5403, nodeValue5439, nodeValue5441, nodeValue5488]; ring

noncomputable def reducedSource2108 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4759 x + ((4 : ℝ) * Sparse.eval nodeValue4763 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((4 : ℝ) * Sparse.eval nodeValue5335 x + ((4 : ℝ) * Sparse.eval nodeValue5351 x + ((4 : ℝ) * Sparse.eval nodeValue5416 x + ((4 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + 0))))))))

def numericRow2108 : Integer.Sparse Master := [(Sum.inl 0, 225), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -270), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -1440), (Sum.inl 24, 720), (Sum.inl 12, -480), (Sum.inl 4, -960), (Sum.inl 27, 180), (Sum.inl 1, 210), (Sum.inr 1959, -3240), (Sum.inr 1963, -12960), (Sum.inr 2019, -12960), (Sum.inr 2170, -3240), (Sum.inr 2174, -12960), (Sum.inr 2190, -12960), (Sum.inr 3670, -12960), (Sum.inr 3689, -12960), (Sum.inr 3753, -12960), (Sum.inr 3757, -12960), (Sum.inr 3837, -25920), (Sum.inr 3896, -12960), (Sum.inr 3901, -12960)]

theorem reindexCheck2108 : Integer.Sparse.reindex keyMap MixedData.row2108 = numericRow2108 := by decide +kernel

theorem numericCheck2108 (x : Master → ℝ) : Integer.Sparse.eval numericRow2108 x =
    (12960 : ℝ) * reducedSource2108 x := by
  norm_num [numericRow2108, reducedSource2108, Integer.Sparse.eval, Sparse.eval, nodeValue4759, nodeValue4763, nodeValue4801, nodeValue5335, nodeValue5351, nodeValue5416, nodeValue5423, nodeValue5433, nodeValue5497]; ring

noncomputable def reducedSource2109 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4761 x + ((1 : ℝ) * Sparse.eval nodeValue4762 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((2 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((2 : ℝ) * Sparse.eval nodeValue5338 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

def numericRow2109 : Integer.Sparse Master := [(Sum.inr 2483, -1), (Sum.inr 3477, -1), (Sum.inr 3692, -1), (Sum.inr 3769, -1), (Sum.inr 3787, -2), (Sum.inr 3801, -2), (Sum.inr 3804, -2), (Sum.inr 3812, -2), (Sum.inr 3849, -1), (Sum.inr 3875, -1), (Sum.inr 4761, 4), (Sum.inr 4762, 4), (Sum.inr 4768, 4), (Sum.inr 4803, 8), (Sum.inr 5044, 8), (Sum.inr 5187, 4), (Sum.inr 5215, 8), (Sum.inr 5219, 4), (Sum.inr 5249, 4), (Sum.inr 5338, 8), (Sum.inr 5353, 8), (Sum.inr 5414, 4), (Sum.inr 5425, 8), (Sum.inr 5430, 8)]

theorem reindexCheck2109 : Integer.Sparse.reindex keyMap MixedData.row2109 = numericRow2109 := by decide +kernel

theorem numericCheck2109 (x : Master → ℝ) : Integer.Sparse.eval numericRow2109 x =
    (4 : ℝ) * reducedSource2109 x := by
  norm_num [numericRow2109, reducedSource2109, Integer.Sparse.eval, Sparse.eval, nodeValue4761, nodeValue4762, nodeValue4768, nodeValue4803, nodeValue5044, nodeValue5076, nodeValue5187, nodeValue5215, nodeValue5219, nodeValue5249, nodeValue5338, nodeValue5353, nodeValue5354, nodeValue5401, nodeValue5406, nodeValue5408, nodeValue5414, nodeValue5425, nodeValue5430, nodeValue5431, nodeValue5481]; ring

noncomputable def reducedSource2110 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2171 x + ((1 : ℝ) * Sparse.eval nodeValue2175 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((2 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3755 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + 0))))))))))))))))))))

def numericRow2110 : Integer.Sparse Master := [(Sum.inr 2171, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2195, 2), (Sum.inr 2653, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 3474, 2), (Sum.inr 3477, 1), (Sum.inr 3537, 1), (Sum.inr 3755, 2), (Sum.inr 3761, 2), (Sum.inr 3769, 1), (Sum.inr 3804, 2), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2)]

theorem reindexCheck2110 : Integer.Sparse.reindex keyMap MixedData.row2110 = numericRow2110 := by decide +kernel

theorem numericCheck2110 (x : Master → ℝ) : Integer.Sparse.eval numericRow2110 x =
    (1 : ℝ) * reducedSource2110 x := by
  norm_num [numericRow2110, reducedSource2110, Integer.Sparse.eval, Sparse.eval, nodeValue2171, nodeValue2175, nodeValue2178, nodeValue2195, nodeValue2653, nodeValue2661, nodeValue2708, nodeValue3474, nodeValue3477, nodeValue3537, nodeValue3755, nodeValue3761, nodeValue3769, nodeValue3804, nodeValue3806, nodeValue3812, nodeValue3840, nodeValue3849, nodeValue3869, nodeValue3871, nodeValue3979]

noncomputable def reducedSource2111 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4077 x + ((4 : ℝ) * Sparse.eval nodeValue4078 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4086 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((4 : ℝ) * Sparse.eval nodeValue4090 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4095 x + 0))))))))

def numericRow2111 : Integer.Sparse Master := [(Sum.inr 4077, 1), (Sum.inr 4078, 4), (Sum.inr 4080, 4), (Sum.inr 4086, 4), (Sum.inr 4088, 4), (Sum.inr 4090, 4), (Sum.inr 4091, 4), (Sum.inr 4092, 4)]

theorem reindexCheck2111 : Integer.Sparse.reindex keyMap MixedData.row2111 = numericRow2111 := by decide +kernel

theorem numericCheck2111 (x : Master → ℝ) : Integer.Sparse.eval numericRow2111 x =
    (1 : ℝ) * reducedSource2111 x := by
  norm_num [numericRow2111, reducedSource2111, Integer.Sparse.eval, Sparse.eval, nodeValue4077, nodeValue4078, nodeValue4080, nodeValue4086, nodeValue4088, nodeValue4090, nodeValue4091, nodeValue4092, nodeValue4095]

end MUB6.Certificate.MixedSourceBridge

end OAI
