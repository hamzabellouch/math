import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
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

noncomputable def reducedSource2064 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5216 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5339 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + 0)))))))))))))))))))))))))))))

def numericRow2064 : Integer.Sparse Master := [(Sum.inr 2488, -1), (Sum.inr 2590, -1), (Sum.inr 3478, -1), (Sum.inr 3564, -1), (Sum.inr 3693, -1), (Sum.inr 3719, -1), (Sum.inr 3770, -1), (Sum.inr 3786, -1), (Sum.inr 3795, -1), (Sum.inr 3799, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3850, -2), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 4680, 4), (Sum.inr 4682, 4), (Sum.inr 4683, 4), (Sum.inr 4690, 4), (Sum.inr 4867, 4), (Sum.inr 4963, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 4976, 4), (Sum.inr 5042, 4), (Sum.inr 5188, 4), (Sum.inr 5216, 4), (Sum.inr 5232, 4), (Sum.inr 5264, 4), (Sum.inr 5339, 4), (Sum.inr 5381, 4), (Sum.inr 5382, 4), (Sum.inr 5385, 4), (Sum.inr 5402, 4), (Sum.inr 5436, 4), (Sum.inr 5446, 4)]

theorem reindexCheck2064 : Integer.Sparse.reindex keyMap MixedData.row2064 = numericRow2064 := by decide +kernel

theorem numericCheck2064 (x : Master → ℝ) : Integer.Sparse.eval numericRow2064 x =
    (4 : ℝ) * reducedSource2064 x := by
  norm_num [numericRow2064, reducedSource2064, Integer.Sparse.eval, Sparse.eval, nodeValue4680, nodeValue4682, nodeValue4683, nodeValue4690, nodeValue4867, nodeValue4963, nodeValue4965, nodeValue4966, nodeValue4976, nodeValue5042, nodeValue5080, nodeValue5163, nodeValue5188, nodeValue5216, nodeValue5232, nodeValue5264, nodeValue5339, nodeValue5355, nodeValue5378, nodeValue5381, nodeValue5382, nodeValue5385, nodeValue5400, nodeValue5402, nodeValue5409, nodeValue5411, nodeValue5432, nodeValue5436, nodeValue5438, nodeValue5446]
  ring

noncomputable def reducedSource2065 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2654 x + ((1 : ℝ) * Sparse.eval nodeValue2659 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3760 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + 0)))))))))))))))))))))))))))))

def numericRow2065 : Integer.Sparse Master := [(Sum.inr 2145, 1), (Sum.inr 2146, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2251, 1), (Sum.inr 2654, 1), (Sum.inr 2659, 1), (Sum.inr 2677, 1), (Sum.inr 2729, 1), (Sum.inr 3462, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3564, 1), (Sum.inr 3760, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3799, 1), (Sum.inr 3802, 1), (Sum.inr 3813, 1), (Sum.inr 3834, 1), (Sum.inr 3850, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1)]

theorem reindexCheck2065 : Integer.Sparse.reindex keyMap MixedData.row2065 = numericRow2065 := by decide +kernel

theorem numericCheck2065 (x : Master → ℝ) : Integer.Sparse.eval numericRow2065 x =
    (1 : ℝ) * reducedSource2065 x := by
  norm_num [numericRow2065, reducedSource2065, Integer.Sparse.eval, Sparse.eval, nodeValue2145, nodeValue2146, nodeValue2153, nodeValue2158, nodeValue2251, nodeValue2654, nodeValue2659, nodeValue2677, nodeValue2729, nodeValue3462, nodeValue3475, nodeValue3478, nodeValue3538, nodeValue3553, nodeValue3555, nodeValue3564, nodeValue3760, nodeValue3770, nodeValue3795, nodeValue3799, nodeValue3802, nodeValue3807, nodeValue3813, nodeValue3834, nodeValue3850, nodeValue3854, nodeValue3866, nodeValue3868, nodeValue3876, nodeValue3881]

noncomputable def reducedSource2066 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4660 x + ((2 : ℝ) * Sparse.eval nodeValue4661 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4960 x + ((2 : ℝ) * Sparse.eval nodeValue4961 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue5030 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5333 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + 0))))))))))))))))))))

def numericRow2066 : Integer.Sparse Master := [(Sum.inl 0, 723), (Sum.inl 5, -60), (Sum.inl 2, 75), (Sum.inl 7, -240), (Sum.inl 3, -1200), (Sum.inl 23, 720), (Sum.inl 12, -960), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, -540), (Sum.inr 1786, -12960), (Sum.inr 1787, -25920), (Sum.inr 1805, -12960), (Sum.inr 1982, -12960), (Sum.inr 1983, -25920), (Sum.inr 2046, -12960), (Sum.inr 2077, -12960), (Sum.inr 2150, -12960), (Sum.inr 2412, -12960), (Sum.inr 2419, -12960), (Sum.inr 2488, -25920), (Sum.inr 2796, -25920), (Sum.inr 2809, -12960), (Sum.inr 3425, -12960), (Sum.inr 3426, -12960), (Sum.inr 3478, -25920), (Sum.inr 3587, -12960), (Sum.inr 3589, -25920), (Sum.inr 3668, -25920), (Sum.inr 3677, -25920), (Sum.inr 3693, -25920), (Sum.inr 3701, -12960), (Sum.inr 3719, -25920), (Sum.inr 3751, -12960), (Sum.inr 3770, -25920), (Sum.inr 3795, -25920), (Sum.inr 3849, -12960), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3890, -12960), (Sum.inr 3892, -25920), (Sum.inr 3900, -12960), (Sum.inr 3901, -12960), (Sum.inr 3903, -25920), (Sum.inr 3964, -12960)]

theorem reindexCheck2066 : Integer.Sparse.reindex keyMap MixedData.row2066 = numericRow2066 := by decide +kernel

theorem numericCheck2066 (x : Master → ℝ) : Integer.Sparse.eval numericRow2066 x =
    (51840 : ℝ) * reducedSource2066 x := by
  norm_num [numericRow2066, reducedSource2066, Integer.Sparse.eval, Sparse.eval, nodeValue4660, nodeValue4661, nodeValue4679, nodeValue4826, nodeValue4960, nodeValue4961, nodeValue4968, nodeValue5030, nodeValue5080, nodeValue5148, nodeValue5333, nodeValue5355, nodeValue5363, nodeValue5378, nodeValue5386, nodeValue5388, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5438]
  ring

noncomputable def reducedSource2067 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4663 x + ((2 : ℝ) * Sparse.eval nodeValue4666 x + ((1 : ℝ) * Sparse.eval nodeValue4677 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((2 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + 0))))))))))))))))))))

def numericRow2067 : Integer.Sparse Master := [(Sum.inr 2556, -1), (Sum.inr 2896, -1), (Sum.inr 3521, -1), (Sum.inr 3597, -1), (Sum.inr 3709, -2), (Sum.inr 3721, -2), (Sum.inr 3731, -1), (Sum.inr 3792, -2), (Sum.inr 3836, -2), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 3867, -1), (Sum.inr 3900, -1), (Sum.inr 3909, -1), (Sum.inr 3964, -1), (Sum.inr 4025, -1), (Sum.inr 4663, 4), (Sum.inr 4666, 8), (Sum.inr 4677, 4), (Sum.inr 4851, 4), (Sum.inr 4956, 4), (Sum.inr 4958, 8), (Sum.inr 4964, 4), (Sum.inr 5129, 8), (Sum.inr 5377, 8), (Sum.inr 5379, 8), (Sum.inr 5430, 8)]

theorem reindexCheck2067 : Integer.Sparse.reindex keyMap MixedData.row2067 = numericRow2067 := by decide +kernel

theorem numericCheck2067 (x : Master → ℝ) : Integer.Sparse.eval numericRow2067 x =
    (4 : ℝ) * reducedSource2067 x := by
  norm_num [numericRow2067, reducedSource2067, Integer.Sparse.eval, Sparse.eval, nodeValue4663, nodeValue4666, nodeValue4677, nodeValue4851, nodeValue4956, nodeValue4958, nodeValue4964, nodeValue5114, nodeValue5129, nodeValue5137, nodeValue5373, nodeValue5377, nodeValue5379, nodeValue5380, nodeValue5383, nodeValue5396, nodeValue5422, nodeValue5424, nodeValue5427, nodeValue5430, nodeValue5447]
  ring

noncomputable def reducedSource2068 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((2 : ℝ) * Sparse.eval nodeValue2148 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3511 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3597 x + ((2 : ℝ) * Sparse.eval nodeValue3792 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3835 x + ((2 : ℝ) * Sparse.eval nodeValue3836 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))))))))))

def numericRow2068 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2142, 1), (Sum.inr 2148, 2), (Sum.inr 2240, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3516, 2), (Sum.inr 3521, 1), (Sum.inr 3554, 1), (Sum.inr 3597, 1), (Sum.inr 3792, 2), (Sum.inr 3832, 2), (Sum.inr 3835, 2), (Sum.inr 3836, 2), (Sum.inr 3843, 2), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3900, 1), (Sum.inr 3909, 1)]

theorem reindexCheck2068 : Integer.Sparse.reindex keyMap MixedData.row2068 = numericRow2068 := by decide +kernel

theorem numericCheck2068 (x : Master → ℝ) : Integer.Sparse.eval numericRow2068 x =
    (1 : ℝ) * reducedSource2068 x := by
  norm_num [numericRow2068, reducedSource2068, Integer.Sparse.eval, Sparse.eval, nodeValue2140, nodeValue2142, nodeValue2148, nodeValue2240, nodeValue3510, nodeValue3511, nodeValue3516, nodeValue3521, nodeValue3554, nodeValue3597, nodeValue3792, nodeValue3798, nodeValue3832, nodeValue3835, nodeValue3836, nodeValue3843, nodeValue3844, nodeValue3848, nodeValue3867, nodeValue3900, nodeValue3909]

noncomputable def reducedSource2069 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4665 x + ((1 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5372 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + 0))))))))))))))))))))))))))))

def numericRow2069 : Integer.Sparse Master := [(Sum.inr 2431, -1), (Sum.inr 2488, -1), (Sum.inr 2553, -1), (Sum.inr 3453, -1), (Sum.inr 3478, -1), (Sum.inr 3514, -1), (Sum.inr 3671, -1), (Sum.inr 3693, -1), (Sum.inr 3708, -1), (Sum.inr 3732, -1), (Sum.inr 3754, -1), (Sum.inr 3770, -1), (Sum.inr 3782, -1), (Sum.inr 3791, -1), (Sum.inr 3796, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 3837, -2), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 4664, 4), (Sum.inr 4665, 4), (Sum.inr 4668, 4), (Sum.inr 4680, 4), (Sum.inr 4852, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4963, 4), (Sum.inr 5129, 4), (Sum.inr 5376, 4), (Sum.inr 5379, 4), (Sum.inr 5381, 8), (Sum.inr 5382, 4), (Sum.inr 5425, 4), (Sum.inr 5445, 4)]

theorem reindexCheck2069 : Integer.Sparse.reindex keyMap MixedData.row2069 = numericRow2069 := by decide +kernel

theorem numericCheck2069 (x : Master → ℝ) : Integer.Sparse.eval numericRow2069 x =
    (4 : ℝ) * reducedSource2069 x := by
  norm_num [numericRow2069, reducedSource2069, Integer.Sparse.eval, Sparse.eval, nodeValue4664, nodeValue4665, nodeValue4668, nodeValue4680, nodeValue4852, nodeValue4954, nodeValue4955, nodeValue4957, nodeValue4963, nodeValue5038, nodeValue5080, nodeValue5129, nodeValue5134, nodeValue5336, nodeValue5355, nodeValue5372, nodeValue5376, nodeValue5379, nodeValue5381, nodeValue5382, nodeValue5384, nodeValue5394, nodeValue5397, nodeValue5409, nodeValue5411, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5445]
  ring

noncomputable def reducedSource2070 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3791 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + 0))))))))))))))))))))))))))))

def numericRow2070 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2145, 1), (Sum.inr 2147, 1), (Sum.inr 2154, 1), (Sum.inr 2250, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3553, 1), (Sum.inr 3754, 1), (Sum.inr 3770, 1), (Sum.inr 3791, 1), (Sum.inr 3796, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3880, 1)]

theorem reindexCheck2070 : Integer.Sparse.reindex keyMap MixedData.row2070 = numericRow2070 := by decide +kernel

theorem numericCheck2070 (x : Master → ℝ) : Integer.Sparse.eval numericRow2070 x =
    (1 : ℝ) * reducedSource2070 x := by
  norm_num [numericRow2070, reducedSource2070, Integer.Sparse.eval, Sparse.eval, nodeValue2144, nodeValue2145, nodeValue2147, nodeValue2154, nodeValue2250, nodeValue3452, nodeValue3453, nodeValue3478, nodeValue3508, nodeValue3509, nodeValue3514, nodeValue3516, nodeValue3553, nodeValue3754, nodeValue3770, nodeValue3791, nodeValue3793, nodeValue3796, nodeValue3807, nodeValue3811, nodeValue3813, nodeValue3832, nodeValue3833, nodeValue3834, nodeValue3837, nodeValue3838, nodeValue3840, nodeValue3866, nodeValue3880]

noncomputable def reducedSource2071 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4696 x + ((1 : ℝ) * Sparse.eval nodeValue4697 x + ((2 : ℝ) * Sparse.eval nodeValue4701 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue5116 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5217 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((2 : ℝ) * Sparse.eval nodeValue5236 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))))

def numericRow2071 : Integer.Sparse Master := [(Sum.inr 1805, -1), (Sum.inr 1812, -1), (Sum.inr 1815, -2), (Sum.inr 2150, -1), (Sum.inr 2165, -1), (Sum.inr 2166, -2), (Sum.inr 2671, -1), (Sum.inr 2684, -2), (Sum.inr 2703, -1), (Sum.inr 2739, -2), (Sum.inr 3053, -1), (Sum.inr 3390, -1), (Sum.inr 3394, -2), (Sum.inr 3496, -1), (Sum.inr 3534, -2), (Sum.inr 3619, -1), (Sum.inr 4696, 4), (Sum.inr 4697, 4), (Sum.inr 4701, 8), (Sum.inr 4879, 4), (Sum.inr 5116, 4), (Sum.inr 5151, 8), (Sum.inr 5217, 8), (Sum.inr 5226, 8), (Sum.inr 5236, 8), (Sum.inr 5286, 4), (Sum.inr 5299, 8)]

theorem reindexCheck2071 : Integer.Sparse.reindex keyMap MixedData.row2071 = numericRow2071 := by decide +kernel

theorem numericCheck2071 (x : Master → ℝ) : Integer.Sparse.eval numericRow2071 x =
    (4 : ℝ) * reducedSource2071 x := by
  norm_num [numericRow2071, reducedSource2071, Integer.Sparse.eval, Sparse.eval, nodeValue4679, nodeValue4686, nodeValue4689, nodeValue4696, nodeValue4697, nodeValue4701, nodeValue4838, nodeValue4879, nodeValue5116, nodeValue5151, nodeValue5217, nodeValue5226, nodeValue5227, nodeValue5236, nodeValue5237, nodeValue5247, nodeValue5271, nodeValue5273, nodeValue5286, nodeValue5299, nodeValue5301]
  ring

noncomputable def reducedSource2072 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2150 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((2 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2238 x + ((1 : ℝ) * Sparse.eval nodeValue2239 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((2 : ℝ) * Sparse.eval nodeValue2257 x + ((1 : ℝ) * Sparse.eval nodeValue2655 x + ((2 : ℝ) * Sparse.eval nodeValue2656 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((2 : ℝ) * Sparse.eval nodeValue2682 x + ((2 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + 0))))))))))))))))))))

def numericRow2072 : Integer.Sparse Master := [(Sum.inr 2150, 1), (Sum.inr 2165, 1), (Sum.inr 2166, 2), (Sum.inr 2238, 1), (Sum.inr 2239, 1), (Sum.inr 2246, 1), (Sum.inr 2257, 2), (Sum.inr 2655, 1), (Sum.inr 2656, 2), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2681, 2), (Sum.inr 2682, 2), (Sum.inr 2684, 2), (Sum.inr 2703, 1), (Sum.inr 2739, 2), (Sum.inr 3023, 1), (Sum.inr 3051, 2), (Sum.inr 3053, 1)]

theorem reindexCheck2072 : Integer.Sparse.reindex keyMap MixedData.row2072 = numericRow2072 := by decide +kernel

theorem numericCheck2072 (x : Master → ℝ) : Integer.Sparse.eval numericRow2072 x =
    (1 : ℝ) * reducedSource2072 x := by
  norm_num [numericRow2072, reducedSource2072, Integer.Sparse.eval, Sparse.eval, nodeValue2150, nodeValue2165, nodeValue2166, nodeValue2227, nodeValue2238, nodeValue2239, nodeValue2246, nodeValue2257, nodeValue2655, nodeValue2656, nodeValue2669, nodeValue2671, nodeValue2681, nodeValue2682, nodeValue2684, nodeValue2703, nodeValue2739, nodeValue2741, nodeValue3023, nodeValue3051, nodeValue3053]

noncomputable def reducedSource2073 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4698 x + ((1 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4700 x + ((1 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue5035 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5215 x + ((1 : ℝ) * Sparse.eval nodeValue5216 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))))))))))))

def numericRow2073 : Integer.Sparse Master := [(Sum.inr 1802, -1), (Sum.inr 1807, -1), (Sum.inr 1810, -1), (Sum.inr 1814, -1), (Sum.inr 2141, -1), (Sum.inr 2151, -1), (Sum.inr 2152, -1), (Sum.inr 2157, -1), (Sum.inr 2522, -1), (Sum.inr 2672, -1), (Sum.inr 2685, -1), (Sum.inr 2686, -1), (Sum.inr 2694, -1), (Sum.inr 2722, -1), (Sum.inr 2723, -1), (Sum.inr 3054, -1), (Sum.inr 3391, -1), (Sum.inr 3397, -1), (Sum.inr 3493, -1), (Sum.inr 3533, -1), (Sum.inr 3544, -1), (Sum.inr 3626, -1), (Sum.inr 4698, 4), (Sum.inr 4699, 4), (Sum.inr 4700, 4), (Sum.inr 4703, 4), (Sum.inr 4880, 4), (Sum.inr 5035, 4), (Sum.inr 5140, 4), (Sum.inr 5215, 4), (Sum.inr 5216, 4), (Sum.inr 5219, 4), (Sum.inr 5220, 4), (Sum.inr 5229, 4), (Sum.inr 5232, 4), (Sum.inr 5233, 4), (Sum.inr 5254, 4), (Sum.inr 5266, 4), (Sum.inr 5267, 4)]

theorem reindexCheck2073 : Integer.Sparse.reindex keyMap MixedData.row2073 = numericRow2073 := by decide +kernel

theorem numericCheck2073 (x : Master → ℝ) : Integer.Sparse.eval numericRow2073 x =
    (4 : ℝ) * reducedSource2073 x := by
  norm_num [numericRow2073, reducedSource2073, Integer.Sparse.eval, Sparse.eval, nodeValue4676, nodeValue4681, nodeValue4684, nodeValue4688, nodeValue4698, nodeValue4699, nodeValue4700, nodeValue4703, nodeValue4834, nodeValue4880, nodeValue5035, nodeValue5110, nodeValue5140, nodeValue5215, nodeValue5216, nodeValue5219, nodeValue5220, nodeValue5228, nodeValue5229, nodeValue5232, nodeValue5233, nodeValue5238, nodeValue5241, nodeValue5254, nodeValue5258, nodeValue5259, nodeValue5266, nodeValue5267, nodeValue5274, nodeValue5302]
  ring

noncomputable def reducedSource2074 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2141 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2248 x + ((1 : ℝ) * Sparse.eval nodeValue2249 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue2652 x + ((1 : ℝ) * Sparse.eval nodeValue2653 x + ((1 : ℝ) * Sparse.eval nodeValue2654 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + 0)))))))))))))))))))))))))))))

def numericRow2074 : Integer.Sparse Master := [(Sum.inr 2141, 1), (Sum.inr 2151, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2248, 1), (Sum.inr 2249, 1), (Sum.inr 2254, 1), (Sum.inr 2256, 1), (Sum.inr 2272, 1), (Sum.inr 2652, 1), (Sum.inr 2653, 1), (Sum.inr 2654, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2694, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 3016, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3054, 1)]

theorem reindexCheck2074 : Integer.Sparse.reindex keyMap MixedData.row2074 = numericRow2074 := by decide +kernel

theorem numericCheck2074 (x : Master → ℝ) : Integer.Sparse.eval numericRow2074 x =
    (1 : ℝ) * reducedSource2074 x := by
  norm_num [numericRow2074, reducedSource2074, Integer.Sparse.eval, Sparse.eval, nodeValue2141, nodeValue2151, nodeValue2152, nodeValue2157, nodeValue2205, nodeValue2248, nodeValue2249, nodeValue2254, nodeValue2256, nodeValue2272, nodeValue2652, nodeValue2653, nodeValue2654, nodeValue2661, nodeValue2662, nodeValue2670, nodeValue2672, nodeValue2673, nodeValue2677, nodeValue2678, nodeValue2685, nodeValue2686, nodeValue2694, nodeValue2722, nodeValue2723, nodeValue2742, nodeValue3016, nodeValue3038, nodeValue3039, nodeValue3054]

noncomputable def reducedSource2075 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4947 x + ((2 : ℝ) * Sparse.eval nodeValue4948 x + ((4 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5115 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((2 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((4 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))

def numericRow2075 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 5, -30), (Sum.inl 8, -120), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -210), (Sum.inr 2338, -3240), (Sum.inr 2339, -3240), (Sum.inr 2341, -6480), (Sum.inr 3416, -3240), (Sum.inr 3417, -6480), (Sum.inr 3420, -3240), (Sum.inr 3613, -3240), (Sum.inr 3616, -3240), (Sum.inr 3709, -3240), (Sum.inr 3790, -3240), (Sum.inr 3792, -3240), (Sum.inr 3815, -3240), (Sum.inr 3894, -3240), (Sum.inr 3896, -3240), (Sum.inr 3898, -3240), (Sum.inr 4010, -3240)]

theorem reindexCheck2075 : Integer.Sparse.reindex keyMap MixedData.row2075 = numericRow2075 := by decide +kernel

theorem numericCheck2075 (x : Master → ℝ) : Integer.Sparse.eval numericRow2075 x =
    (6480 : ℝ) * reducedSource2075 x := by
  norm_num [numericRow2075, reducedSource2075, Integer.Sparse.eval, Sparse.eval, nodeValue4947, nodeValue4948, nodeValue4949, nodeValue5115, nodeValue5172, nodeValue5177, nodeValue5373, nodeValue5390, nodeValue5404, nodeValue5416, nodeValue5418, nodeValue5442, nodeValue5462, nodeValue5485]
  ring

noncomputable def reducedSource2076 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4939 x + ((4 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5337 x + ((2 : ℝ) * Sparse.eval nodeValue5356 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((4 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))

def numericRow2076 : Integer.Sparse Master := [(Sum.inl 0, 54), (Sum.inl 5, -6), (Sum.inl 8, -24), (Sum.inl 24, 72), (Sum.inl 27, 18), (Sum.inl 1, 30), (Sum.inr 1967, -432), (Sum.inr 1969, -864), (Sum.inr 2029, -864), (Sum.inr 2183, -432), (Sum.inr 2185, -864), (Sum.inr 2225, -864), (Sum.inr 2330, -864), (Sum.inr 2337, -1728), (Sum.inr 3404, -864), (Sum.inr 3412, -1728), (Sum.inr 3603, -864), (Sum.inr 3672, -864), (Sum.inr 3694, -864), (Sum.inr 3756, -864), (Sum.inr 3773, -864), (Sum.inr 3779, -864), (Sum.inr 3797, -864), (Sum.inr 3896, -864), (Sum.inr 3903, -1728), (Sum.inr 4041, -432), (Sum.inr 4042, -864)]

theorem reindexCheck2076 : Integer.Sparse.reindex keyMap MixedData.row2076 = numericRow2076 := by decide +kernel

theorem numericCheck2076 (x : Master → ℝ) : Integer.Sparse.eval numericRow2076 x =
    (1728 : ℝ) * reducedSource2076 x := by
  norm_num [numericRow2076, reducedSource2076, Integer.Sparse.eval, Sparse.eval, nodeValue4767, nodeValue4769, nodeValue4811, nodeValue4939, nodeValue4946, nodeValue5168, nodeValue5337, nodeValue5356, nodeValue5393, nodeValue5416, nodeValue5434, nodeValue5464, nodeValue5465, nodeValue5486]
  ring

noncomputable def reducedSource2077 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4941 x + ((2 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((1 : ℝ) * Sparse.eval nodeValue5457 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))

def numericRow2077 : Integer.Sparse Master := [(Sum.inl 0, 984), (Sum.inl 5, -120), (Sum.inl 8, -480), (Sum.inl 27, 360), (Sum.inl 1, 120), (Sum.inl 30, 1440), (Sum.inr 2332, -12960), (Sum.inr 2334, -12960), (Sum.inr 2337, -12960), (Sum.inr 2342, -12960), (Sum.inr 2432, -6480), (Sum.inr 2489, -6480), (Sum.inr 3410, -12960), (Sum.inr 3411, -12960), (Sum.inr 3412, -12960), (Sum.inr 3421, -12960), (Sum.inr 3456, -6480), (Sum.inr 3482, -6480), (Sum.inr 3607, -12960), (Sum.inr 3616, -6480), (Sum.inr 3672, -6480), (Sum.inr 3694, -6480), (Sum.inr 3756, -6480), (Sum.inr 3773, -6480), (Sum.inr 3898, -6480), (Sum.inr 4041, -6480), (Sum.inr 4042, -12960), (Sum.inr 4043, -6480), (Sum.inr 4045, -12960), (Sum.inr 4047, -12960)]

theorem reindexCheck2077 : Integer.Sparse.reindex keyMap MixedData.row2077 = numericRow2077 := by decide +kernel

theorem numericCheck2077 (x : Master → ℝ) : Integer.Sparse.eval numericRow2077 x =
    (25920 : ℝ) * reducedSource2077 x := by
  norm_num [numericRow2077, reducedSource2077, Integer.Sparse.eval, Sparse.eval, nodeValue4941, nodeValue4943, nodeValue4946, nodeValue4950, nodeValue5039, nodeValue5081, nodeValue5169, nodeValue5177, nodeValue5337, nodeValue5356, nodeValue5418, nodeValue5457, nodeValue5460, nodeValue5464, nodeValue5465, nodeValue5466, nodeValue5476, nodeValue5483, nodeValue5486, nodeValue5487]
  ring

noncomputable def reducedSource2078 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4942 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue5043 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5217 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + 0))))))))))))))))))))

def numericRow2078 : Integer.Sparse Master := [(Sum.inr 2489, -1), (Sum.inr 2954, -2), (Sum.inr 3482, -1), (Sum.inr 3606, -2), (Sum.inr 3694, -1), (Sum.inr 3773, -1), (Sum.inr 3779, -1), (Sum.inr 3787, -2), (Sum.inr 3797, -1), (Sum.inr 3804, -2), (Sum.inr 3857, -2), (Sum.inr 3876, -2), (Sum.inr 3983, -4), (Sum.inr 4942, 8), (Sum.inr 4944, 8), (Sum.inr 4945, 8), (Sum.inr 4951, 8), (Sum.inr 5043, 4), (Sum.inr 5189, 4), (Sum.inr 5217, 4), (Sum.inr 5236, 4), (Sum.inr 5269, 4), (Sum.inr 5340, 4), (Sum.inr 5419, 4), (Sum.inr 5461, 4), (Sum.inr 5463, 4)]

theorem reindexCheck2078 : Integer.Sparse.reindex keyMap MixedData.row2078 = numericRow2078 := by decide +kernel

theorem numericCheck2078 (x : Master → ℝ) : Integer.Sparse.eval numericRow2078 x =
    (4 : ℝ) * reducedSource2078 x := by
  norm_num [numericRow2078, reducedSource2078, Integer.Sparse.eval, Sparse.eval, nodeValue4942, nodeValue4944, nodeValue4945, nodeValue4951, nodeValue5043, nodeValue5081, nodeValue5170, nodeValue5189, nodeValue5217, nodeValue5236, nodeValue5269, nodeValue5340, nodeValue5356, nodeValue5393, nodeValue5401, nodeValue5410, nodeValue5419, nodeValue5438, nodeValue5461, nodeValue5463, nodeValue5484]
  ring

noncomputable def reducedSource2079 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2656 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue3407 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((2 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3465 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((2 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + 0))))))))))))))))))))

def numericRow2079 : Integer.Sparse Master := [(Sum.inr 2656, 1), (Sum.inr 2658, 2), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 3407, 2), (Sum.inr 3413, 2), (Sum.inr 3418, 2), (Sum.inr 3465, 1), (Sum.inr 3482, 1), (Sum.inr 3542, 1), (Sum.inr 3606, 2), (Sum.inr 3763, 1), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3804, 2), (Sum.inr 3842, 1), (Sum.inr 3857, 2), (Sum.inr 3960, 1), (Sum.inr 3973, 1), (Sum.inr 3983, 2)]

theorem reindexCheck2079 : Integer.Sparse.reindex keyMap MixedData.row2079 = numericRow2079 := by decide +kernel

theorem numericCheck2079 (x : Master → ℝ) : Integer.Sparse.eval numericRow2079 x =
    (1 : ℝ) * reducedSource2079 x := by
  norm_num [numericRow2079, reducedSource2079, Integer.Sparse.eval, Sparse.eval, nodeValue2656, nodeValue2658, nodeValue2682, nodeValue2736, nodeValue3407, nodeValue3413, nodeValue3418, nodeValue3465, nodeValue3482, nodeValue3542, nodeValue3606, nodeValue3763, nodeValue3773, nodeValue3797, nodeValue3804, nodeValue3816, nodeValue3842, nodeValue3857, nodeValue3960, nodeValue3973, nodeValue3983]

end MUB6.Certificate.MixedSourceBridge

end OAI
