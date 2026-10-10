import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
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

noncomputable def reducedSource960 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((3 : ℝ) * Sparse.eval nodeValue5406 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((6 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))

def numericRow960 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3721, -4320), (Sum.inr 3731, -1440), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3836, -4320), (Sum.inr 3867, -1440), (Sum.inr 3899, -2880), (Sum.inr 3900, -4320), (Sum.inr 3964, -4320), (Sum.inr 4046, -4320), (Sum.inr 4851, 17280), (Sum.inr 4863, 5760), (Sum.inr 4885, 5760), (Sum.inr 5429, 17280), (Sum.inr 5430, 34560)]

theorem reindexCheck960 : Integer.Sparse.reindex keyMap MixedData.row960 = numericRow960 := by decide +kernel

theorem numericCheck960 (x : Master → ℝ) : Integer.Sparse.eval numericRow960 x =
    (5760 : ℝ) * reducedSource960 x := by
  norm_num [numericRow960, reducedSource960, Integer.Sparse.eval, Sparse.eval, nodeValue4851, nodeValue4863, nodeValue4885, nodeValue5380, nodeValue5383, nodeValue5406, nodeValue5422, nodeValue5427, nodeValue5429, nodeValue5430, nodeValue5437, nodeValue5479, nodeValue5482]
  ring

noncomputable def reducedSource961 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((3 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5359 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((6 : ℝ) * Sparse.eval nodeValue5445 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((3 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + 0))))))))))))

def numericRow961 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -10), (Sum.inr 3053, -1440), (Sum.inr 3619, -1440), (Sum.inr 3899, -2880), (Sum.inr 3901, -4320), (Sum.inr 3910, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 5085, 17280), (Sum.inr 5097, 5760), (Sum.inr 5277, 5760), (Sum.inr 5281, 17280), (Sum.inr 5359, 17280), (Sum.inr 5445, 34560)]

theorem reindexCheck961 : Integer.Sparse.reindex keyMap MixedData.row961 = numericRow961 := by decide +kernel

theorem numericCheck961 (x : Master → ℝ) : Integer.Sparse.eval numericRow961 x =
    (5760 : ℝ) * reducedSource961 x := by
  norm_num [numericRow961, reducedSource961, Integer.Sparse.eval, Sparse.eval, nodeValue5085, nodeValue5097, nodeValue5277, nodeValue5281, nodeValue5301, nodeValue5359, nodeValue5433, nodeValue5437, nodeValue5445, nodeValue5450, nodeValue5469, nodeValue5474, nodeValue5479]
  ring

noncomputable def reducedSource962 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((3 : ℝ) * Sparse.eval nodeValue3074 x + ((3 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((3 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((3 : ℝ) * Sparse.eval nodeValue3952 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3975 x + ((6 : ℝ) * Sparse.eval nodeValue4024 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + ((3 : ℝ) * Sparse.eval nodeValue4033 x + 0))))))))))))

def numericRow962 : Integer.Sparse Master := [(Sum.inl 0, -63), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 10), (Sum.inr 3058, 1440), (Sum.inr 3059, 1440), (Sum.inr 3074, 4320), (Sum.inr 3461, 4320), (Sum.inr 3619, 1440), (Sum.inr 3759, 4320), (Sum.inr 3899, 1440), (Sum.inr 3952, 4320), (Sum.inr 4024, 8640)]

theorem reindexCheck962 : Integer.Sparse.reindex keyMap MixedData.row962 = numericRow962 := by decide +kernel

theorem numericCheck962 (x : Master → ℝ) : Integer.Sparse.eval numericRow962 x =
    (1440 : ℝ) * reducedSource962 x := by
  norm_num [numericRow962, reducedSource962, Integer.Sparse.eval, Sparse.eval, nodeValue3058, nodeValue3059, nodeValue3074, nodeValue3461, nodeValue3619, nodeValue3759, nodeValue3899, nodeValue3952, nodeValue3962, nodeValue3975, nodeValue4024, nodeValue4029, nodeValue4033]
  ring

noncomputable def reducedSource963 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

def numericRow963 : Integer.Sparse Master := [(Sum.inl 0, 118), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, -150), (Sum.inr 2589, -720), (Sum.inr 2590, -1440), (Sum.inr 2764, -720), (Sum.inr 3563, -720), (Sum.inr 3564, -1440), (Sum.inr 3581, -720), (Sum.inr 3613, -720), (Sum.inr 3787, -1440), (Sum.inr 3790, -1440), (Sum.inr 3804, -1440), (Sum.inr 3809, -1440), (Sum.inr 3813, -1440), (Sum.inr 3815, -1440), (Sum.inr 3896, -720), (Sum.inr 3898, -720), (Sum.inr 3909, -720), (Sum.inr 3910, -720), (Sum.inr 3913, -1440), (Sum.inr 4010, -2160), (Sum.inr 4025, -720)]

theorem reindexCheck963 : Integer.Sparse.reindex keyMap MixedData.row963 = numericRow963 := by decide +kernel

theorem numericCheck963 (x : Master → ℝ) : Integer.Sparse.eval numericRow963 x =
    (2880 : ℝ) * reducedSource963 x := by
  norm_num [numericRow963, reducedSource963, Integer.Sparse.eval, Sparse.eval, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5290, nodeValue5401, nodeValue5404, nodeValue5411, nodeValue5416, nodeValue5418, nodeValue5442, nodeValue5447, nodeValue5450, nodeValue5451, nodeValue5452, nodeValue5462, nodeValue5481, nodeValue5485, nodeValue5489, nodeValue5492, nodeValue5493]
  ring

noncomputable def reducedSource964 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))))

def numericRow964 : Integer.Sparse Master := [(Sum.inl 0, 751), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 4, -320), (Sum.inl 1, 50), (Sum.inr 2508, -4320), (Sum.inr 2509, -4320), (Sum.inr 2512, -8640), (Sum.inr 2703, -4320), (Sum.inr 2704, -4320), (Sum.inr 2705, -4320), (Sum.inr 2739, -8640), (Sum.inr 3460, -4320), (Sum.inr 3471, -8640), (Sum.inr 3496, -4320), (Sum.inr 3498, -4320), (Sum.inr 3534, -8640), (Sum.inr 3623, -4320), (Sum.inr 3703, -4320), (Sum.inr 3705, -8640), (Sum.inr 3758, -4320), (Sum.inr 3767, -8640), (Sum.inr 3902, -4320), (Sum.inr 3945, -8640), (Sum.inr 3952, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4046, -4320), (Sum.inr 4047, -8640)]

theorem reindexCheck964 : Integer.Sparse.reindex keyMap MixedData.row964 = numericRow964 := by decide +kernel

theorem numericCheck964 (x : Master → ℝ) : Integer.Sparse.eval numericRow964 x =
    (17280 : ℝ) * reducedSource964 x := by
  norm_num [numericRow964, reducedSource964, Integer.Sparse.eval, Sparse.eval, nodeValue5098, nodeValue5099, nodeValue5102, nodeValue5247, nodeValue5248, nodeValue5271, nodeValue5306, nodeValue5365, nodeValue5368, nodeValue5439, nodeValue5469, nodeValue5473, nodeValue5478, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5489, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5499]
  ring

noncomputable def reducedSource965 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5069 x + ((1 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5092 x + ((1 : ℝ) * Sparse.eval nodeValue5132 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5350 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5362 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))))))))))

def numericRow965 : Integer.Sparse Master := [(Sum.inl 0, 8), (Sum.inl 2, -5), (Sum.inl 1, 15), (Sum.inr 3787, -360), (Sum.inr 3800, -360), (Sum.inr 3804, -360), (Sum.inr 3805, -360), (Sum.inr 3838, -360), (Sum.inr 3843, -360), (Sum.inr 3857, -360), (Sum.inr 3876, -360), (Sum.inr 3974, -720), (Sum.inr 3983, -1440), (Sum.inr 4010, -360), (Sum.inr 4046, -360), (Sum.inr 5069, 1440), (Sum.inr 5071, 1440), (Sum.inr 5074, 1440), (Sum.inr 5092, 1440), (Sum.inr 5132, 1440), (Sum.inr 5138, 1440), (Sum.inr 5160, 1440), (Sum.inr 5255, 1440), (Sum.inr 5289, 1440), (Sum.inr 5350, 1440), (Sum.inr 5353, 1440), (Sum.inr 5362, 1440), (Sum.inr 5419, 1440), (Sum.inr 5421, 1440), (Sum.inr 5430, 2880), (Sum.inr 5461, 1440), (Sum.inr 5470, 1440), (Sum.inr 5480, 1440)]

theorem reindexCheck965 : Integer.Sparse.reindex keyMap MixedData.row965 = numericRow965 := by decide +kernel

theorem numericCheck965 (x : Master → ℝ) : Integer.Sparse.eval numericRow965 x =
    (1440 : ℝ) * reducedSource965 x := by
  norm_num [numericRow965, reducedSource965, Integer.Sparse.eval, Sparse.eval, nodeValue5069, nodeValue5071, nodeValue5074, nodeValue5092, nodeValue5132, nodeValue5138, nodeValue5160, nodeValue5255, nodeValue5289, nodeValue5350, nodeValue5353, nodeValue5362, nodeValue5401, nodeValue5405, nodeValue5419, nodeValue5421, nodeValue5424, nodeValue5430, nodeValue5438, nodeValue5461, nodeValue5470, nodeValue5471, nodeValue5478, nodeValue5480, nodeValue5481, nodeValue5482, nodeValue5484, nodeValue5485]
  ring

noncomputable def reducedSource966 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue3442 x + ((1 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

def numericRow966 : Integer.Sparse Master := [(Sum.inl 0, -292), (Sum.inl 2, 300), (Sum.inl 3, 640), (Sum.inl 12, 160), (Sum.inl 4, 480), (Sum.inl 1, -880), (Sum.inl 31, -480), (Sum.inr 2550, 8640), (Sum.inr 2551, 8640), (Sum.inr 2557, 8640), (Sum.inr 2587, 8640), (Sum.inr 2718, 8640), (Sum.inr 3442, 8640), (Sum.inr 3445, 8640), (Sum.inr 3463, 8640), (Sum.inr 3572, 8640), (Sum.inr 3748, 8640), (Sum.inr 3750, 8640), (Sum.inr 3761, 8640), (Sum.inr 3804, 8640), (Sum.inr 3805, 8640), (Sum.inr 3848, 8640), (Sum.inr 3871, 8640), (Sum.inr 3922, 8640), (Sum.inr 3927, 8640), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

theorem reindexCheck966 : Integer.Sparse.reindex keyMap MixedData.row966 = numericRow966 := by decide +kernel

theorem numericCheck966 (x : Master → ℝ) : Integer.Sparse.eval numericRow966 x =
    (8640 : ℝ) * reducedSource966 x := by
  norm_num [numericRow966, reducedSource966, Integer.Sparse.eval, Sparse.eval, nodeValue2550, nodeValue2551, nodeValue2557, nodeValue2587, nodeValue2718, nodeValue3442, nodeValue3445, nodeValue3463, nodeValue3572, nodeValue3748, nodeValue3750, nodeValue3761, nodeValue3804, nodeValue3805, nodeValue3848, nodeValue3871, nodeValue3922, nodeValue3927, nodeValue3946, nodeValue3955, nodeValue3956, nodeValue3978, nodeValue3979, nodeValue3980, nodeValue3983, nodeValue3984, nodeValue3990, nodeValue3993, nodeValue3994, nodeValue3997]
  ring

noncomputable def reducedSource967 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2476 x + ((1 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2501 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3499 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3700 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3966 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

def numericRow967 : Integer.Sparse Master := [(Sum.inl 0, -156), (Sum.inl 5, 48), (Sum.inl 6, -6), (Sum.inl 2, 150), (Sum.inl 7, 96), (Sum.inl 35, 96), (Sum.inl 3, 864), (Sum.inl 13, 192), (Sum.inl 24, -288), (Sum.inl 12, 384), (Sum.inl 56, -288), (Sum.inl 26, 96), (Sum.inl 4, 576), (Sum.inl 27, -72), (Sum.inl 1, -504), (Sum.inr 2476, 5184), (Sum.inr 2478, 5184), (Sum.inr 2481, 5184), (Sum.inr 2501, 5184), (Sum.inr 2763, 5184), (Sum.inr 3499, 5184), (Sum.inr 3503, 5184), (Sum.inr 3517, 5184), (Sum.inr 3558, 5184), (Sum.inr 3688, 5184), (Sum.inr 3691, 5184), (Sum.inr 3700, 5184), (Sum.inr 3842, 5184), (Sum.inr 3843, 5184), (Sum.inr 3848, 5184), (Sum.inr 3857, 5184), (Sum.inr 3873, 5184), (Sum.inr 3947, 5184), (Sum.inr 3972, 5184), (Sum.inr 3973, 5184), (Sum.inr 3974, 5184), (Sum.inr 3978, 5184), (Sum.inr 3983, 5184)]

theorem reindexCheck967 : Integer.Sparse.reindex keyMap MixedData.row967 = numericRow967 := by decide +kernel

theorem numericCheck967 (x : Master → ℝ) : Integer.Sparse.eval numericRow967 x =
    (5184 : ℝ) * reducedSource967 x := by
  norm_num [numericRow967, reducedSource967, Integer.Sparse.eval, Sparse.eval, nodeValue2476, nodeValue2478, nodeValue2481, nodeValue2501, nodeValue2763, nodeValue3499, nodeValue3503, nodeValue3517, nodeValue3558, nodeValue3688, nodeValue3691, nodeValue3700, nodeValue3842, nodeValue3843, nodeValue3848, nodeValue3857, nodeValue3873, nodeValue3947, nodeValue3966, nodeValue3972, nodeValue3973, nodeValue3974, nodeValue3976, nodeValue3977, nodeValue3978, nodeValue3983, nodeValue3991, nodeValue3992, nodeValue3997, nodeValue3998]
  ring

noncomputable def reducedSource968 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))

def numericRow968 : Integer.Sparse Master := [(Sum.inl 0, 1007), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -110), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -160), (Sum.inl 24, 240), (Sum.inl 12, -160), (Sum.inl 4, 160), (Sum.inl 27, 180), (Sum.inl 1, 340), (Sum.inl 30, 480), (Sum.inr 2553, -8640), (Sum.inr 2556, -4320), (Sum.inr 2721, -4320), (Sum.inr 3514, -8640), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3602, -4320), (Sum.inr 3779, -8640), (Sum.inr 3781, -8640), (Sum.inr 3794, -8640), (Sum.inr 3797, -8640), (Sum.inr 3800, -8640), (Sum.inr 3805, -8640), (Sum.inr 3903, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 4041, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -8640)]

theorem reindexCheck968 : Integer.Sparse.reindex keyMap MixedData.row968 = numericRow968 := by decide +kernel

theorem numericCheck968 (x : Master → ℝ) : Integer.Sparse.eval numericRow968 x =
    (17280 : ℝ) * reducedSource968 x := by
  norm_num [numericRow968, reducedSource968, Integer.Sparse.eval, Sparse.eval, nodeValue5134, nodeValue5137, nodeValue5167, nodeValue5257, nodeValue5393, nodeValue5395, nodeValue5405, nodeValue5434, nodeValue5460, nodeValue5464, nodeValue5469, nodeValue5472, nodeValue5482, nodeValue5483, nodeValue5486, nodeValue5489, nodeValue5490, nodeValue5498, nodeValue5499]
  ring

noncomputable def reducedSource969 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))))

def numericRow969 : Integer.Sparse Master := [(Sum.inl 0, 1049), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -100), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -320), (Sum.inl 24, 240), (Sum.inl 12, -160), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, 620), (Sum.inl 30, 480), (Sum.inr 2479, -4320), (Sum.inr 2480, -8640), (Sum.inr 2508, -4320), (Sum.inr 3459, -4320), (Sum.inr 3460, -4320), (Sum.inr 3467, -8640), (Sum.inr 3622, -4320), (Sum.inr 3689, -4320), (Sum.inr 3690, -8640), (Sum.inr 3703, -4320), (Sum.inr 3757, -4320), (Sum.inr 3758, -4320), (Sum.inr 3764, -8640), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3896, -4320), (Sum.inr 3901, -4320), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4045, -8640), (Sum.inr 4047, -8640)]

theorem reindexCheck969 : Integer.Sparse.reindex keyMap MixedData.row969 = numericRow969 := by decide +kernel

theorem numericCheck969 (x : Master → ℝ) : Integer.Sparse.eval numericRow969 x =
    (17280 : ℝ) * reducedSource969 x := by
  norm_num [numericRow969, reducedSource969, Integer.Sparse.eval, Sparse.eval, nodeValue5072, nodeValue5073, nodeValue5098, nodeValue5292, nodeValue5351, nodeValue5352, nodeValue5365, nodeValue5416, nodeValue5424, nodeValue5433, nodeValue5476, nodeValue5477, nodeValue5478, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5490, nodeValue5493, nodeValue5497, nodeValue5499, nodeValue5500]
  ring

noncomputable def reducedSource970 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

def numericRow970 : Integer.Sparse Master := [(Sum.inl 0, 2118), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -165), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -240), (Sum.inl 24, 720), (Sum.inl 12, -240), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, -1710), (Sum.inr 2477, -25920), (Sum.inr 2483, -12960), (Sum.inr 2503, -12960), (Sum.inr 2764, -12960), (Sum.inr 3444, -25920), (Sum.inr 3446, -12960), (Sum.inr 3477, -12960), (Sum.inr 3581, -12960), (Sum.inr 3687, -25920), (Sum.inr 3692, -12960), (Sum.inr 3701, -12960), (Sum.inr 3749, -25920), (Sum.inr 3751, -12960), (Sum.inr 3769, -12960), (Sum.inr 3782, -25920), (Sum.inr 3787, -25920), (Sum.inr 3796, -25920), (Sum.inr 3804, -25920), (Sum.inr 3849, -12960), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3896, -12960), (Sum.inr 3900, -12960), (Sum.inr 3901, -12960), (Sum.inr 3903, -25920), (Sum.inr 3910, -12960), (Sum.inr 3964, -12960), (Sum.inr 3983, -51840), (Sum.inr 4010, -12960)]

theorem reindexCheck970 : Integer.Sparse.reindex keyMap MixedData.row970 = numericRow970 := by decide +kernel

theorem numericCheck970 (x : Master → ℝ) : Integer.Sparse.eval numericRow970 x =
    (51840 : ℝ) * reducedSource970 x := by
  norm_num [numericRow970, reducedSource970, Integer.Sparse.eval, Sparse.eval, nodeValue5070, nodeValue5076, nodeValue5093, nodeValue5290, nodeValue5349, nodeValue5354, nodeValue5363, nodeValue5397, nodeValue5401, nodeValue5416, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5438, nodeValue5450, nodeValue5484, nodeValue5485, nodeValue5489, nodeValue5490, nodeValue5492]
  ring

noncomputable def reducedSource971 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue3687 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3701 x + ((2 : ℝ) * Sparse.eval nodeValue3787 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4011 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

def numericRow971 : Integer.Sparse Master := [(Sum.inl 0, -1251), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 7, 240), (Sum.inl 8, 240), (Sum.inl 24, -720), (Sum.inl 27, -180), (Sum.inl 1, 1050), (Sum.inr 2477, 25920), (Sum.inr 2483, 12960), (Sum.inr 2503, 12960), (Sum.inr 2764, 12960), (Sum.inr 3687, 25920), (Sum.inr 3692, 12960), (Sum.inr 3701, 12960), (Sum.inr 3787, 25920), (Sum.inr 3796, 25920), (Sum.inr 3849, 12960), (Sum.inr 3876, 25920), (Sum.inr 3900, 12960), (Sum.inr 3901, 12960), (Sum.inr 3910, 12960), (Sum.inr 3983, 25920)]

theorem reindexCheck971 : Integer.Sparse.reindex keyMap MixedData.row971 = numericRow971 := by decide +kernel

theorem numericCheck971 (x : Master → ℝ) : Integer.Sparse.eval numericRow971 x =
    (12960 : ℝ) * reducedSource971 x := by
  norm_num [numericRow971, reducedSource971, Integer.Sparse.eval, Sparse.eval, nodeValue2477, nodeValue2483, nodeValue2503, nodeValue2764, nodeValue3687, nodeValue3692, nodeValue3701, nodeValue3787, nodeValue3796, nodeValue3849, nodeValue3876, nodeValue3900, nodeValue3901, nodeValue3910, nodeValue3967, nodeValue3982, nodeValue3983, nodeValue3998, nodeValue4011, nodeValue4013, nodeValue4017]
  ring

noncomputable def reducedSource972 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

def numericRow972 : Integer.Sparse Master := [(Sum.inl 0, 88), (Sum.inl 2, -60), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 300), (Sum.inr 3787, -4320), (Sum.inr 3789, -2160), (Sum.inr 3804, -4320), (Sum.inr 3810, -2160), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3902, -2160), (Sum.inr 3957, -4320), (Sum.inr 3974, -8640), (Sum.inr 3983, -8640), (Sum.inr 4010, -2160), (Sum.inr 4046, -4320), (Sum.inr 5249, 8640), (Sum.inr 5251, 8640), (Sum.inr 5255, 17280), (Sum.inr 5281, 8640), (Sum.inr 5414, 8640), (Sum.inr 5429, 8640), (Sum.inr 5430, 17280), (Sum.inr 5470, 17280), (Sum.inr 5480, 17280)]

theorem reindexCheck972 : Integer.Sparse.reindex keyMap MixedData.row972 = numericRow972 := by decide +kernel

theorem numericCheck972 (x : Master → ℝ) : Integer.Sparse.eval numericRow972 x =
    (8640 : ℝ) * reducedSource972 x := by
  norm_num [numericRow972, reducedSource972, Integer.Sparse.eval, Sparse.eval, nodeValue5249, nodeValue5251, nodeValue5255, nodeValue5281, nodeValue5401, nodeValue5403, nodeValue5408, nodeValue5414, nodeValue5424, nodeValue5429, nodeValue5430, nodeValue5431, nodeValue5439, nodeValue5470, nodeValue5472, nodeValue5478, nodeValue5480, nodeValue5482, nodeValue5484, nodeValue5485, nodeValue5486]
  ring

noncomputable def reducedSource973 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

def numericRow973 : Integer.Sparse Master := [(Sum.inl 0, -206), (Sum.inl 2, 270), (Sum.inl 3, 1440), (Sum.inl 12, 240), (Sum.inl 26, 320), (Sum.inl 4, 960), (Sum.inl 1, -1260), (Sum.inl 31, -480), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2718, 8640), (Sum.inr 2750, 4320), (Sum.inr 3804, 8640), (Sum.inr 3810, 4320), (Sum.inr 3849, 4320), (Sum.inr 3869, 4320), (Sum.inr 3871, 8640), (Sum.inr 3954, 4320), (Sum.inr 3955, 8640), (Sum.inr 3957, 4320), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

theorem reindexCheck973 : Integer.Sparse.reindex keyMap MixedData.row973 = numericRow973 := by decide +kernel

theorem numericCheck973 (x : Master → ℝ) : Integer.Sparse.eval numericRow973 x =
    (4320 : ℝ) * reducedSource973 x := by
  norm_num [numericRow973, reducedSource973, Integer.Sparse.eval, Sparse.eval, nodeValue2708, nodeValue2710, nodeValue2718, nodeValue2750, nodeValue3804, nodeValue3806, nodeValue3810, nodeValue3849, nodeValue3869, nodeValue3871, nodeValue3954, nodeValue3955, nodeValue3957, nodeValue3978, nodeValue3980, nodeValue3983, nodeValue3985, nodeValue3990, nodeValue3994, nodeValue3998, nodeValue4012]
  ring

noncomputable def reducedSource974 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))

def numericRow974 : Integer.Sparse Master := [(Sum.inl 0, 131), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 80), (Sum.inl 4, 320), (Sum.inl 1, 90), (Sum.inr 2954, -4320), (Sum.inr 3606, -4320), (Sum.inr 3787, -4320), (Sum.inr 3790, -4320), (Sum.inr 3804, -4320), (Sum.inr 3815, -4320), (Sum.inr 3857, -8640), (Sum.inr 3876, -8640), (Sum.inr 3902, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3974, -8640), (Sum.inr 3983, -17280), (Sum.inr 4010, -8640), (Sum.inr 5160, 17280), (Sum.inr 5161, 17280), (Sum.inr 5164, 17280), (Sum.inr 5255, 17280), (Sum.inr 5260, 17280), (Sum.inr 5269, 17280), (Sum.inr 5289, 34560), (Sum.inr 5430, 17280), (Sum.inr 5446, 17280), (Sum.inr 5461, 17280), (Sum.inr 5463, 17280), (Sum.inr 5470, 17280), (Sum.inr 5480, 34560)]

theorem reindexCheck974 : Integer.Sparse.reindex keyMap MixedData.row974 = numericRow974 := by decide +kernel

theorem numericCheck974 (x : Master → ℝ) : Integer.Sparse.eval numericRow974 x =
    (17280 : ℝ) * reducedSource974 x := by
  norm_num [numericRow974, reducedSource974, Integer.Sparse.eval, Sparse.eval, nodeValue5160, nodeValue5161, nodeValue5164, nodeValue5170, nodeValue5255, nodeValue5260, nodeValue5269, nodeValue5289, nodeValue5401, nodeValue5404, nodeValue5410, nodeValue5430, nodeValue5438, nodeValue5439, nodeValue5446, nodeValue5461, nodeValue5463, nodeValue5470, nodeValue5473, nodeValue5478, nodeValue5480, nodeValue5481, nodeValue5484, nodeValue5485, nodeValue5486]
  ring

noncomputable def reducedSource975 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))))))))))

def numericRow975 : Integer.Sparse Master := [(Sum.inl 0, -166), (Sum.inl 2, 30), (Sum.inl 3, -640), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 4, -480), (Sum.inl 1, -20), (Sum.inr 2718, 4320), (Sum.inr 2719, 4320), (Sum.inr 2724, 4320), (Sum.inr 2736, 4320), (Sum.inr 2763, 4320), (Sum.inr 3558, 4320), (Sum.inr 3565, 4320), (Sum.inr 3572, 4320), (Sum.inr 3606, 4320), (Sum.inr 3804, 4320), (Sum.inr 3815, 4320), (Sum.inr 3857, 4320), (Sum.inr 3955, 4320), (Sum.inr 3959, 4320), (Sum.inr 3960, 4320), (Sum.inr 3961, 4320), (Sum.inr 3972, 4320), (Sum.inr 3973, 4320), (Sum.inr 3974, 4320), (Sum.inr 3978, 8640), (Sum.inr 3983, 4320)]

theorem reindexCheck975 : Integer.Sparse.reindex keyMap MixedData.row975 = numericRow975 := by decide +kernel

theorem numericCheck975 (x : Master → ℝ) : Integer.Sparse.eval numericRow975 x =
    (4320 : ℝ) * reducedSource975 x := by
  norm_num [numericRow975, reducedSource975, Integer.Sparse.eval, Sparse.eval, nodeValue2718, nodeValue2719, nodeValue2724, nodeValue2736, nodeValue2763, nodeValue3558, nodeValue3565, nodeValue3572, nodeValue3606, nodeValue3804, nodeValue3815, nodeValue3816, nodeValue3857, nodeValue3955, nodeValue3959, nodeValue3960, nodeValue3961, nodeValue3972, nodeValue3973, nodeValue3974, nodeValue3978, nodeValue3979, nodeValue3983, nodeValue3984, nodeValue3985, nodeValue3993, nodeValue3997, nodeValue3998, nodeValue4012]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
