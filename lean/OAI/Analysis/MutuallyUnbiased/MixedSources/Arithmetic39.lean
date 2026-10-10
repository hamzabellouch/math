import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource624 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3150 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((3 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow624 : Integer.Sparse Master := [(Sum.inr 3150, 1), (Sum.inr 3373, 1), (Sum.inr 3378, 3), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem reindexCheck624 : Integer.Sparse.reindex keyMap MixedData.row624 = numericRow624 := by decide +kernel

theorem numericCheck624 (x : Master → ℝ) : Integer.Sparse.eval numericRow624 x =
    (1 : ℝ) * reducedSource624 x := by
  norm_num [numericRow624, reducedSource624, Integer.Sparse.eval, Sparse.eval, nodeValue3150, nodeValue3373, nodeValue3378, nodeValue3526, nodeValue4083]

noncomputable def reducedSource625 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((2 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3150 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow625 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 3149, 2), (Sum.inr 3150, 1), (Sum.inr 3155, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem reindexCheck625 : Integer.Sparse.reindex keyMap MixedData.row625 = numericRow625 := by decide +kernel

theorem numericCheck625 (x : Master → ℝ) : Integer.Sparse.eval numericRow625 x =
    (1 : ℝ) * reducedSource625 x := by
  norm_num [numericRow625, reducedSource625, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue3149, nodeValue3150, nodeValue3155, nodeValue3526, nodeValue4083]

noncomputable def reducedSource626 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((2 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow626 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 2), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

theorem reindexCheck626 : Integer.Sparse.reindex keyMap MixedData.row626 = numericRow626 := by decide +kernel

theorem numericCheck626 (x : Master → ℝ) : Integer.Sparse.eval numericRow626 x =
    (1 : ℝ) * reducedSource626 x := by
  norm_num [numericRow626, reducedSource626, Integer.Sparse.eval, Sparse.eval, nodeValue2023, nodeValue3378, nodeValue3505, nodeValue3526, nodeValue3532, nodeValue4083]

noncomputable def reducedSource627 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow627 : Integer.Sparse Master := [(Sum.inr 3149, 1), (Sum.inr 3376, 1), (Sum.inr 3500, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck627 : Integer.Sparse.reindex keyMap MixedData.row627 = numericRow627 := by decide +kernel

theorem numericCheck627 (x : Master → ℝ) : Integer.Sparse.eval numericRow627 x =
    (1 : ℝ) * reducedSource627 x := by
  norm_num [numericRow627, reducedSource627, Integer.Sparse.eval, Sparse.eval, nodeValue3149, nodeValue3376, nodeValue3500, nodeValue3505, nodeValue3526, nodeValue3573, nodeValue4083]

noncomputable def reducedSource628 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue5166 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + ((4 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + 0)))))))))))))

def numericRow628 : Integer.Sparse Master := [(Sum.inl 0, 116), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, -40), (Sum.inl 1, 530), (Sum.inr 1293, -2160), (Sum.inr 1294, -2160), (Sum.inr 2954, -4320), (Sum.inr 3053, -2160), (Sum.inr 3054, -2160), (Sum.inr 3304, -2160), (Sum.inr 3305, -2160), (Sum.inr 3308, -1080), (Sum.inr 3603, -2160), (Sum.inr 3606, -4320), (Sum.inr 3619, -2160), (Sum.inr 3623, -4320), (Sum.inr 3626, -2160), (Sum.inr 3633, -2160), (Sum.inr 3902, -2160)]

theorem reindexCheck628 : Integer.Sparse.reindex keyMap MixedData.row628 = numericRow628 := by decide +kernel

theorem numericCheck628 (x : Master → ℝ) : Integer.Sparse.eval numericRow628 x =
    (4320 : ℝ) * reducedSource628 x := by
  norm_num [numericRow628, reducedSource628, Integer.Sparse.eval, Sparse.eval, nodeValue4618, nodeValue4619, nodeValue4623, nodeValue5166, nodeValue5168, nodeValue5170, nodeValue5301, nodeValue5302, nodeValue5306, nodeValue5308, nodeValue5310, nodeValue5439, nodeValue5453, nodeValue5455]
  ring

noncomputable def reducedSource629 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1293 x + ((2 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue2953 x + ((4 : ℝ) * Sparse.eval nodeValue2954 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((2 : ℝ) * Sparse.eval nodeValue3053 x + ((2 : ℝ) * Sparse.eval nodeValue3054 x + ((4 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((2 : ℝ) * Sparse.eval nodeValue4012 x + ((2 : ℝ) * Sparse.eval nodeValue4019 x + 0)))))))))))))

def numericRow629 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, -250), (Sum.inr 1293, 1080), (Sum.inr 1294, 1080), (Sum.inr 2954, 2160), (Sum.inr 3053, 1080), (Sum.inr 3054, 1080)]

theorem reindexCheck629 : Integer.Sparse.reindex keyMap MixedData.row629 = numericRow629 := by decide +kernel

theorem numericCheck629 (x : Master → ℝ) : Integer.Sparse.eval numericRow629 x =
    (540 : ℝ) * reducedSource629 x := by
  norm_num [numericRow629, reducedSource629, Integer.Sparse.eval, Sparse.eval, nodeValue1293, nodeValue1294, nodeValue1305, nodeValue2953, nodeValue2954, nodeValue2963, nodeValue3053, nodeValue3054, nodeValue3120, nodeValue3121, nodeValue3124, nodeValue3912, nodeValue4012, nodeValue4019]
  ring

noncomputable def reducedSource630 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((4 : ℝ) * Sparse.eval nodeValue5102 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

def numericRow630 : Integer.Sparse Master := [(Sum.inl 0, 118), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, -80), (Sum.inl 1, -95), (Sum.inr 1079, -2160), (Sum.inr 1080, -1080), (Sum.inr 1083, -2160), (Sum.inr 1708, -2160), (Sum.inr 1710, -1080), (Sum.inr 1728, -2160), (Sum.inr 2508, -2160), (Sum.inr 2509, -2160), (Sum.inr 2512, -4320), (Sum.inr 2704, -2160), (Sum.inr 2739, -4320), (Sum.inr 2740, -4320), (Sum.inr 2743, -2160), (Sum.inr 3460, -2160), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3622, -2160), (Sum.inr 3627, -2160), (Sum.inr 4010, -2160)]

theorem reindexCheck630 : Integer.Sparse.reindex keyMap MixedData.row630 = numericRow630 := by decide +kernel

theorem numericCheck630 (x : Master → ℝ) : Integer.Sparse.eval numericRow630 x =
    (4320 : ℝ) * reducedSource630 x := by
  norm_num [numericRow630, reducedSource630, Integer.Sparse.eval, Sparse.eval, nodeValue4495, nodeValue4496, nodeValue4499, nodeValue5098, nodeValue5099, nodeValue5102, nodeValue5271, nodeValue5272, nodeValue5275, nodeValue5292, nodeValue5293, nodeValue5485, nodeValue5492, nodeValue5493]
  ring

noncomputable def reducedSource631 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2508 x + ((2 : ℝ) * Sparse.eval nodeValue2509 x + ((4 : ℝ) * Sparse.eval nodeValue2512 x + ((4 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue3984 x + ((2 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0)))))))))))))

def numericRow631 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, 16), (Sum.inr 1079, 432), (Sum.inr 1080, 216), (Sum.inr 1083, 432), (Sum.inr 2508, 432), (Sum.inr 2509, 432), (Sum.inr 2512, 864), (Sum.inr 2739, 864), (Sum.inr 2740, 432), (Sum.inr 2743, 432)]

theorem reindexCheck631 : Integer.Sparse.reindex keyMap MixedData.row631 = numericRow631 := by decide +kernel

theorem numericCheck631 (x : Master → ℝ) : Integer.Sparse.eval numericRow631 x =
    (216 : ℝ) * reducedSource631 x := by
  norm_num [numericRow631, reducedSource631, Integer.Sparse.eval, Sparse.eval, nodeValue1079, nodeValue1080, nodeValue1083, nodeValue2508, nodeValue2509, nodeValue2512, nodeValue2739, nodeValue2740, nodeValue2743, nodeValue2766, nodeValue2767, nodeValue3984, nodeValue4015, nodeValue4018]
  ring

noncomputable def reducedSource632 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((4 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((4 : ℝ) * Sparse.eval nodeValue5304 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))

def numericRow632 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2244, -4320), (Sum.inr 2247, -2160), (Sum.inr 2262, -4320), (Sum.inr 2290, -2160), (Sum.inr 2739, -8640), (Sum.inr 2764, -4320), (Sum.inr 2782, -8640), (Sum.inr 3534, -8640), (Sum.inr 3581, -4320), (Sum.inr 3583, -8640), (Sum.inr 3622, -4320), (Sum.inr 5270, 17280), (Sum.inr 5289, 34560), (Sum.inr 5295, 17280)]

theorem reindexCheck632 : Integer.Sparse.reindex keyMap MixedData.row632 = numericRow632 := by decide +kernel

theorem numericCheck632 (x : Master → ℝ) : Integer.Sparse.eval numericRow632 x =
    (8640 : ℝ) * reducedSource632 x := by
  norm_num [numericRow632, reducedSource632, Integer.Sparse.eval, Sparse.eval, nodeValue4888, nodeValue4890, nodeValue4895, nodeValue5256, nodeValue5270, nodeValue5271, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5295, nodeValue5304, nodeValue5307]
  ring

noncomputable def reducedSource633 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((2 : ℝ) * Sparse.eval nodeValue3085 x + ((4 : ℝ) * Sparse.eval nodeValue3097 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((4 : ℝ) * Sparse.eval nodeValue3109 x + ((2 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3122 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

def numericRow633 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 2754, 1080), (Sum.inr 2764, 1080), (Sum.inr 2769, 1080), (Sum.inr 2782, 1080), (Sum.inr 3097, 2160)]

theorem reindexCheck633 : Integer.Sparse.reindex keyMap MixedData.row633 = numericRow633 := by decide +kernel

theorem numericCheck633 (x : Master → ℝ) : Integer.Sparse.eval numericRow633 x =
    (540 : ℝ) * reducedSource633 x := by
  norm_num [numericRow633, reducedSource633, Integer.Sparse.eval, Sparse.eval, nodeValue2754, nodeValue2755, nodeValue2764, nodeValue2769, nodeValue2782, nodeValue2785, nodeValue3085, nodeValue3097, nodeValue3100, nodeValue3109, nodeValue3119, nodeValue3122, nodeValue3227, nodeValue3229]
  ring

noncomputable def reducedSource634 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3581 x + ((2 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((1 : ℝ) * Sparse.eval nodeValue3628 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow634 : Integer.Sparse Master := [(Sum.inr 3581, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem reindexCheck634 : Integer.Sparse.reindex keyMap MixedData.row634 = numericRow634 := by decide +kernel

theorem numericCheck634 (x : Master → ℝ) : Integer.Sparse.eval numericRow634 x =
    (1 : ℝ) * reducedSource634 x := by
  norm_num [numericRow634, reducedSource634, Integer.Sparse.eval, Sparse.eval, nodeValue3581, nodeValue3583, nodeValue3623, nodeValue3628, nodeValue4083]

noncomputable def reducedSource635 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0)))))))))))))))))))))))))))))

def numericRow635 : Integer.Sparse Master := [(Sum.inl 0, -206), (Sum.inl 2, -30), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 200), (Sum.inr 1228, 4320), (Sum.inr 1229, 4320), (Sum.inr 1230, 4320), (Sum.inr 1241, 4320), (Sum.inr 1291, 4320), (Sum.inr 2874, 4320), (Sum.inr 2875, 4320), (Sum.inr 2876, 4320), (Sum.inr 2885, 4320), (Sum.inr 2921, 4320), (Sum.inr 2922, 4320), (Sum.inr 2928, 4320), (Sum.inr 2951, 4320), (Sum.inr 3023, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3051, 4320), (Sum.inr 3086, 4320), (Sum.inr 3097, 4320), (Sum.inr 3098, 4320), (Sum.inr 3809, 4320), (Sum.inr 3959, 4320), (Sum.inr 3972, 4320)]

theorem reindexCheck635 : Integer.Sparse.reindex keyMap MixedData.row635 = numericRow635 := by decide +kernel

theorem numericCheck635 (x : Master → ℝ) : Integer.Sparse.eval numericRow635 x =
    (4320 : ℝ) * reducedSource635 x := by
  norm_num [numericRow635, reducedSource635, Integer.Sparse.eval, Sparse.eval, nodeValue1228, nodeValue1229, nodeValue1230, nodeValue1241, nodeValue1291, nodeValue2874, nodeValue2875, nodeValue2876, nodeValue2885, nodeValue2921, nodeValue2922, nodeValue2928, nodeValue2951, nodeValue3023, nodeValue3024, nodeValue3025, nodeValue3051, nodeValue3085, nodeValue3086, nodeValue3089, nodeValue3097, nodeValue3098, nodeValue3103, nodeValue3109, nodeValue3119, nodeValue3809, nodeValue3959, nodeValue3972, nodeValue3982, nodeValue3987]
  ring

noncomputable def reducedSource636 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2502 x + ((1 : ℝ) * Sparse.eval nodeValue2506 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0)))))))))))))))))))))))))))))

def numericRow636 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -65), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -160), (Sum.inl 1, 205), (Sum.inr 2500, 4320), (Sum.inr 2502, 4320), (Sum.inr 2506, 4320), (Sum.inr 2513, 4320), (Sum.inr 2781, 4320), (Sum.inr 3286, 4320), (Sum.inr 3287, 4320), (Sum.inr 3296, 4320), (Sum.inr 3303, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3540, 4320), (Sum.inr 3557, 4320), (Sum.inr 3558, 4320), (Sum.inr 3560, 4320), (Sum.inr 3566, 4320), (Sum.inr 3567, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3575, 4320), (Sum.inr 3577, 4320), (Sum.inr 3582, 4320), (Sum.inr 3583, 4320), (Sum.inr 3871, 4320), (Sum.inr 3881, 4320)]

theorem reindexCheck636 : Integer.Sparse.reindex keyMap MixedData.row636 = numericRow636 := by decide +kernel

theorem numericCheck636 (x : Master → ℝ) : Integer.Sparse.eval numericRow636 x =
    (4320 : ℝ) * reducedSource636 x := by
  norm_num [numericRow636, reducedSource636, Integer.Sparse.eval, Sparse.eval, nodeValue2500, nodeValue2502, nodeValue2506, nodeValue2513, nodeValue2781, nodeValue3286, nodeValue3287, nodeValue3296, nodeValue3303, nodeValue3525, nodeValue3533, nodeValue3534, nodeValue3540, nodeValue3557, nodeValue3558, nodeValue3560, nodeValue3566, nodeValue3567, nodeValue3570, nodeValue3572, nodeValue3573, nodeValue3575, nodeValue3577, nodeValue3582, nodeValue3583, nodeValue3852, nodeValue3871, nodeValue3881, nodeValue3883, nodeValue3888]
  ring

noncomputable def reducedSource637 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow637 : Integer.Sparse Master := [(Sum.inr 2763, 1), (Sum.inr 3813, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3903, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem reindexCheck637 : Integer.Sparse.reindex keyMap MixedData.row637 = numericRow637 := by decide +kernel

theorem numericCheck637 (x : Master → ℝ) : Integer.Sparse.eval numericRow637 x =
    (1 : ℝ) * reducedSource637 x := by
  norm_num [numericRow637, reducedSource637, Integer.Sparse.eval, Sparse.eval, nodeValue2763, nodeValue3813, nodeValue3848, nodeValue3884, nodeValue3903, nodeValue3913, nodeValue4092]

noncomputable def reducedSource638 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow638 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 1261, 1), (Sum.inr 1263, 1), (Sum.inr 1268, 1), (Sum.inr 1291, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

theorem reindexCheck638 : Integer.Sparse.reindex keyMap MixedData.row638 = numericRow638 := by decide +kernel

theorem numericCheck638 (x : Master → ℝ) : Integer.Sparse.eval numericRow638 x =
    (1 : ℝ) * reducedSource638 x := by
  norm_num [numericRow638, reducedSource638, Integer.Sparse.eval, Sparse.eval, nodeValue1259, nodeValue1261, nodeValue1263, nodeValue1268, nodeValue1291, nodeValue2763, nodeValue4092]

noncomputable def reducedSource639 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow639 : Integer.Sparse Master := [(Sum.inr 2566, 1), (Sum.inr 2568, 1), (Sum.inr 2571, 1), (Sum.inr 2587, 1), (Sum.inr 2763, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem reindexCheck639 : Integer.Sparse.reindex keyMap MixedData.row639 = numericRow639 := by decide +kernel

theorem numericCheck639 (x : Master → ℝ) : Integer.Sparse.eval numericRow639 x =
    (1 : ℝ) * reducedSource639 x := by
  norm_num [numericRow639, reducedSource639, Integer.Sparse.eval, Sparse.eval, nodeValue2566, nodeValue2568, nodeValue2571, nodeValue2587, nodeValue2763, nodeValue3848, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
