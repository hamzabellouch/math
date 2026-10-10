import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource672 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue2977 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow672 : Integer.Sparse Master := [(Sum.inr 2571, 1), (Sum.inr 2974, 1), (Sum.inr 2975, 1), (Sum.inr 2977, 1), (Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem reindexCheck672 : Integer.Sparse.reindex keyMap MixedData.row672 = numericRow672 := by decide +kernel

theorem numericCheck672 (x : Master → ℝ) : Integer.Sparse.eval numericRow672 x =
    (1 : ℝ) * reducedSource672 x := by
  norm_num [numericRow672, reducedSource672, Integer.Sparse.eval, Sparse.eval, nodeValue2571, nodeValue2974, nodeValue2975, nodeValue2977, nodeValue3051, nodeValue3848, nodeValue4092]

noncomputable def reducedSource673 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow673 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 2881, 1), (Sum.inr 2882, 1), (Sum.inr 2885, 1), (Sum.inr 3051, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem reindexCheck673 : Integer.Sparse.reindex keyMap MixedData.row673 = numericRow673 := by decide +kernel

theorem numericCheck673 (x : Master → ℝ) : Integer.Sparse.eval numericRow673 x =
    (1 : ℝ) * reducedSource673 x := by
  norm_num [numericRow673, reducedSource673, Integer.Sparse.eval, Sparse.eval, nodeValue2878, nodeValue2881, nodeValue2882, nodeValue2885, nodeValue3051, nodeValue3961, nodeValue4092]

noncomputable def reducedSource674 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow674 : Integer.Sparse Master := [(Sum.inr 2575, 1), (Sum.inr 3043, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3051, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

theorem reindexCheck674 : Integer.Sparse.reindex keyMap MixedData.row674 = numericRow674 := by decide +kernel

theorem numericCheck674 (x : Master → ℝ) : Integer.Sparse.eval numericRow674 x =
    (1 : ℝ) * reducedSource674 x := by
  norm_num [numericRow674, reducedSource674, Integer.Sparse.eval, Sparse.eval, nodeValue2575, nodeValue3043, nodeValue3044, nodeValue3045, nodeValue3051, nodeValue3850, nodeValue4092]

noncomputable def reducedSource675 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2123 x + ((1 : ℝ) * Sparse.eval nodeValue2132 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2756 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2772 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3116 x + 0))))))))))))))))))))))))))))

def numericRow675 : Integer.Sparse Master := [(Sum.inl 0, -242), (Sum.inl 5, -40), (Sum.inl 2, -220), (Sum.inl 35, -160), (Sum.inl 3, -1440), (Sum.inl 13, -320), (Sum.inl 55, 480), (Sum.inl 12, -480), (Sum.inl 26, -480), (Sum.inl 4, -480), (Sum.inl 27, 120), (Sum.inl 1, -170), (Sum.inr 2118, 8640), (Sum.inr 2119, 8640), (Sum.inr 2123, 8640), (Sum.inr 2132, 8640), (Sum.inr 2220, 8640), (Sum.inr 2250, 8640), (Sum.inr 2274, 8640), (Sum.inr 2275, 8640), (Sum.inr 2277, 8640), (Sum.inr 2565, 8640), (Sum.inr 2575, 8640), (Sum.inr 2585, 8640), (Sum.inr 2727, 8640), (Sum.inr 2728, 8640), (Sum.inr 2730, 8640), (Sum.inr 2748, 8640), (Sum.inr 2750, 8640), (Sum.inr 2756, 8640), (Sum.inr 2757, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2772, 8640), (Sum.inr 2773, 17280), (Sum.inr 3091, 8640), (Sum.inr 3115, 8640)]

theorem reindexCheck675 : Integer.Sparse.reindex keyMap MixedData.row675 = numericRow675 := by decide +kernel

theorem numericCheck675 (x : Master → ℝ) : Integer.Sparse.eval numericRow675 x =
    (8640 : ℝ) * reducedSource675 x := by
  norm_num [numericRow675, reducedSource675, Integer.Sparse.eval, Sparse.eval, nodeValue2118, nodeValue2119, nodeValue2123, nodeValue2132, nodeValue2220, nodeValue2250, nodeValue2274, nodeValue2275, nodeValue2277, nodeValue2565, nodeValue2575, nodeValue2585, nodeValue2727, nodeValue2728, nodeValue2730, nodeValue2748, nodeValue2750, nodeValue2756, nodeValue2757, nodeValue2763, nodeValue2764, nodeValue2766, nodeValue2772, nodeValue2773, nodeValue2775, nodeValue3091, nodeValue3109, nodeValue3115, nodeValue3116]
  ring

noncomputable def reducedSource676 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow676 : Integer.Sparse Master := [(Sum.inr 2930, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3394, 1), (Sum.inr 3534, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck676 : Integer.Sparse.reindex keyMap MixedData.row676 = numericRow676 := by decide +kernel

theorem numericCheck676 (x : Master → ℝ) : Integer.Sparse.eval numericRow676 x =
    (1 : ℝ) * reducedSource676 x := by
  norm_num [numericRow676, reducedSource676, Integer.Sparse.eval, Sparse.eval, nodeValue2930, nodeValue3376, nodeValue3380, nodeValue3394, nodeValue3534, nodeValue3573, nodeValue4083]

noncomputable def reducedSource677 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue3551 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow677 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2926, 1), (Sum.inr 3551, 1), (Sum.inr 3567, 1), (Sum.inr 3571, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck677 : Integer.Sparse.reindex keyMap MixedData.row677 = numericRow677 := by decide +kernel

theorem numericCheck677 (x : Master → ℝ) : Integer.Sparse.eval numericRow677 x =
    (1 : ℝ) * reducedSource677 x := by
  norm_num [numericRow677, reducedSource677, Integer.Sparse.eval, Sparse.eval, nodeValue2089, nodeValue2926, nodeValue3551, nodeValue3567, nodeValue3571, nodeValue3573, nodeValue4083]

noncomputable def reducedSource678 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2929 x + ((1 : ℝ) * Sparse.eval nodeValue3149 x + ((1 : ℝ) * Sparse.eval nodeValue3152 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow678 : Integer.Sparse Master := [(Sum.inr 2092, 1), (Sum.inr 2929, 1), (Sum.inr 3149, 1), (Sum.inr 3152, 1), (Sum.inr 3158, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck678 : Integer.Sparse.reindex keyMap MixedData.row678 = numericRow678 := by decide +kernel

theorem numericCheck678 (x : Master → ℝ) : Integer.Sparse.eval numericRow678 x =
    (1 : ℝ) * reducedSource678 x := by
  norm_num [numericRow678, reducedSource678, Integer.Sparse.eval, Sparse.eval, nodeValue2092, nodeValue2929, nodeValue3149, nodeValue3152, nodeValue3158, nodeValue3573, nodeValue4083]

noncomputable def reducedSource679 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue2929 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow679 : Integer.Sparse Master := [(Sum.inr 2926, 1), (Sum.inr 2929, 1), (Sum.inr 2930, 1), (Sum.inr 2956, 1), (Sum.inr 3079, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck679 : Integer.Sparse.reindex keyMap MixedData.row679 = numericRow679 := by decide +kernel

theorem numericCheck679 (x : Master → ℝ) : Integer.Sparse.eval numericRow679 x =
    (1 : ℝ) * reducedSource679 x := by
  norm_num [numericRow679, reducedSource679, Integer.Sparse.eval, Sparse.eval, nodeValue2926, nodeValue2929, nodeValue2930, nodeValue2956, nodeValue3079, nodeValue3573, nodeValue4083]

noncomputable def reducedSource680 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow680 : Integer.Sparse Master := [(Sum.inr 2110, 1), (Sum.inr 3079, 1), (Sum.inr 3505, 1), (Sum.inr 3573, 2), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

theorem reindexCheck680 : Integer.Sparse.reindex keyMap MixedData.row680 = numericRow680 := by decide +kernel

theorem numericCheck680 (x : Master → ℝ) : Integer.Sparse.eval numericRow680 x =
    (1 : ℝ) * reducedSource680 x := by
  norm_num [numericRow680, reducedSource680, Integer.Sparse.eval, Sparse.eval, nodeValue2110, nodeValue3079, nodeValue3505, nodeValue3573, nodeValue3581, nodeValue4083]

noncomputable def reducedSource681 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3152 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3551 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow681 : Integer.Sparse Master := [(Sum.inr 3152, 1), (Sum.inr 3380, 1), (Sum.inr 3551, 1), (Sum.inr 3552, 1), (Sum.inr 3573, 2), (Sum.inr 4083, -1)]

theorem reindexCheck681 : Integer.Sparse.reindex keyMap MixedData.row681 = numericRow681 := by decide +kernel

theorem numericCheck681 (x : Master → ℝ) : Integer.Sparse.eval numericRow681 x =
    (1 : ℝ) * reducedSource681 x := by
  norm_num [numericRow681, reducedSource681, Integer.Sparse.eval, Sparse.eval, nodeValue3152, nodeValue3380, nodeValue3551, nodeValue3552, nodeValue3573, nodeValue4083]

noncomputable def reducedSource682 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4473 x + ((3 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4494 x + ((3 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((3 : ℝ) * Sparse.eval nodeValue5203 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((6 : ℝ) * Sparse.eval nodeValue5266 x + ((3 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))

def numericRow682 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2880, -720), (Sum.inr 2884, -2160), (Sum.inr 3617, -720), (Sum.inr 3621, -2160), (Sum.inr 3909, -720), (Sum.inr 3910, -2160), (Sum.inr 4025, -720), (Sum.inr 4473, 2880), (Sum.inr 4474, 8640), (Sum.inr 4494, 2880), (Sum.inr 5085, 8640), (Sum.inr 5097, 2880), (Sum.inr 5265, 8640), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640)]

theorem reindexCheck682 : Integer.Sparse.reindex keyMap MixedData.row682 = numericRow682 := by decide +kernel

theorem numericCheck682 (x : Master → ℝ) : Integer.Sparse.eval numericRow682 x =
    (2880 : ℝ) * reducedSource682 x := by
  norm_num [numericRow682, reducedSource682, Integer.Sparse.eval, Sparse.eval, nodeValue4473, nodeValue4474, nodeValue4494, nodeValue5085, nodeValue5097, nodeValue5202, nodeValue5203, nodeValue5265, nodeValue5266, nodeValue5270, nodeValue5447, nodeValue5450, nodeValue5474]
  ring

noncomputable def reducedSource683 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1700 x + ((3 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((3 : ℝ) * Sparse.eval nodeValue3075 x + ((3 : ℝ) * Sparse.eval nodeValue3461 x + ((3 : ℝ) * Sparse.eval nodeValue3526 x + ((6 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((3 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))

def numericRow683 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 50), (Sum.inr 1699, 720), (Sum.inr 1700, 720), (Sum.inr 1709, 2160), (Sum.inr 3058, 720), (Sum.inr 3075, 2160), (Sum.inr 3461, 2160), (Sum.inr 3526, 2160), (Sum.inr 3535, 4320), (Sum.inr 3617, 720), (Sum.inr 3621, 2160), (Sum.inr 4025, 720)]

theorem reindexCheck683 : Integer.Sparse.reindex keyMap MixedData.row683 = numericRow683 := by decide +kernel

theorem numericCheck683 (x : Master → ℝ) : Integer.Sparse.eval numericRow683 x =
    (720 : ℝ) * reducedSource683 x := by
  norm_num [numericRow683, reducedSource683, Integer.Sparse.eval, Sparse.eval, nodeValue1699, nodeValue1700, nodeValue1709, nodeValue3058, nodeValue3075, nodeValue3461, nodeValue3526, nodeValue3535, nodeValue3617, nodeValue3621, nodeValue3962, nodeValue4025, nodeValue4029]
  ring

noncomputable def reducedSource684 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((3 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow684 : Integer.Sparse Master := [(Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 3), (Sum.inr 4091, -1)]

theorem reindexCheck684 : Integer.Sparse.reindex keyMap MixedData.row684 = numericRow684 := by decide +kernel

theorem numericCheck684 (x : Master → ℝ) : Integer.Sparse.eval numericRow684 x =
    (1 : ℝ) * reducedSource684 x := by
  norm_num [numericRow684, reducedSource684, Integer.Sparse.eval, Sparse.eval, nodeValue3053, nodeValue3909, nodeValue3910, nodeValue3962, nodeValue4091]

noncomputable def reducedSource685 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2746 x + ((3 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow685 : Integer.Sparse Master := [(Sum.inr 2746, 1), (Sum.inr 2976, 3), (Sum.inr 3053, 1), (Sum.inr 3909, 1), (Sum.inr 4091, -1)]

theorem reindexCheck685 : Integer.Sparse.reindex keyMap MixedData.row685 = numericRow685 := by decide +kernel

theorem numericCheck685 (x : Master → ℝ) : Integer.Sparse.eval numericRow685 x =
    (1 : ℝ) * reducedSource685 x := by
  norm_num [numericRow685, reducedSource685, Integer.Sparse.eval, Sparse.eval, nodeValue2746, nodeValue2976, nodeValue3053, nodeValue3909, nodeValue4091]

noncomputable def reducedSource686 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4878 x + ((3 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4886 x + ((3 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5286 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((6 : ℝ) * Sparse.eval nodeValue5299 x + 0))))))))))))

def numericRow686 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2671, -1440), (Sum.inr 2684, -4320), (Sum.inr 3390, -1440), (Sum.inr 3394, -4320), (Sum.inr 3622, -4320), (Sum.inr 4878, 5760), (Sum.inr 4879, 17280), (Sum.inr 4885, 5760), (Sum.inr 4886, 5760), (Sum.inr 5265, 17280), (Sum.inr 5286, 17280), (Sum.inr 5299, 34560)]

theorem reindexCheck686 : Integer.Sparse.reindex keyMap MixedData.row686 = numericRow686 := by decide +kernel

theorem numericCheck686 (x : Master → ℝ) : Integer.Sparse.eval numericRow686 x =
    (5760 : ℝ) * reducedSource686 x := by
  norm_num [numericRow686, reducedSource686, Integer.Sparse.eval, Sparse.eval, nodeValue4878, nodeValue4879, nodeValue4885, nodeValue4886, nodeValue4889, nodeValue5227, nodeValue5237, nodeValue5265, nodeValue5273, nodeValue5283, nodeValue5286, nodeValue5292, nodeValue5299]
  ring

noncomputable def reducedSource687 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((3 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((3 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue3023 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((6 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))

def numericRow687 : Integer.Sparse Master := [(Sum.inl 0, -73), (Sum.inl 2, -60), (Sum.inl 3, -240), (Sum.inl 13, -240), (Sum.inl 12, -80), (Sum.inl 1, 45), (Sum.inr 2234, 1440), (Sum.inr 2235, 1440), (Sum.inr 2246, 4320), (Sum.inr 2671, 1440), (Sum.inr 2684, 4320), (Sum.inr 3023, 4320), (Sum.inr 3037, 4320), (Sum.inr 3051, 8640), (Sum.inr 3221, 1440)]

theorem reindexCheck687 : Integer.Sparse.reindex keyMap MixedData.row687 = numericRow687 := by decide +kernel

theorem numericCheck687 (x : Master → ℝ) : Integer.Sparse.eval numericRow687 x =
    (1440 : ℝ) * reducedSource687 x := by
  norm_num [numericRow687, reducedSource687, Integer.Sparse.eval, Sparse.eval, nodeValue2234, nodeValue2235, nodeValue2246, nodeValue2671, nodeValue2684, nodeValue2741, nodeValue3023, nodeValue3037, nodeValue3051, nodeValue3076, nodeValue3100, nodeValue3221, nodeValue3223]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
