import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource608 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((2 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3239 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + 0))))))))))))))))))))

def numericRow608 : Integer.Sparse Master := [(Sum.inl 0, -16), (Sum.inl 2, -1), (Sum.inl 3, 64), (Sum.inl 13, 48), (Sum.inl 4, 32), (Sum.inl 1, 35), (Sum.inr 2833, 1728), (Sum.inr 2834, 864), (Sum.inr 2836, 864), (Sum.inr 3037, 864), (Sum.inr 3238, 1728), (Sum.inr 3239, 864), (Sum.inr 3241, 864), (Sum.inr 3289, 864), (Sum.inr 3460, 864), (Sum.inr 3461, 864), (Sum.inr 3464, 1728), (Sum.inr 3528, 1728), (Sum.inr 3534, 1728), (Sum.inr 3535, 1728), (Sum.inr 3541, 1728), (Sum.inr 3567, 864), (Sum.inr 3573, 1728), (Sum.inr 3801, 864)]

theorem reindexCheck608 : Integer.Sparse.reindex keyMap MixedData.row608 = numericRow608 := by decide +kernel

theorem numericCheck608 (x : Master → ℝ) : Integer.Sparse.eval numericRow608 x =
    (864 : ℝ) * reducedSource608 x := by
  norm_num [numericRow608, reducedSource608, Integer.Sparse.eval, Sparse.eval, nodeValue2833, nodeValue2834, nodeValue2836, nodeValue3037, nodeValue3238, nodeValue3239, nodeValue3241, nodeValue3289, nodeValue3460, nodeValue3461, nodeValue3464, nodeValue3525, nodeValue3528, nodeValue3534, nodeValue3535, nodeValue3541, nodeValue3567, nodeValue3573, nodeValue3801, nodeValue3847, nodeValue3853]
  ring

noncomputable def reducedSource609 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3906 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

def numericRow609 : Integer.Sparse Master := [(Sum.inr 2730, 2), (Sum.inr 3812, 2), (Sum.inr 3906, 2), (Sum.inr 4092, -1)]

theorem reindexCheck609 : Integer.Sparse.reindex keyMap MixedData.row609 = numericRow609 := by decide +kernel

theorem numericCheck609 (x : Master → ℝ) : Integer.Sparse.eval numericRow609 x =
    (1 : ℝ) * reducedSource609 x := by
  norm_num [numericRow609, reducedSource609, Integer.Sparse.eval, Sparse.eval, nodeValue2730, nodeValue3812, nodeValue3906, nodeValue4092]

noncomputable def reducedSource610 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1276 x + ((1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow610 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2757, 1), (Sum.inr 2773, 2), (Sum.inr 4092, -1)]

theorem reindexCheck610 : Integer.Sparse.reindex keyMap MixedData.row610 = numericRow610 := by decide +kernel

theorem numericCheck610 (x : Master → ℝ) : Integer.Sparse.eval numericRow610 x =
    (1 : ℝ) * reducedSource610 x := by
  norm_num [numericRow610, reducedSource610, Integer.Sparse.eval, Sparse.eval, nodeValue1276, nodeValue2645, nodeValue2730, nodeValue2757, nodeValue2773, nodeValue4092]

noncomputable def reducedSource611 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2493 x + ((2 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow611 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2494, 2), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

theorem reindexCheck611 : Integer.Sparse.reindex keyMap MixedData.row611 = numericRow611 := by decide +kernel

theorem numericCheck611 (x : Master → ℝ) : Integer.Sparse.eval numericRow611 x =
    (1 : ℝ) * reducedSource611 x := by
  norm_num [numericRow611, reducedSource611, Integer.Sparse.eval, Sparse.eval, nodeValue2493, nodeValue2494, nodeValue2508, nodeValue2730, nodeValue3812, nodeValue4092]

noncomputable def reducedSource612 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4406 x + ((2 : ℝ) * Sparse.eval nodeValue4407 x + ((1 : ℝ) * Sparse.eval nodeValue4414 x + ((1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue5004 x + ((2 : ℝ) * Sparse.eval nodeValue5005 x + ((1 : ℝ) * Sparse.eval nodeValue5011 x + ((2 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((2 : ℝ) * Sparse.eval nodeValue5243 x + ((2 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + 0))))))))))))))))))))

def numericRow612 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2880, -2160), (Sum.inr 3053, -2160), (Sum.inr 3617, -2160), (Sum.inr 3619, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3910, -2160), (Sum.inr 3957, -4320), (Sum.inr 4406, 8640), (Sum.inr 4407, 17280), (Sum.inr 4414, 8640), (Sum.inr 4473, 8640), (Sum.inr 5004, 8640), (Sum.inr 5005, 17280), (Sum.inr 5011, 8640), (Sum.inr 5150, 17280), (Sum.inr 5184, 8640), (Sum.inr 5185, 17280), (Sum.inr 5243, 17280), (Sum.inr 5244, 17280), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640), (Sum.inr 5429, 8640)]

theorem reindexCheck612 : Integer.Sparse.reindex keyMap MixedData.row612 = numericRow612 := by decide +kernel

theorem numericCheck612 (x : Master → ℝ) : Integer.Sparse.eval numericRow612 x =
    (8640 : ℝ) * reducedSource612 x := by
  norm_num [numericRow612, reducedSource612, Integer.Sparse.eval, Sparse.eval, nodeValue4406, nodeValue4407, nodeValue4414, nodeValue4473, nodeValue5004, nodeValue5005, nodeValue5011, nodeValue5150, nodeValue5184, nodeValue5185, nodeValue5202, nodeValue5243, nodeValue5244, nodeValue5265, nodeValue5266, nodeValue5270, nodeValue5301, nodeValue5429, nodeValue5431, nodeValue5450, nodeValue5472]
  ring

noncomputable def reducedSource613 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((2 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue2389 x + ((2 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2636 x + ((2 : ℝ) * Sparse.eval nodeValue2697 x + ((2 : ℝ) * Sparse.eval nodeValue2698 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

def numericRow613 : Integer.Sparse Master := [(Sum.inl 0, -70), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, 225), (Sum.inl 51, -720), (Sum.inl 3, 640), (Sum.inl 52, 240), (Sum.inl 4, 400), (Sum.inl 1, -370), (Sum.inl 31, -480), (Sum.inr 987, 4320), (Sum.inr 988, 8640), (Sum.inr 995, 4320), (Sum.inr 1056, 4320), (Sum.inr 2389, 4320), (Sum.inr 2390, 8640), (Sum.inr 2396, 4320), (Sum.inr 2614, 4320), (Sum.inr 2615, 8640), (Sum.inr 2697, 8640), (Sum.inr 2698, 8640), (Sum.inr 2700, 8640), (Sum.inr 2730, 8640), (Sum.inr 2731, 8640), (Sum.inr 2738, 4320), (Sum.inr 3874, 4320), (Sum.inr 3875, 8640)]

theorem reindexCheck613 : Integer.Sparse.reindex keyMap MixedData.row613 = numericRow613 := by decide +kernel

theorem numericCheck613 (x : Master → ℝ) : Integer.Sparse.eval numericRow613 x =
    (4320 : ℝ) * reducedSource613 x := by
  norm_num [numericRow613, reducedSource613, Integer.Sparse.eval, Sparse.eval, nodeValue987, nodeValue988, nodeValue995, nodeValue1056, nodeValue2389, nodeValue2390, nodeValue2396, nodeValue2614, nodeValue2615, nodeValue2636, nodeValue2697, nodeValue2698, nodeValue2700, nodeValue2730, nodeValue2731, nodeValue2738, nodeValue2775, nodeValue3874, nodeValue3875, nodeValue3887, nodeValue4002]
  ring

noncomputable def reducedSource614 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1593 x + ((1 : ℝ) * Sparse.eval nodeValue1594 x + ((2 : ℝ) * Sparse.eval nodeValue1601 x + ((1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue2912 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3337 x + ((2 : ℝ) * Sparse.eval nodeValue3342 x + ((2 : ℝ) * Sparse.eval nodeValue3488 x + ((2 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((2 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

def numericRow614 : Integer.Sparse Master := [(Sum.inl 0, -16), (Sum.inl 2, 50), (Sum.inl 3, 640), (Sum.inl 12, 280), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 400), (Sum.inl 1, -230), (Sum.inr 1593, 2160), (Sum.inr 1594, 2160), (Sum.inr 1601, 4320), (Sum.inr 1699, 2160), (Sum.inr 2912, 2160), (Sum.inr 2923, 4320), (Sum.inr 3075, 2160), (Sum.inr 3337, 2160), (Sum.inr 3342, 4320), (Sum.inr 3488, 4320), (Sum.inr 3497, 4320), (Sum.inr 3524, 2160), (Sum.inr 3526, 4320), (Sum.inr 3529, 4320), (Sum.inr 3535, 4320), (Sum.inr 3617, 2160), (Sum.inr 3619, 2160), (Sum.inr 3954, 2160), (Sum.inr 3957, 2160)]

theorem reindexCheck614 : Integer.Sparse.reindex keyMap MixedData.row614 = numericRow614 := by decide +kernel

theorem numericCheck614 (x : Master → ℝ) : Integer.Sparse.eval numericRow614 x =
    (2160 : ℝ) * reducedSource614 x := by
  norm_num [numericRow614, reducedSource614, Integer.Sparse.eval, Sparse.eval, nodeValue1593, nodeValue1594, nodeValue1601, nodeValue1699, nodeValue2912, nodeValue2923, nodeValue3075, nodeValue3337, nodeValue3342, nodeValue3488, nodeValue3497, nodeValue3524, nodeValue3526, nodeValue3529, nodeValue3535, nodeValue3617, nodeValue3619, nodeValue3954, nodeValue3957, nodeValue4026, nodeValue4029]
  ring

noncomputable def reducedSource615 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow615 : Integer.Sparse Master := [(Sum.inr 3037, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 2), (Sum.inr 3910, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem reindexCheck615 : Integer.Sparse.reindex keyMap MixedData.row615 = numericRow615 := by decide +kernel

theorem numericCheck615 (x : Master → ℝ) : Integer.Sparse.eval numericRow615 x =
    (1 : ℝ) * reducedSource615 x := by
  norm_num [numericRow615, reducedSource615, Integer.Sparse.eval, Sparse.eval, nodeValue3037, nodeValue3846, nodeValue3849, nodeValue3910, nodeValue3957, nodeValue4091]

noncomputable def reducedSource616 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1360 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue1421 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow616 : Integer.Sparse Master := [(Sum.inr 1358, 2), (Sum.inr 1360, 1), (Sum.inr 1366, 1), (Sum.inr 1421, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

theorem reindexCheck616 : Integer.Sparse.reindex keyMap MixedData.row616 = numericRow616 := by decide +kernel

theorem numericCheck616 (x : Master → ℝ) : Integer.Sparse.eval numericRow616 x =
    (1 : ℝ) * reducedSource616 x := by
  norm_num [numericRow616, reducedSource616, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue1360, nodeValue1366, nodeValue1421, nodeValue3037, nodeValue4091]

noncomputable def reducedSource617 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow617 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

theorem reindexCheck617 : Integer.Sparse.reindex keyMap MixedData.row617 = numericRow617 := by decide +kernel

theorem numericCheck617 (x : Master → ℝ) : Integer.Sparse.eval numericRow617 x =
    (1 : ℝ) * reducedSource617 x := by
  norm_num [numericRow617, reducedSource617, Integer.Sparse.eval, Sparse.eval, nodeValue1366, nodeValue2880, nodeValue3037, nodeValue3053, nodeValue4091]

noncomputable def reducedSource618 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow618 : Integer.Sparse Master := [(Sum.inr 2862, 2), (Sum.inr 2864, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem reindexCheck618 : Integer.Sparse.reindex keyMap MixedData.row618 = numericRow618 := by decide +kernel

theorem numericCheck618 (x : Master → ℝ) : Integer.Sparse.eval numericRow618 x =
    (1 : ℝ) * reducedSource618 x := by
  norm_num [numericRow618, reducedSource618, Integer.Sparse.eval, Sparse.eval, nodeValue2862, nodeValue2864, nodeValue2880, nodeValue3037, nodeValue3957, nodeValue4091]

noncomputable def reducedSource619 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((2 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow619 : Integer.Sparse Master := [(Sum.inr 2573, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3037, 2), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

theorem reindexCheck619 : Integer.Sparse.reindex keyMap MixedData.row619 = numericRow619 := by decide +kernel

theorem numericCheck619 (x : Master → ℝ) : Integer.Sparse.eval numericRow619 x =
    (1 : ℝ) * reducedSource619 x := by
  norm_num [numericRow619, reducedSource619, Integer.Sparse.eval, Sparse.eval, nodeValue2573, nodeValue3029, nodeValue3030, nodeValue3037, nodeValue3849, nodeValue4091]

noncomputable def reducedSource620 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4794 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4806 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5230 x + ((3 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5262 x + ((2 : ℝ) * Sparse.eval nodeValue5263 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))

def numericRow620 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2023, -8640), (Sum.inr 2214, -8640), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2671, -4320), (Sum.inr 2721, -12960), (Sum.inr 3053, -4320), (Sum.inr 3390, -4320), (Sum.inr 3532, -12960), (Sum.inr 3619, -4320), (Sum.inr 3622, -4320), (Sum.inr 4793, 17280), (Sum.inr 4794, 17280), (Sum.inr 4795, 17280), (Sum.inr 4806, 34560), (Sum.inr 4878, 17280), (Sum.inr 5226, 34560), (Sum.inr 5230, 17280), (Sum.inr 5231, 51840), (Sum.inr 5262, 34560), (Sum.inr 5263, 34560), (Sum.inr 5265, 34560), (Sum.inr 5299, 34560)]

theorem reindexCheck620 : Integer.Sparse.reindex keyMap MixedData.row620 = numericRow620 := by decide +kernel

theorem numericCheck620 (x : Master → ℝ) : Integer.Sparse.eval numericRow620 x =
    (17280 : ℝ) * reducedSource620 x := by
  norm_num [numericRow620, reducedSource620, Integer.Sparse.eval, Sparse.eval, nodeValue4793, nodeValue4794, nodeValue4795, nodeValue4805, nodeValue4806, nodeValue4878, nodeValue4889, nodeValue5226, nodeValue5227, nodeValue5230, nodeValue5231, nodeValue5256, nodeValue5257, nodeValue5262, nodeValue5263, nodeValue5265, nodeValue5292, nodeValue5299, nodeValue5301]
  ring

noncomputable def reducedSource621 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2117 x + ((2 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2675 x + ((2 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2727 x + ((2 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3093 x + 0))))))))))))))))))))

def numericRow621 : Integer.Sparse Master := [(Sum.inl 0, -109), (Sum.inl 5, 60), (Sum.inl 2, -160), (Sum.inl 35, 240), (Sum.inl 3, 1040), (Sum.inl 55, -720), (Sum.inl 26, 640), (Sum.inl 4, 640), (Sum.inl 27, -180), (Sum.inl 1, -395), (Sum.inr 2117, 4320), (Sum.inr 2118, 8640), (Sum.inr 2131, 4320), (Sum.inr 2213, 4320), (Sum.inr 2214, 8640), (Sum.inr 2219, 4320), (Sum.inr 2277, 4320), (Sum.inr 2675, 4320), (Sum.inr 2676, 8640), (Sum.inr 2721, 8640), (Sum.inr 2727, 8640), (Sum.inr 2728, 8640), (Sum.inr 2730, 8640), (Sum.inr 2773, 8640), (Sum.inr 3043, 4320), (Sum.inr 3091, 8640)]

theorem reindexCheck621 : Integer.Sparse.reindex keyMap MixedData.row621 = numericRow621 := by decide +kernel

theorem numericCheck621 (x : Master → ℝ) : Integer.Sparse.eval numericRow621 x =
    (4320 : ℝ) * reducedSource621 x := by
  norm_num [numericRow621, reducedSource621, Integer.Sparse.eval, Sparse.eval, nodeValue2117, nodeValue2118, nodeValue2131, nodeValue2213, nodeValue2214, nodeValue2219, nodeValue2277, nodeValue2675, nodeValue2676, nodeValue2720, nodeValue2721, nodeValue2727, nodeValue2728, nodeValue2730, nodeValue2766, nodeValue2773, nodeValue2775, nodeValue3043, nodeValue3087, nodeValue3091, nodeValue3093]
  ring

noncomputable def reducedSource622 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2024 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue3034 x + ((2 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3041 x + ((2 : ℝ) * Sparse.eval nodeValue3043 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3203 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

def numericRow622 : Integer.Sparse Master := [(Sum.inl 0, -169), (Sum.inl 5, -120), (Sum.inl 6, 20), (Sum.inl 2, -50), (Sum.inl 7, 160), (Sum.inl 35, 480), (Sum.inl 3, 1840), (Sum.inl 13, 1200), (Sum.inl 52, 320), (Sum.inl 54, -480), (Sum.inl 12, 560), (Sum.inl 26, 320), (Sum.inl 4, 320), (Sum.inl 1, -525), (Sum.inr 2010, 4320), (Sum.inr 2011, 4320), (Sum.inr 2024, 8640), (Sum.inr 2234, 4320), (Sum.inr 2669, 8640), (Sum.inr 2671, 4320), (Sum.inr 2676, 4320), (Sum.inr 2721, 4320), (Sum.inr 3034, 8640), (Sum.inr 3036, 8640), (Sum.inr 3037, 8640), (Sum.inr 3041, 4320), (Sum.inr 3043, 8640), (Sum.inr 3051, 8640), (Sum.inr 3053, 4320), (Sum.inr 3199, 4320)]

theorem reindexCheck622 : Integer.Sparse.reindex keyMap MixedData.row622 = numericRow622 := by decide +kernel

theorem numericCheck622 (x : Master → ℝ) : Integer.Sparse.eval numericRow622 x =
    (4320 : ℝ) * reducedSource622 x := by
  norm_num [numericRow622, reducedSource622, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue2011, nodeValue2024, nodeValue2234, nodeValue2669, nodeValue2671, nodeValue2676, nodeValue2721, nodeValue3034, nodeValue3036, nodeValue3037, nodeValue3041, nodeValue3043, nodeValue3051, nodeValue3053, nodeValue3085, nodeValue3087, nodeValue3100, nodeValue3199, nodeValue3203, nodeValue3223]
  ring

noncomputable def reducedSource623 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow623 : Integer.Sparse Master := [(Sum.inr 3376, 2), (Sum.inr 3378, 1), (Sum.inr 3390, 1), (Sum.inr 3526, 1), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

theorem reindexCheck623 : Integer.Sparse.reindex keyMap MixedData.row623 = numericRow623 := by decide +kernel

theorem numericCheck623 (x : Master → ℝ) : Integer.Sparse.eval numericRow623 x =
    (1 : ℝ) * reducedSource623 x := by
  norm_num [numericRow623, reducedSource623, Integer.Sparse.eval, Sparse.eval, nodeValue3376, nodeValue3378, nodeValue3390, nodeValue3526, nodeValue3532, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
