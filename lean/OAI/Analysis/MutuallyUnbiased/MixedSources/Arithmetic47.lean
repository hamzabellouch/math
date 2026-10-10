import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource752 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow752 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 3691, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 3805, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

theorem reindexCheck752 : Integer.Sparse.reindex keyMap MixedData.row752 = numericRow752 := by decide +kernel

theorem numericCheck752 (x : Master → ℝ) : Integer.Sparse.eval numericRow752 x =
    (1 : ℝ) * reducedSource752 x := by
  norm_num [numericRow752, reducedSource752, Integer.Sparse.eval, Sparse.eval, nodeValue2481, nodeValue3691, nodeValue3788, nodeValue3803, nodeValue3805, nodeValue3809, nodeValue4092]

noncomputable def reducedSource753 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2474 x + ((1 : ℝ) * Sparse.eval nodeValue2475 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow753 : Integer.Sparse Master := [(Sum.inr 2474, 1), (Sum.inr 2475, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem reindexCheck753 : Integer.Sparse.reindex keyMap MixedData.row753 = numericRow753 := by decide +kernel

theorem numericCheck753 (x : Master → ℝ) : Integer.Sparse.eval numericRow753 x =
    (1 : ℝ) * reducedSource753 x := by
  norm_num [numericRow753, reducedSource753, Integer.Sparse.eval, Sparse.eval, nodeValue2474, nodeValue2475, nodeValue2481, nodeValue2494, nodeValue2714, nodeValue3803, nodeValue4092]

noncomputable def reducedSource754 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow754 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3698, 1), (Sum.inr 3803, 1), (Sum.inr 3812, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem reindexCheck754 : Integer.Sparse.reindex keyMap MixedData.row754 = numericRow754 := by decide +kernel

theorem numericCheck754 (x : Master → ℝ) : Integer.Sparse.eval numericRow754 x =
    (1 : ℝ) * reducedSource754 x := by
  norm_num [numericRow754, reducedSource754, Integer.Sparse.eval, Sparse.eval, nodeValue2494, nodeValue2714, nodeValue3698, nodeValue3803, nodeValue3812, nodeValue3814, nodeValue4092]

noncomputable def reducedSource755 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3686 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow755 : Integer.Sparse Master := [(Sum.inr 3217, 1), (Sum.inr 3686, 1), (Sum.inr 3691, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem reindexCheck755 : Integer.Sparse.reindex keyMap MixedData.row755 = numericRow755 := by decide +kernel

theorem numericCheck755 (x : Master → ℝ) : Integer.Sparse.eval numericRow755 x =
    (1 : ℝ) * reducedSource755 x := by
  norm_num [numericRow755, reducedSource755, Integer.Sparse.eval, Sparse.eval, nodeValue3217, nodeValue3686, nodeValue3691, nodeValue3698, nodeValue3788, nodeValue3803, nodeValue4092]

noncomputable def reducedSource756 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2475 x + ((2 : ℝ) * Sparse.eval nodeValue3686 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

def numericRow756 : Integer.Sparse Master := [(Sum.inr 2475, 2), (Sum.inr 3686, 2), (Sum.inr 3803, 2), (Sum.inr 4092, -1)]

theorem reindexCheck756 : Integer.Sparse.reindex keyMap MixedData.row756 = numericRow756 := by decide +kernel

theorem numericCheck756 (x : Master → ℝ) : Integer.Sparse.eval numericRow756 x =
    (1 : ℝ) * reducedSource756 x := by
  norm_num [numericRow756, reducedSource756, Integer.Sparse.eval, Sparse.eval, nodeValue2475, nodeValue3686, nodeValue3803, nodeValue4092]

noncomputable def reducedSource757 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4812 x + ((1 : ℝ) * Sparse.eval nodeValue4813 x + ((1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4824 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5146 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5357 x + ((1 : ℝ) * Sparse.eval nodeValue5358 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0)))))))))))))))))))))))))))

def numericRow757 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 3719, -4320), (Sum.inr 3782, -8640), (Sum.inr 3795, -4320), (Sum.inr 3796, -8640), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 4812, 17280), (Sum.inr 4813, 17280), (Sum.inr 4816, 17280), (Sum.inr 4824, 17280), (Sum.inr 4852, 17280), (Sum.inr 5129, 17280), (Sum.inr 5138, 17280), (Sum.inr 5146, 17280), (Sum.inr 5260, 17280), (Sum.inr 5357, 17280), (Sum.inr 5358, 17280), (Sum.inr 5360, 17280), (Sum.inr 5376, 17280), (Sum.inr 5381, 34560), (Sum.inr 5420, 17280), (Sum.inr 5421, 17280), (Sum.inr 5426, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5445, 17280)]

theorem reindexCheck757 : Integer.Sparse.reindex keyMap MixedData.row757 = numericRow757 := by decide +kernel

theorem numericCheck757 (x : Master → ℝ) : Integer.Sparse.eval numericRow757 x =
    (17280 : ℝ) * reducedSource757 x := by
  norm_num [numericRow757, reducedSource757, Integer.Sparse.eval, Sparse.eval, nodeValue4812, nodeValue4813, nodeValue4816, nodeValue4824, nodeValue4852, nodeValue5129, nodeValue5138, nodeValue5146, nodeValue5260, nodeValue5357, nodeValue5358, nodeValue5360, nodeValue5376, nodeValue5378, nodeValue5381, nodeValue5397, nodeValue5411, nodeValue5412, nodeValue5420, nodeValue5421, nodeValue5423, nodeValue5424, nodeValue5426, nodeValue5430, nodeValue5434, nodeValue5436, nodeValue5445, nodeValue5477]
  ring

noncomputable def reducedSource758 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))))))))))))))

def numericRow758 : Integer.Sparse Master := [(Sum.inl 0, -179), (Sum.inl 6, -5), (Sum.inl 2, -40), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 51, -240), (Sum.inl 3, 1520), (Sum.inl 13, 240), (Sum.inl 52, 80), (Sum.inl 23, -480), (Sum.inl 54, -240), (Sum.inl 24, -240), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 25, -480), (Sum.inl 26, 400), (Sum.inl 4, 480), (Sum.inl 27, 60), (Sum.inl 1, -20), (Sum.inr 2071, 4320), (Sum.inr 2072, 4320), (Sum.inr 2078, 4320), (Sum.inr 2089, 4320), (Sum.inr 2196, 4320), (Sum.inr 2916, 4320), (Sum.inr 2922, 4320), (Sum.inr 2933, 4320), (Sum.inr 3086, 4320), (Sum.inr 3715, 4320), (Sum.inr 3718, 4320), (Sum.inr 3722, 4320), (Sum.inr 3723, 4320), (Sum.inr 3752, 4320), (Sum.inr 3762, 4320), (Sum.inr 3796, 4320), (Sum.inr 3814, 4320), (Sum.inr 3841, 4320), (Sum.inr 3870, 4320), (Sum.inr 3873, 4320), (Sum.inr 3877, 4320), (Sum.inr 3880, 4320), (Sum.inr 3972, 4320)]

theorem reindexCheck758 : Integer.Sparse.reindex keyMap MixedData.row758 = numericRow758 := by decide +kernel

theorem numericCheck758 (x : Master → ℝ) : Integer.Sparse.eval numericRow758 x =
    (4320 : ℝ) * reducedSource758 x := by
  norm_num [numericRow758, reducedSource758, Integer.Sparse.eval, Sparse.eval, nodeValue2071, nodeValue2072, nodeValue2078, nodeValue2089, nodeValue2196, nodeValue2916, nodeValue2922, nodeValue2933, nodeValue3086, nodeValue3715, nodeValue3718, nodeValue3722, nodeValue3723, nodeValue3727, nodeValue3752, nodeValue3762, nodeValue3796, nodeValue3814, nodeValue3830, nodeValue3841, nodeValue3870, nodeValue3873, nodeValue3877, nodeValue3880, nodeValue3883, nodeValue3971, nodeValue3972, nodeValue3982, nodeValue3990, nodeValue4032]
  ring

noncomputable def reducedSource759 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + 0))))))))))))))))))))))))))))

def numericRow759 : Integer.Sparse Master := [(Sum.inl 0, -204), (Sum.inl 5, 80), (Sum.inl 6, -10), (Sum.inl 2, -70), (Sum.inl 35, 160), (Sum.inl 51, -480), (Sum.inl 3, 640), (Sum.inl 13, 160), (Sum.inl 52, 160), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 27, -120), (Sum.inl 1, -160), (Sum.inr 2030, 8640), (Sum.inr 2031, 8640), (Sum.inr 2034, 8640), (Sum.inr 2043, 8640), (Sum.inr 2250, 8640), (Sum.inr 3516, 8640), (Sum.inr 3517, 8640), (Sum.inr 3540, 8640), (Sum.inr 3560, 8640), (Sum.inr 3695, 8640), (Sum.inr 3696, 8640), (Sum.inr 3698, 8640), (Sum.inr 3795, 8640), (Sum.inr 3796, 8640), (Sum.inr 3813, 8640), (Sum.inr 3826, 8640), (Sum.inr 3827, 8640), (Sum.inr 3833, 8640), (Sum.inr 3834, 17280), (Sum.inr 3837, 8640), (Sum.inr 3838, 8640), (Sum.inr 3841, 8640), (Sum.inr 3854, 8640), (Sum.inr 3871, 8640), (Sum.inr 3880, 8640)]

theorem reindexCheck759 : Integer.Sparse.reindex keyMap MixedData.row759 = numericRow759 := by decide +kernel

theorem numericCheck759 (x : Master → ℝ) : Integer.Sparse.eval numericRow759 x =
    (8640 : ℝ) * reducedSource759 x := by
  norm_num [numericRow759, reducedSource759, Integer.Sparse.eval, Sparse.eval, nodeValue2030, nodeValue2031, nodeValue2034, nodeValue2043, nodeValue2250, nodeValue3516, nodeValue3517, nodeValue3540, nodeValue3560, nodeValue3695, nodeValue3696, nodeValue3698, nodeValue3795, nodeValue3796, nodeValue3813, nodeValue3826, nodeValue3827, nodeValue3830, nodeValue3833, nodeValue3834, nodeValue3837, nodeValue3838, nodeValue3841, nodeValue3852, nodeValue3854, nodeValue3856, nodeValue3871, nodeValue3880, nodeValue3989]
  ring

noncomputable def reducedSource760 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((1 : ℝ) * Sparse.eval nodeValue4044 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow760 : Integer.Sparse Master := [(Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3946, 1), (Sum.inr 4022, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

theorem reindexCheck760 : Integer.Sparse.reindex keyMap MixedData.row760 = numericRow760 := by decide +kernel

theorem numericCheck760 (x : Master → ℝ) : Integer.Sparse.eval numericRow760 x =
    (1 : ℝ) * reducedSource760 x := by
  norm_num [numericRow760, reducedSource760, Integer.Sparse.eval, Sparse.eval, nodeValue3782, nodeValue3839, nodeValue3946, nodeValue4022, nodeValue4024, nodeValue4044, nodeValue4092]

noncomputable def reducedSource761 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3168 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow761 : Integer.Sparse Master := [(Sum.inr 3168, 1), (Sum.inr 3715, 1), (Sum.inr 3722, 1), (Sum.inr 3725, 1), (Sum.inr 3839, 1), (Sum.inr 4022, 1), (Sum.inr 4092, -1)]

theorem reindexCheck761 : Integer.Sparse.reindex keyMap MixedData.row761 = numericRow761 := by decide +kernel

theorem numericCheck761 (x : Master → ℝ) : Integer.Sparse.eval numericRow761 x =
    (1 : ℝ) * reducedSource761 x := by
  norm_num [numericRow761, reducedSource761, Integer.Sparse.eval, Sparse.eval, nodeValue3168, nodeValue3715, nodeValue3722, nodeValue3725, nodeValue3839, nodeValue4022, nodeValue4092]

noncomputable def reducedSource762 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow762 : Integer.Sparse Master := [(Sum.inr 2568, 1), (Sum.inr 3725, 1), (Sum.inr 3780, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem reindexCheck762 : Integer.Sparse.reindex keyMap MixedData.row762 = numericRow762 := by decide +kernel

theorem numericCheck762 (x : Master → ℝ) : Integer.Sparse.eval numericRow762 x =
    (1 : ℝ) * reducedSource762 x := by
  norm_num [numericRow762, reducedSource762, Integer.Sparse.eval, Sparse.eval, nodeValue2568, nodeValue3725, nodeValue3780, nodeValue3828, nodeValue3839, nodeValue3848, nodeValue4092]

noncomputable def reducedSource763 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow763 : Integer.Sparse Master := [(Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 3782, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

theorem reindexCheck763 : Integer.Sparse.reindex keyMap MixedData.row763 = numericRow763 := by decide +kernel

theorem numericCheck763 (x : Master → ℝ) : Integer.Sparse.eval numericRow763 x =
    (1 : ℝ) * reducedSource763 x := by
  norm_num [numericRow763, reducedSource763, Integer.Sparse.eval, Sparse.eval, nodeValue3170, nodeValue3719, nodeValue3782, nodeValue3809, nodeValue3839, nodeValue4024, nodeValue4092]

noncomputable def reducedSource764 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow764 : Integer.Sparse Master := [(Sum.inr 2557, 1), (Sum.inr 3722, 1), (Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3843, 1), (Sum.inr 4092, -1)]

theorem reindexCheck764 : Integer.Sparse.reindex keyMap MixedData.row764 = numericRow764 := by decide +kernel

theorem numericCheck764 (x : Master → ℝ) : Integer.Sparse.eval numericRow764 x =
    (1 : ℝ) * reducedSource764 x := by
  norm_num [numericRow764, reducedSource764, Integer.Sparse.eval, Sparse.eval, nodeValue2557, nodeValue3722, nodeValue3782, nodeValue3839, nodeValue3841, nodeValue3843, nodeValue4092]

noncomputable def reducedSource765 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow765 : Integer.Sparse Master := [(Sum.inr 3175, 1), (Sum.inr 3723, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

theorem reindexCheck765 : Integer.Sparse.reindex keyMap MixedData.row765 = numericRow765 := by decide +kernel

theorem numericCheck765 (x : Master → ℝ) : Integer.Sparse.eval numericRow765 x =
    (1 : ℝ) * reducedSource765 x := by
  norm_num [numericRow765, reducedSource765, Integer.Sparse.eval, Sparse.eval, nodeValue3175, nodeValue3723, nodeValue3828, nodeValue3839, nodeValue3877, nodeValue3946, nodeValue4092]

noncomputable def reducedSource766 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow766 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3723, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem reindexCheck766 : Integer.Sparse.reindex keyMap MixedData.row766 = numericRow766 := by decide +kernel

theorem numericCheck766 (x : Master → ℝ) : Integer.Sparse.eval numericRow766 x =
    (1 : ℝ) * reducedSource766 x := by
  norm_num [numericRow766, reducedSource766, Integer.Sparse.eval, Sparse.eval, nodeValue2545, nodeValue3715, nodeValue3719, nodeValue3723, nodeValue3837, nodeValue3839, nodeValue4092]

noncomputable def reducedSource767 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow767 : Integer.Sparse Master := [(Sum.inr 3196, 1), (Sum.inr 3780, 1), (Sum.inr 3782, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem reindexCheck767 : Integer.Sparse.reindex keyMap MixedData.row767 = numericRow767 := by decide +kernel

theorem numericCheck767 (x : Master → ℝ) : Integer.Sparse.eval numericRow767 x =
    (1 : ℝ) * reducedSource767 x := by
  norm_num [numericRow767, reducedSource767, Integer.Sparse.eval, Sparse.eval, nodeValue3196, nodeValue3780, nodeValue3782, nodeValue3814, nodeValue3839, nodeValue3841, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
