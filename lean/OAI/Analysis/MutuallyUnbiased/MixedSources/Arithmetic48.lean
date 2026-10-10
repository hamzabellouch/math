import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource768 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue3168 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow768 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 3168, 1), (Sum.inr 3170, 1), (Sum.inr 3175, 1), (Sum.inr 3196, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem reindexCheck768 : Integer.Sparse.reindex keyMap MixedData.row768 = numericRow768 := by decide +kernel

theorem numericCheck768 (x : Master → ℝ) : Integer.Sparse.eval numericRow768 x =
    (1 : ℝ) * reducedSource768 x := by
  norm_num [numericRow768, reducedSource768, Integer.Sparse.eval, Sparse.eval, nodeValue2544, nodeValue3168, nodeValue3170, nodeValue3175, nodeValue3196, nodeValue3839, nodeValue4092]

noncomputable def reducedSource769 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue1994 x + ((1 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3743 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((1 : ℝ) * Sparse.eval nodeValue3829 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + 0))))))))))))))))))))))))))))

def numericRow769 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 40), (Sum.inl 6, -5), (Sum.inl 2, 160), (Sum.inl 35, 80), (Sum.inl 51, -240), (Sum.inl 3, 1280), (Sum.inl 13, 320), (Sum.inl 52, 80), (Sum.inl 55, -240), (Sum.inl 12, 240), (Sum.inl 26, 240), (Sum.inl 4, 480), (Sum.inl 27, -60), (Sum.inl 1, -470), (Sum.inl 31, -240), (Sum.inr 1991, 4320), (Sum.inr 1994, 4320), (Sum.inr 1998, 4320), (Sum.inr 2033, 4320), (Sum.inr 2195, 4320), (Sum.inr 2533, 4320), (Sum.inr 2535, 4320), (Sum.inr 2566, 4320), (Sum.inr 2661, 4320), (Sum.inr 3536, 4320), (Sum.inr 3537, 4320), (Sum.inr 3539, 4320), (Sum.inr 3574, 4320), (Sum.inr 3680, 4320), (Sum.inr 3697, 4320), (Sum.inr 3743, 4320), (Sum.inr 3761, 4320), (Sum.inr 3810, 4320), (Sum.inr 3812, 4320), (Sum.inr 3825, 4320), (Sum.inr 3840, 8640), (Sum.inr 3848, 4320), (Sum.inr 3849, 4320), (Sum.inr 3871, 4320), (Sum.inr 3880, 4320)]

theorem reindexCheck769 : Integer.Sparse.reindex keyMap MixedData.row769 = numericRow769 := by decide +kernel

theorem numericCheck769 (x : Master → ℝ) : Integer.Sparse.eval numericRow769 x =
    (4320 : ℝ) * reducedSource769 x := by
  norm_num [numericRow769, reducedSource769, Integer.Sparse.eval, Sparse.eval, nodeValue1991, nodeValue1994, nodeValue1998, nodeValue2033, nodeValue2195, nodeValue2533, nodeValue2535, nodeValue2566, nodeValue2661, nodeValue3536, nodeValue3537, nodeValue3539, nodeValue3574, nodeValue3680, nodeValue3697, nodeValue3743, nodeValue3761, nodeValue3810, nodeValue3812, nodeValue3825, nodeValue3829, nodeValue3840, nodeValue3848, nodeValue3849, nodeValue3851, nodeValue3855, nodeValue3871, nodeValue3880, nodeValue3994]
  ring

noncomputable def reducedSource770 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow770 : Integer.Sparse Master := [(Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3875, 1), (Sum.inr 3880, 1), (Sum.inr 3901, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

theorem reindexCheck770 : Integer.Sparse.reindex keyMap MixedData.row770 = numericRow770 := by decide +kernel

theorem numericCheck770 (x : Master → ℝ) : Integer.Sparse.eval numericRow770 x =
    (1 : ℝ) * reducedSource770 x := by
  norm_num [numericRow770, reducedSource770, Integer.Sparse.eval, Sparse.eval, nodeValue3871, nodeValue3872, nodeValue3875, nodeValue3880, nodeValue3901, nodeValue3974, nodeValue4091]

noncomputable def reducedSource771 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2611 x + ((1 : ℝ) * Sparse.eval nodeValue2919 x + ((1 : ℝ) * Sparse.eval nodeValue3195 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow771 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2919, 1), (Sum.inr 3195, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem reindexCheck771 : Integer.Sparse.reindex keyMap MixedData.row771 = numericRow771 := by decide +kernel

theorem numericCheck771 (x : Master → ℝ) : Integer.Sparse.eval numericRow771 x =
    (1 : ℝ) * reducedSource771 x := by
  norm_num [numericRow771, reducedSource771, Integer.Sparse.eval, Sparse.eval, nodeValue2611, nodeValue2919, nodeValue3195, nodeValue3197, nodeValue3202, nodeValue3872, nodeValue4091]

noncomputable def reducedSource772 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow772 : Integer.Sparse Master := [(Sum.inr 3197, 1), (Sum.inr 3872, 2), (Sum.inr 3878, 1), (Sum.inr 3899, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem reindexCheck772 : Integer.Sparse.reindex keyMap MixedData.row772 = numericRow772 := by decide +kernel

theorem numericCheck772 (x : Master → ℝ) : Integer.Sparse.eval numericRow772 x =
    (1 : ℝ) * reducedSource772 x := by
  norm_num [numericRow772, reducedSource772, Integer.Sparse.eval, Sparse.eval, nodeValue3197, nodeValue3872, nodeValue3878, nodeValue3899, nodeValue3964, nodeValue4091]

noncomputable def reducedSource773 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2945 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3863 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow773 : Integer.Sparse Master := [(Sum.inr 2612, 1), (Sum.inr 2945, 1), (Sum.inr 3783, 1), (Sum.inr 3863, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem reindexCheck773 : Integer.Sparse.reindex keyMap MixedData.row773 = numericRow773 := by decide +kernel

theorem numericCheck773 (x : Master → ℝ) : Integer.Sparse.eval numericRow773 x =
    (1 : ℝ) * reducedSource773 x := by
  norm_num [numericRow773, reducedSource773, Integer.Sparse.eval, Sparse.eval, nodeValue2612, nodeValue2945, nodeValue3783, nodeValue3863, nodeValue3871, nodeValue3872, nodeValue4091]

noncomputable def reducedSource774 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow774 : Integer.Sparse Master := [(Sum.inr 3202, 1), (Sum.inr 3783, 1), (Sum.inr 3789, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem reindexCheck774 : Integer.Sparse.reindex keyMap MixedData.row774 = numericRow774 := by decide +kernel

theorem numericCheck774 (x : Master → ℝ) : Integer.Sparse.eval numericRow774 x =
    (1 : ℝ) * reducedSource774 x := by
  norm_num [numericRow774, reducedSource774, Integer.Sparse.eval, Sparse.eval, nodeValue3202, nodeValue3783, nodeValue3789, nodeValue3801, nodeValue3872, nodeValue3972, nodeValue4091]

noncomputable def reducedSource775 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2920 x + ((1 : ℝ) * Sparse.eval nodeValue3865 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow775 : Integer.Sparse Master := [(Sum.inr 2623, 1), (Sum.inr 2920, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem reindexCheck775 : Integer.Sparse.reindex keyMap MixedData.row775 = numericRow775 := by decide +kernel

theorem numericCheck775 (x : Master → ℝ) : Integer.Sparse.eval numericRow775 x =
    (1 : ℝ) * reducedSource775 x := by
  norm_num [numericRow775, reducedSource775, Integer.Sparse.eval, Sparse.eval, nodeValue2623, nodeValue2920, nodeValue3865, nodeValue3872, nodeValue3878, nodeValue3880, nodeValue4091]

noncomputable def reducedSource776 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3195 x + ((1 : ℝ) * Sparse.eval nodeValue3863 x + ((1 : ℝ) * Sparse.eval nodeValue3865 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow776 : Integer.Sparse Master := [(Sum.inr 3195, 1), (Sum.inr 3863, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 2), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

theorem reindexCheck776 : Integer.Sparse.reindex keyMap MixedData.row776 = numericRow776 := by decide +kernel

theorem numericCheck776 (x : Master → ℝ) : Integer.Sparse.eval numericRow776 x =
    (1 : ℝ) * reducedSource776 x := by
  norm_num [numericRow776, reducedSource776, Integer.Sparse.eval, Sparse.eval, nodeValue3195, nodeValue3863, nodeValue3865, nodeValue3872, nodeValue3922, nodeValue4091]

noncomputable def reducedSource777 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow777 : Integer.Sparse Master := [(Sum.inr 2617, 1), (Sum.inr 3069, 1), (Sum.inr 3789, 1), (Sum.inr 3872, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem reindexCheck777 : Integer.Sparse.reindex keyMap MixedData.row777 = numericRow777 := by decide +kernel

theorem numericCheck777 (x : Master → ℝ) : Integer.Sparse.eval numericRow777 x =
    (1 : ℝ) * reducedSource777 x := by
  norm_num [numericRow777, reducedSource777, Integer.Sparse.eval, Sparse.eval, nodeValue2617, nodeValue3069, nodeValue3789, nodeValue3872, nodeValue3875, nodeValue4091]

noncomputable def reducedSource778 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2919 x + ((1 : ℝ) * Sparse.eval nodeValue2920 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2945 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow778 : Integer.Sparse Master := [(Sum.inr 2919, 1), (Sum.inr 2920, 1), (Sum.inr 2928, 1), (Sum.inr 2945, 1), (Sum.inr 3069, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem reindexCheck778 : Integer.Sparse.reindex keyMap MixedData.row778 = numericRow778 := by decide +kernel

theorem numericCheck778 (x : Master → ℝ) : Integer.Sparse.eval numericRow778 x =
    (1 : ℝ) * reducedSource778 x := by
  norm_num [numericRow778, reducedSource778, Integer.Sparse.eval, Sparse.eval, nodeValue2919, nodeValue2920, nodeValue2928, nodeValue2945, nodeValue3069, nodeValue3872, nodeValue4091]

noncomputable def reducedSource779 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3712 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

def numericRow779 : Integer.Sparse Master := [(Sum.inl 0, -50), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 25), (Sum.inr 2906, 2160), (Sum.inr 2907, 2160), (Sum.inr 2909, 2160), (Sum.inr 2951, 2160), (Sum.inr 3051, 2160), (Sum.inr 3430, 2160), (Sum.inr 3437, 2160), (Sum.inr 3464, 2160), (Sum.inr 3518, 2160), (Sum.inr 3535, 2160), (Sum.inr 3541, 2160), (Sum.inr 3559, 2160), (Sum.inr 3712, 2160), (Sum.inr 3714, 2160), (Sum.inr 3730, 2160), (Sum.inr 3762, 2160), (Sum.inr 3794, 2160), (Sum.inr 3809, 2160), (Sum.inr 3832, 2160), (Sum.inr 3838, 2160), (Sum.inr 3841, 2160), (Sum.inr 3845, 2160), (Sum.inr 3872, 2160), (Sum.inr 3877, 2160), (Sum.inr 3972, 2160)]

theorem reindexCheck779 : Integer.Sparse.reindex keyMap MixedData.row779 = numericRow779 := by decide +kernel

theorem numericCheck779 (x : Master → ℝ) : Integer.Sparse.eval numericRow779 x =
    (2160 : ℝ) * reducedSource779 x := by
  norm_num [numericRow779, reducedSource779, Integer.Sparse.eval, Sparse.eval, nodeValue2906, nodeValue2907, nodeValue2909, nodeValue2951, nodeValue3051, nodeValue3430, nodeValue3437, nodeValue3464, nodeValue3515, nodeValue3518, nodeValue3535, nodeValue3541, nodeValue3559, nodeValue3712, nodeValue3714, nodeValue3730, nodeValue3762, nodeValue3794, nodeValue3809, nodeValue3832, nodeValue3838, nodeValue3841, nodeValue3845, nodeValue3853, nodeValue3862, nodeValue3872, nodeValue3877, nodeValue3972, nodeValue3990, nodeValue3993]
  ring

noncomputable def reducedSource780 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3970 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

def numericRow780 : Integer.Sparse Master := [(Sum.inl 0, -176), (Sum.inl 5, 20), (Sum.inl 6, -5), (Sum.inl 2, -40), (Sum.inl 51, -240), (Sum.inl 3, 400), (Sum.inl 52, 80), (Sum.inl 12, 80), (Sum.inl 26, 80), (Sum.inl 4, 160), (Sum.inl 1, 145), (Sum.inl 31, -240), (Sum.inr 2454, 4320), (Sum.inr 2455, 4320), (Sum.inr 2463, 4320), (Sum.inr 2494, 4320), (Sum.inr 2732, 4320), (Sum.inr 2905, 4320), (Sum.inr 2909, 4320), (Sum.inr 3039, 4320), (Sum.inr 3558, 4320), (Sum.inr 3559, 4320), (Sum.inr 3561, 4320), (Sum.inr 3573, 4320), (Sum.inr 3679, 4320), (Sum.inr 3698, 4320), (Sum.inr 3714, 4320), (Sum.inr 3724, 4320), (Sum.inr 3838, 4320), (Sum.inr 3839, 4320), (Sum.inr 3841, 4320), (Sum.inr 3866, 4320), (Sum.inr 3871, 4320), (Sum.inr 3876, 4320), (Sum.inr 3877, 4320)]

theorem reindexCheck780 : Integer.Sparse.reindex keyMap MixedData.row780 = numericRow780 := by decide +kernel

theorem numericCheck780 (x : Master → ℝ) : Integer.Sparse.eval numericRow780 x =
    (4320 : ℝ) * reducedSource780 x := by
  norm_num [numericRow780, reducedSource780, Integer.Sparse.eval, Sparse.eval, nodeValue2454, nodeValue2455, nodeValue2463, nodeValue2494, nodeValue2732, nodeValue2905, nodeValue2909, nodeValue2934, nodeValue3039, nodeValue3558, nodeValue3559, nodeValue3561, nodeValue3573, nodeValue3679, nodeValue3698, nodeValue3714, nodeValue3724, nodeValue3838, nodeValue3839, nodeValue3841, nodeValue3853, nodeValue3866, nodeValue3871, nodeValue3876, nodeValue3877, nodeValue3883, nodeValue3889, nodeValue3970, nodeValue3990, nodeValue4003]
  ring

noncomputable def reducedSource781 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow781 : Integer.Sparse Master := [(Sum.inr 2587, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

theorem reindexCheck781 : Integer.Sparse.reindex keyMap MixedData.row781 = numericRow781 := by decide +kernel

theorem numericCheck781 (x : Master → ℝ) : Integer.Sparse.eval numericRow781 x =
    (1 : ℝ) * reducedSource781 x := by
  norm_num [numericRow781, reducedSource781, Integer.Sparse.eval, Sparse.eval, nodeValue2587, nodeValue3730, nodeValue3840, nodeValue3843, nodeValue3848, nodeValue3857, nodeValue4092]

noncomputable def reducedSource782 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue3729 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow782 : Integer.Sparse Master := [(Sum.inr 2577, 2), (Sum.inr 3729, 1), (Sum.inr 3840, 2), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem reindexCheck782 : Integer.Sparse.reindex keyMap MixedData.row782 = numericRow782 := by decide +kernel

theorem numericCheck782 (x : Master → ℝ) : Integer.Sparse.eval numericRow782 x =
    (1 : ℝ) * reducedSource782 x := by
  norm_num [numericRow782, reducedSource782, Integer.Sparse.eval, Sparse.eval, nodeValue2577, nodeValue3729, nodeValue3840, nodeValue3854, nodeValue4092]

noncomputable def reducedSource783 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow783 : Integer.Sparse Master := [(Sum.inr 2974, 1), (Sum.inr 3780, 1), (Sum.inr 3781, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem reindexCheck783 : Integer.Sparse.reindex keyMap MixedData.row783 = numericRow783 := by decide +kernel

theorem numericCheck783 (x : Master → ℝ) : Integer.Sparse.eval numericRow783 x =
    (1 : ℝ) * reducedSource783 x := by
  norm_num [numericRow783, reducedSource783, Integer.Sparse.eval, Sparse.eval, nodeValue2974, nodeValue3780, nodeValue3781, nodeValue3813, nodeValue3840, nodeValue3848, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
