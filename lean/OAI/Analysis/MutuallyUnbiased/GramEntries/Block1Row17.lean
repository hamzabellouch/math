import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block52
import OAI.Analysis.MutuallyUnbiased.GramRows.Block53
import OAI.Analysis.MutuallyUnbiased.GramRows.Block54
import OAI.Analysis.MutuallyUnbiased.GramRows.Block55
import OAI.Analysis.MutuallyUnbiased.GramRows.Block56
import OAI.Analysis.MutuallyUnbiased.GramRows.Block57

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3704, row3705, row3706, row3707, row3708, row3709, row3710, row3711, row3712, row3713, row3714, row3715, row3716, row3717, row3718, row3719, row3720, row3721, row3722, row3723, row3724, row3725, row3726, row3727, row3728, row3729, row3730, row3731, row3732, row3733]

theorem entryCheck17_0 : entry17_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_0 k)) := by decide +kernel

theorem rowsSound17_0 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval3704 x
  · exact rowEval3705 x
  · exact rowEval3706 x
  · exact rowEval3707 x
  · exact rowEval3708 x
  · exact rowEval3709 x
  · exact rowEval3710 x
  · exact rowEval3711 x
  · exact rowEval3712 x
  · exact rowEval3713 x
  · exact rowEval3714 x
  · exact rowEval3715 x
  · exact rowEval3716 x
  · exact rowEval3717 x
  · exact rowEval3718 x
  · exact rowEval3719 x
  · exact rowEval3720 x
  · exact rowEval3721 x
  · exact rowEval3722 x
  · exact rowEval3723 x
  · exact rowEval3724 x
  · exact rowEval3725 x
  · exact rowEval3726 x
  · exact rowEval3727 x
  · exact rowEval3728 x
  · exact rowEval3729 x
  · exact rowEval3730 x
  · exact rowEval3731 x
  · exact rowEval3732 x
  · exact rowEval3733 x

theorem entryEval17_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_0 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck17_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_0]

def rows17_1 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3734, row3735, row3736, row3737, row3738, row3739, row3740, row3741, row3742, row3743, row3744, row3745, row3746, row3747, row3748, row3749, row3750, row3751, row3752, row3753, row3754, row3755, row3756, row3757, row3758, row3759, row3760, row3761, row3762, row3763]

theorem entryCheck17_1 : entry17_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_1 k)) := by decide +kernel

theorem rowsSound17_1 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval3734 x
  · exact rowEval3735 x
  · exact rowEval3736 x
  · exact rowEval3737 x
  · exact rowEval3738 x
  · exact rowEval3739 x
  · exact rowEval3740 x
  · exact rowEval3741 x
  · exact rowEval3742 x
  · exact rowEval3743 x
  · exact rowEval3744 x
  · exact rowEval3745 x
  · exact rowEval3746 x
  · exact rowEval3747 x
  · exact rowEval3748 x
  · exact rowEval3749 x
  · exact rowEval3750 x
  · exact rowEval3751 x
  · exact rowEval3752 x
  · exact rowEval3753 x
  · exact rowEval3754 x
  · exact rowEval3755 x
  · exact rowEval3756 x
  · exact rowEval3757 x
  · exact rowEval3758 x
  · exact rowEval3759 x
  · exact rowEval3760 x
  · exact rowEval3761 x
  · exact rowEval3762 x
  · exact rowEval3763 x

theorem entryEval17_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_1 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck17_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_1]

def rows17_2 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3764, row3765, row3766, row3767, row3768, row3769, row3770, row3771, row3772, row3773, row3774, row3775, row3776, row3777, row3778, row3779, row3780, row3781, row3782, row3783, row3784, row3785, row3786, row3787, row3788, row3789, row3790, row3791, row3792, row3793]

theorem entryCheck17_2 : entry17_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_2 k)) := by decide +kernel

theorem rowsSound17_2 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval3764 x
  · exact rowEval3765 x
  · exact rowEval3766 x
  · exact rowEval3767 x
  · exact rowEval3768 x
  · exact rowEval3769 x
  · exact rowEval3770 x
  · exact rowEval3771 x
  · exact rowEval3772 x
  · exact rowEval3773 x
  · exact rowEval3774 x
  · exact rowEval3775 x
  · exact rowEval3776 x
  · exact rowEval3777 x
  · exact rowEval3778 x
  · exact rowEval3779 x
  · exact rowEval3780 x
  · exact rowEval3781 x
  · exact rowEval3782 x
  · exact rowEval3783 x
  · exact rowEval3784 x
  · exact rowEval3785 x
  · exact rowEval3786 x
  · exact rowEval3787 x
  · exact rowEval3788 x
  · exact rowEval3789 x
  · exact rowEval3790 x
  · exact rowEval3791 x
  · exact rowEval3792 x
  · exact rowEval3793 x

theorem entryEval17_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_2 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck17_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_2]

def rows17_3 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3794, row3795, row3796, row3797, row3798, row3799, row3800, row3801, row3802, row3803, row3804, row3805, row3806, row3807, row3808, row3809, row3810, row3811, row3812, row3813, row3814, row3815, row3816, row3817, row3818, row3819, row3820, row3821, row3822, row3823]

theorem entryCheck17_3 : entry17_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_3 k)) := by decide +kernel

theorem rowsSound17_3 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval3794 x
  · exact rowEval3795 x
  · exact rowEval3796 x
  · exact rowEval3797 x
  · exact rowEval3798 x
  · exact rowEval3799 x
  · exact rowEval3800 x
  · exact rowEval3801 x
  · exact rowEval3802 x
  · exact rowEval3803 x
  · exact rowEval3804 x
  · exact rowEval3805 x
  · exact rowEval3806 x
  · exact rowEval3807 x
  · exact rowEval3808 x
  · exact rowEval3809 x
  · exact rowEval3810 x
  · exact rowEval3811 x
  · exact rowEval3812 x
  · exact rowEval3813 x
  · exact rowEval3814 x
  · exact rowEval3815 x
  · exact rowEval3816 x
  · exact rowEval3817 x
  · exact rowEval3818 x
  · exact rowEval3819 x
  · exact rowEval3820 x
  · exact rowEval3821 x
  · exact rowEval3822 x
  · exact rowEval3823 x

theorem entryEval17_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_3 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck17_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_3]

def rows17_4 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3824, row3825, row3826, row3827, row3828, row3829, row3830, row3831, row3832, row3833, row3834, row3835, row3836, row3837, row3838, row3839, row3840, row3841, row3842, row3843, row3844, row3845, row3846, row3847, row3848, row3849, row3850, row3851, row3852, row3853]

theorem entryCheck17_4 : entry17_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_4 k)) := by decide +kernel

theorem rowsSound17_4 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval3824 x
  · exact rowEval3825 x
  · exact rowEval3826 x
  · exact rowEval3827 x
  · exact rowEval3828 x
  · exact rowEval3829 x
  · exact rowEval3830 x
  · exact rowEval3831 x
  · exact rowEval3832 x
  · exact rowEval3833 x
  · exact rowEval3834 x
  · exact rowEval3835 x
  · exact rowEval3836 x
  · exact rowEval3837 x
  · exact rowEval3838 x
  · exact rowEval3839 x
  · exact rowEval3840 x
  · exact rowEval3841 x
  · exact rowEval3842 x
  · exact rowEval3843 x
  · exact rowEval3844 x
  · exact rowEval3845 x
  · exact rowEval3846 x
  · exact rowEval3847 x
  · exact rowEval3848 x
  · exact rowEval3849 x
  · exact rowEval3850 x
  · exact rowEval3851 x
  · exact rowEval3852 x
  · exact rowEval3853 x

theorem entryEval17_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_4 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck17_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_4]

def rows17_5 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3854, row3855, row3856, row3857, row3858, row3859, row3860, row3861, row3862, row3863, row3864, row3865, row3866, row3867, row3868, row3869, row3870, row3871, row3872, row3873, row3874, row3875, row3876, row3877, row3878, row3879, row3880, row3881, row3882, row3883]

theorem entryCheck17_5 : entry17_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_5 k)) := by decide +kernel

theorem rowsSound17_5 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval3854 x
  · exact rowEval3855 x
  · exact rowEval3856 x
  · exact rowEval3857 x
  · exact rowEval3858 x
  · exact rowEval3859 x
  · exact rowEval3860 x
  · exact rowEval3861 x
  · exact rowEval3862 x
  · exact rowEval3863 x
  · exact rowEval3864 x
  · exact rowEval3865 x
  · exact rowEval3866 x
  · exact rowEval3867 x
  · exact rowEval3868 x
  · exact rowEval3869 x
  · exact rowEval3870 x
  · exact rowEval3871 x
  · exact rowEval3872 x
  · exact rowEval3873 x
  · exact rowEval3874 x
  · exact rowEval3875 x
  · exact rowEval3876 x
  · exact rowEval3877 x
  · exact rowEval3878 x
  · exact rowEval3879 x
  · exact rowEval3880 x
  · exact rowEval3881 x
  · exact rowEval3882 x
  · exact rowEval3883 x

theorem entryEval17_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_5 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck17_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_5]

def rows17_6 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3884, row3885, row3886, row3887, row3888, row3889, row3890, row3891, row3892, row3893, row3894, row3895, row3896, row3897, row3898, row3899, row3900, row3901, row3902, row3903, row3904, row3905, row3906, row3907, row3908, row3909, row3910, row3911, row3912, row3913]

theorem entryCheck17_6 : entry17_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_6 k)) := by decide +kernel

theorem rowsSound17_6 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval3884 x
  · exact rowEval3885 x
  · exact rowEval3886 x
  · exact rowEval3887 x
  · exact rowEval3888 x
  · exact rowEval3889 x
  · exact rowEval3890 x
  · exact rowEval3891 x
  · exact rowEval3892 x
  · exact rowEval3893 x
  · exact rowEval3894 x
  · exact rowEval3895 x
  · exact rowEval3896 x
  · exact rowEval3897 x
  · exact rowEval3898 x
  · exact rowEval3899 x
  · exact rowEval3900 x
  · exact rowEval3901 x
  · exact rowEval3902 x
  · exact rowEval3903 x
  · exact rowEval3904 x
  · exact rowEval3905 x
  · exact rowEval3906 x
  · exact rowEval3907 x
  · exact rowEval3908 x
  · exact rowEval3909 x
  · exact rowEval3910 x
  · exact rowEval3911 x
  · exact rowEval3912 x
  · exact rowEval3913 x

theorem entryEval17_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_6 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck17_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_6]

def rows17_7 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3914, row3915, row3916, row3917, row3918, row3919, row3920, row3921, row3922, row3923, row3924, row3925, row3926, row3927, row3928, row3929, row3930, row3931, row3932, row3933, row3934, row3935, row3936, row3937, row3938, row3939, row3940, row3941, row3942, row3943]

theorem entryCheck17_7 : entry17_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_7 k)) := by decide +kernel

theorem rowsSound17_7 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval3914 x
  · exact rowEval3915 x
  · exact rowEval3916 x
  · exact rowEval3917 x
  · exact rowEval3918 x
  · exact rowEval3919 x
  · exact rowEval3920 x
  · exact rowEval3921 x
  · exact rowEval3922 x
  · exact rowEval3923 x
  · exact rowEval3924 x
  · exact rowEval3925 x
  · exact rowEval3926 x
  · exact rowEval3927 x
  · exact rowEval3928 x
  · exact rowEval3929 x
  · exact rowEval3930 x
  · exact rowEval3931 x
  · exact rowEval3932 x
  · exact rowEval3933 x
  · exact rowEval3934 x
  · exact rowEval3935 x
  · exact rowEval3936 x
  · exact rowEval3937 x
  · exact rowEval3938 x
  · exact rowEval3939 x
  · exact rowEval3940 x
  · exact rowEval3941 x
  · exact rowEval3942 x
  · exact rowEval3943 x

theorem entryEval17_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_7 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck17_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_7]

def rows17_8 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3944, row3945, row3946, row3947, row3948, row3949, row3950, row3951, row3952, row3953, row3954, row3955, row3956, row3957, row3958, row3959, row3960, row3961, row3962, row3963, row3964, row3965, row3966, row3967, row3968, row3969, row3970, row3971, row3972, row3973]

theorem entryCheck17_8 : entry17_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_8 k)) := by decide +kernel

theorem rowsSound17_8 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval3944 x
  · exact rowEval3945 x
  · exact rowEval3946 x
  · exact rowEval3947 x
  · exact rowEval3948 x
  · exact rowEval3949 x
  · exact rowEval3950 x
  · exact rowEval3951 x
  · exact rowEval3952 x
  · exact rowEval3953 x
  · exact rowEval3954 x
  · exact rowEval3955 x
  · exact rowEval3956 x
  · exact rowEval3957 x
  · exact rowEval3958 x
  · exact rowEval3959 x
  · exact rowEval3960 x
  · exact rowEval3961 x
  · exact rowEval3962 x
  · exact rowEval3963 x
  · exact rowEval3964 x
  · exact rowEval3965 x
  · exact rowEval3966 x
  · exact rowEval3967 x
  · exact rowEval3968 x
  · exact rowEval3969 x
  · exact rowEval3970 x
  · exact rowEval3971 x
  · exact rowEval3972 x
  · exact rowEval3973 x

theorem entryEval17_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_8 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck17_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_8]

def rows17_9 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3974, row3975, row3976, row3977, row3978, row3979, row3980, row3981, row3982, row3983, row3984, row3985, row3986, row3987, row3988, row3989, row3990, row3991, row3992, row3993, row3994, row3995, row3996, row3997, row3998, row3999, row4000, row4001, row4002, row4003]

theorem entryCheck17_9 : entry17_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_9 k)) := by decide +kernel

theorem rowsSound17_9 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval3974 x
  · exact rowEval3975 x
  · exact rowEval3976 x
  · exact rowEval3977 x
  · exact rowEval3978 x
  · exact rowEval3979 x
  · exact rowEval3980 x
  · exact rowEval3981 x
  · exact rowEval3982 x
  · exact rowEval3983 x
  · exact rowEval3984 x
  · exact rowEval3985 x
  · exact rowEval3986 x
  · exact rowEval3987 x
  · exact rowEval3988 x
  · exact rowEval3989 x
  · exact rowEval3990 x
  · exact rowEval3991 x
  · exact rowEval3992 x
  · exact rowEval3993 x
  · exact rowEval3994 x
  · exact rowEval3995 x
  · exact rowEval3996 x
  · exact rowEval3997 x
  · exact rowEval3998 x
  · exact rowEval3999 x
  · exact rowEval4000 x
  · exact rowEval4001 x
  · exact rowEval4002 x
  · exact rowEval4003 x

theorem entryEval17_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_9 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck17_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_9]

def rows17_10 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4004, row4005, row4006, row4007, row4008, row4009, row4010, row4011, row4012, row4013, row4014, row4015, row4016, row4017, row4018, row4019, row4020, row4021, row4022, row4023, row4024, row4025, row4026, row4027, row4028, row4029, row4030, row4031, row4032, row4033]

theorem entryCheck17_10 : entry17_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_10 k)) := by decide +kernel

theorem rowsSound17_10 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval4004 x
  · exact rowEval4005 x
  · exact rowEval4006 x
  · exact rowEval4007 x
  · exact rowEval4008 x
  · exact rowEval4009 x
  · exact rowEval4010 x
  · exact rowEval4011 x
  · exact rowEval4012 x
  · exact rowEval4013 x
  · exact rowEval4014 x
  · exact rowEval4015 x
  · exact rowEval4016 x
  · exact rowEval4017 x
  · exact rowEval4018 x
  · exact rowEval4019 x
  · exact rowEval4020 x
  · exact rowEval4021 x
  · exact rowEval4022 x
  · exact rowEval4023 x
  · exact rowEval4024 x
  · exact rowEval4025 x
  · exact rowEval4026 x
  · exact rowEval4027 x
  · exact rowEval4028 x
  · exact rowEval4029 x
  · exact rowEval4030 x
  · exact rowEval4031 x
  · exact rowEval4032 x
  · exact rowEval4033 x

theorem entryEval17_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_10 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck17_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_10]

def rows17_11 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4034, row4035, row4036, row4037, row4038, row4039, row4040, row4041, row4042, row4043, row4044, row4045, row4046, row4047, row4048, row4049, row4050, row4051, row4052, row4053, row4054, row4055, row4056, row4057, row4058, row4059, row4060, row4061, row4062, row4063]

theorem entryCheck17_11 : entry17_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_11 k)) := by decide +kernel

theorem rowsSound17_11 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval4034 x
  · exact rowEval4035 x
  · exact rowEval4036 x
  · exact rowEval4037 x
  · exact rowEval4038 x
  · exact rowEval4039 x
  · exact rowEval4040 x
  · exact rowEval4041 x
  · exact rowEval4042 x
  · exact rowEval4043 x
  · exact rowEval4044 x
  · exact rowEval4045 x
  · exact rowEval4046 x
  · exact rowEval4047 x
  · exact rowEval4048 x
  · exact rowEval4049 x
  · exact rowEval4050 x
  · exact rowEval4051 x
  · exact rowEval4052 x
  · exact rowEval4053 x
  · exact rowEval4054 x
  · exact rowEval4055 x
  · exact rowEval4056 x
  · exact rowEval4057 x
  · exact rowEval4058 x
  · exact rowEval4059 x
  · exact rowEval4060 x
  · exact rowEval4061 x
  · exact rowEval4062 x
  · exact rowEval4063 x

theorem entryEval17_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck17_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_11]

def rows17_12 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4064, row4065, row4066, row4067, row4068, row4069, row4070, row4071, row4072, row4073, row4074, row4075, row4076, row4077, row4078, row4079, row4080, row4081, row4082, row4083, row4084, row4085, row4086, row4087, row4088, row4089, row4090, row4091, row4092, row4093]

theorem entryCheck17_12 : entry17_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_12 k)) := by decide +kernel

theorem rowsSound17_12 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval4064 x
  · exact rowEval4065 x
  · exact rowEval4066 x
  · exact rowEval4067 x
  · exact rowEval4068 x
  · exact rowEval4069 x
  · exact rowEval4070 x
  · exact rowEval4071 x
  · exact rowEval4072 x
  · exact rowEval4073 x
  · exact rowEval4074 x
  · exact rowEval4075 x
  · exact rowEval4076 x
  · exact rowEval4077 x
  · exact rowEval4078 x
  · exact rowEval4079 x
  · exact rowEval4080 x
  · exact rowEval4081 x
  · exact rowEval4082 x
  · exact rowEval4083 x
  · exact rowEval4084 x
  · exact rowEval4085 x
  · exact rowEval4086 x
  · exact rowEval4087 x
  · exact rowEval4088 x
  · exact rowEval4089 x
  · exact rowEval4090 x
  · exact rowEval4091 x
  · exact rowEval4092 x
  · exact rowEval4093 x

theorem entryEval17_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_12 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck17_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_12]

def rows17_13 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4094, row4095, row4096, row4097, row4098, row4099, row4100, row4101, row4102, row4103, row4104, row4105, row4106, row4107, row4108, row4109, row4110, row4111, row4112, row4113, row4114, row4115, row4116, row4117, row4118, row4119, row4120, row4121, row4122, row4123]

theorem entryCheck17_13 : entry17_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_13 k)) := by decide +kernel

theorem rowsSound17_13 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval4094 x
  · exact rowEval4095 x
  · exact rowEval4096 x
  · exact rowEval4097 x
  · exact rowEval4098 x
  · exact rowEval4099 x
  · exact rowEval4100 x
  · exact rowEval4101 x
  · exact rowEval4102 x
  · exact rowEval4103 x
  · exact rowEval4104 x
  · exact rowEval4105 x
  · exact rowEval4106 x
  · exact rowEval4107 x
  · exact rowEval4108 x
  · exact rowEval4109 x
  · exact rowEval4110 x
  · exact rowEval4111 x
  · exact rowEval4112 x
  · exact rowEval4113 x
  · exact rowEval4114 x
  · exact rowEval4115 x
  · exact rowEval4116 x
  · exact rowEval4117 x
  · exact rowEval4118 x
  · exact rowEval4119 x
  · exact rowEval4120 x
  · exact rowEval4121 x
  · exact rowEval4122 x
  · exact rowEval4123 x

theorem entryEval17_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_13 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck17_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_13]

def rows17_14 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4124, row4125, row4126, row4127, row4128, row4129, row4130, row4131, row4132, row4133, row4134, row4135, row4136, row4137, row4138, row4139, row4140, row4141, row4142, row4143, row4144, row4145, row4146, row4147, row4148, row4149, row4150, row4151, row4152, row4153]

theorem entryCheck17_14 : entry17_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_14 k)) := by decide +kernel

theorem rowsSound17_14 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval4124 x
  · exact rowEval4125 x
  · exact rowEval4126 x
  · exact rowEval4127 x
  · exact rowEval4128 x
  · exact rowEval4129 x
  · exact rowEval4130 x
  · exact rowEval4131 x
  · exact rowEval4132 x
  · exact rowEval4133 x
  · exact rowEval4134 x
  · exact rowEval4135 x
  · exact rowEval4136 x
  · exact rowEval4137 x
  · exact rowEval4138 x
  · exact rowEval4139 x
  · exact rowEval4140 x
  · exact rowEval4141 x
  · exact rowEval4142 x
  · exact rowEval4143 x
  · exact rowEval4144 x
  · exact rowEval4145 x
  · exact rowEval4146 x
  · exact rowEval4147 x
  · exact rowEval4148 x
  · exact rowEval4149 x
  · exact rowEval4150 x
  · exact rowEval4151 x
  · exact rowEval4152 x
  · exact rowEval4153 x

theorem entryEval17_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_14 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck17_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_14]

def rows17_15 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4154, row4155, row4156, row4157, row4158, row4159, row4160, row4161, row4162, row4163, row4164, row4165, row4166, row4167, row4168, row4169, row4170, row4171, row4172, row4173, row4174, row4175, row4176, row4177, row4178, row4179, row4180, row4181, row4182, row4183]

theorem entryCheck17_15 : entry17_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_15 k)) := by decide +kernel

theorem rowsSound17_15 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval4154 x
  · exact rowEval4155 x
  · exact rowEval4156 x
  · exact rowEval4157 x
  · exact rowEval4158 x
  · exact rowEval4159 x
  · exact rowEval4160 x
  · exact rowEval4161 x
  · exact rowEval4162 x
  · exact rowEval4163 x
  · exact rowEval4164 x
  · exact rowEval4165 x
  · exact rowEval4166 x
  · exact rowEval4167 x
  · exact rowEval4168 x
  · exact rowEval4169 x
  · exact rowEval4170 x
  · exact rowEval4171 x
  · exact rowEval4172 x
  · exact rowEval4173 x
  · exact rowEval4174 x
  · exact rowEval4175 x
  · exact rowEval4176 x
  · exact rowEval4177 x
  · exact rowEval4178 x
  · exact rowEval4179 x
  · exact rowEval4180 x
  · exact rowEval4181 x
  · exact rowEval4182 x
  · exact rowEval4183 x

theorem entryEval17_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_15 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck17_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_15]

def rows17_16 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4184, row4185, row4186, row4187, row4188, row4189, row4190, row4191, row4192, row4193, row4194, row4195, row4196, row4197, row4198, row4199, row4200, row4201, row4202, row4203, row4204, row4205, row4206, row4207, row4208, row4209, row4210, row4211, row4212, row4213]

theorem entryCheck17_16 : entry17_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_16 k)) := by decide +kernel

theorem rowsSound17_16 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form16) x := by
  fin_cases k
  · exact rowEval4184 x
  · exact rowEval4185 x
  · exact rowEval4186 x
  · exact rowEval4187 x
  · exact rowEval4188 x
  · exact rowEval4189 x
  · exact rowEval4190 x
  · exact rowEval4191 x
  · exact rowEval4192 x
  · exact rowEval4193 x
  · exact rowEval4194 x
  · exact rowEval4195 x
  · exact rowEval4196 x
  · exact rowEval4197 x
  · exact rowEval4198 x
  · exact rowEval4199 x
  · exact rowEval4200 x
  · exact rowEval4201 x
  · exact rowEval4202 x
  · exact rowEval4203 x
  · exact rowEval4204 x
  · exact rowEval4205 x
  · exact rowEval4206 x
  · exact rowEval4207 x
  · exact rowEval4208 x
  · exact rowEval4209 x
  · exact rowEval4210 x
  · exact rowEval4211 x
  · exact rowEval4212 x
  · exact rowEval4213 x

theorem entryEval17_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_16 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form16 B := by
  rw [entryCheck17_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_16]

def rows17_17 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4214, row4215, row4216, row4217, row4218, row4219, row4220, row4221, row4222, row4223, row4224, row4225, row4226, row4227, row4228, row4229, row4230, row4231, row4232, row4233, row4234, row4235, row4236, row4237, row4238, row4239, row4240, row4241, row4242, row4243]

theorem entryCheck17_17 : entry17_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form17.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form17.terms k).coefficient) (rows17_17 k)) := by decide +kernel

theorem rowsSound17_17 (k : Fin GramFunctions.Block1.form17.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows17_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form17.terms k).tag (GramFunctions.Block1.form17.terms k).charge GramFunctions.Block1.form17) x := by
  fin_cases k
  · exact rowEval4214 x
  · exact rowEval4215 x
  · exact rowEval4216 x
  · exact rowEval4217 x
  · exact rowEval4218 x
  · exact rowEval4219 x
  · exact rowEval4220 x
  · exact rowEval4221 x
  · exact rowEval4222 x
  · exact rowEval4223 x
  · exact rowEval4224 x
  · exact rowEval4225 x
  · exact rowEval4226 x
  · exact rowEval4227 x
  · exact rowEval4228 x
  · exact rowEval4229 x
  · exact rowEval4230 x
  · exact rowEval4231 x
  · exact rowEval4232 x
  · exact rowEval4233 x
  · exact rowEval4234 x
  · exact rowEval4235 x
  · exact rowEval4236 x
  · exact rowEval4237 x
  · exact rowEval4238 x
  · exact rowEval4239 x
  · exact rowEval4240 x
  · exact rowEval4241 x
  · exact rowEval4242 x
  · exact rowEval4243 x

theorem entryEval17_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_17 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form17 B := by
  rw [entryCheck17_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form17 GramFunctions.Block1.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound17_17]

end MUB6.Certificate.GramEntries.Block1

end OAI
