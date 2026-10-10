import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource800 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3736 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3823 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))))))))))

def numericRow800 : Integer.Sparse Master := [(Sum.inl 0, -36), (Sum.inl 2, 5), (Sum.inl 3, 40), (Sum.inl 12, 40), (Sum.inl 1, 5), (Sum.inr 2023, 360), (Sum.inr 2025, 360), (Sum.inr 2028, 360), (Sum.inr 2058, 360), (Sum.inr 2245, 360), (Sum.inr 2924, 360), (Sum.inr 2931, 360), (Sum.inr 3692, 360), (Sum.inr 3693, 360), (Sum.inr 3706, 360), (Sum.inr 3719, 360), (Sum.inr 3782, 360), (Sum.inr 3801, 360), (Sum.inr 3849, 360), (Sum.inr 3850, 360), (Sum.inr 3857, 360), (Sum.inr 3910, 360)]

theorem reindexCheck800 : Integer.Sparse.reindex keyMap MixedData.row800 = numericRow800 := by decide +kernel

theorem numericCheck800 (x : Master → ℝ) : Integer.Sparse.eval numericRow800 x =
    (360 : ℝ) * reducedSource800 x := by
  norm_num [numericRow800, reducedSource800, Integer.Sparse.eval, Sparse.eval, nodeValue2023, nodeValue2025, nodeValue2028, nodeValue2058, nodeValue2245, nodeValue2924, nodeValue2931, nodeValue2959, nodeValue3101, nodeValue3692, nodeValue3693, nodeValue3706, nodeValue3719, nodeValue3736, nodeValue3782, nodeValue3801, nodeValue3823, nodeValue3849, nodeValue3850, nodeValue3853, nodeValue3857, nodeValue3862, nodeValue3910, nodeValue3912, nodeValue3982, nodeValue4013, nodeValue4033, nodeValue4036, nodeValue4040]; ring

noncomputable def reducedSource801 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + 0)))))))))))))))

def numericRow801 : Integer.Sparse Master := [(Sum.inl 0, 96), (Sum.inl 2, 45), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, -15), (Sum.inr 2739, -4320), (Sum.inr 3534, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -4320), (Sum.inr 3812, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -2160), (Sum.inr 3907, -4320), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5299, 17280), (Sum.inr 5425, 17280), (Sum.inr 5426, 8640)]

theorem reindexCheck801 : Integer.Sparse.reindex keyMap MixedData.row801 = numericRow801 := by decide +kernel

theorem numericCheck801 (x : Master → ℝ) : Integer.Sparse.eval numericRow801 x =
    (8640 : ℝ) * reducedSource801 x := by
  norm_num [numericRow801, reducedSource801, Integer.Sparse.eval, Sparse.eval, nodeValue5265, nodeValue5266, nodeValue5267, nodeValue5271, nodeValue5299, nodeValue5406, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5424, nodeValue5425, nodeValue5426, nodeValue5434, nodeValue5435, nodeValue5442, nodeValue5443]; ring

noncomputable def reducedSource802 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2392 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2394 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3347 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3714 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

def numericRow802 : Integer.Sparse Master := [(Sum.inl 0, -224), (Sum.inl 2, -150), (Sum.inl 3, -160), (Sum.inl 12, 320), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -110), (Sum.inr 2392, 8640), (Sum.inr 2393, 8640), (Sum.inr 2394, 8640), (Sum.inr 2405, 8640), (Sum.inr 2732, 8640), (Sum.inr 2909, 8640), (Sum.inr 2910, 8640), (Sum.inr 2955, 8640), (Sum.inr 3055, 8640), (Sum.inr 3347, 8640), (Sum.inr 3348, 8640), (Sum.inr 3358, 8640), (Sum.inr 3541, 8640), (Sum.inr 3559, 8640), (Sum.inr 3565, 8640), (Sum.inr 3584, 8640), (Sum.inr 3714, 8640), (Sum.inr 3733, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3949, 8640)]

theorem reindexCheck802 : Integer.Sparse.reindex keyMap MixedData.row802 = numericRow802 := by decide +kernel

theorem numericCheck802 (x : Master → ℝ) : Integer.Sparse.eval numericRow802 x =
    (8640 : ℝ) * reducedSource802 x := by
  norm_num [numericRow802, reducedSource802, Integer.Sparse.eval, Sparse.eval, nodeValue2392, nodeValue2393, nodeValue2394, nodeValue2405, nodeValue2732, nodeValue2909, nodeValue2910, nodeValue2955, nodeValue3055, nodeValue3347, nodeValue3348, nodeValue3358, nodeValue3541, nodeValue3559, nodeValue3565, nodeValue3584, nodeValue3714, nodeValue3733, nodeValue3839, nodeValue3845, nodeValue3862, nodeValue3868, nodeValue3869, nodeValue3872, nodeValue3876, nodeValue3877, nodeValue3889, nodeValue3949, nodeValue3993, nodeValue4003]; ring

noncomputable def reducedSource803 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow803 : Integer.Sparse Master := [(Sum.inr 2591, 1), (Sum.inr 3733, 1), (Sum.inr 3819, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

theorem reindexCheck803 : Integer.Sparse.reindex keyMap MixedData.row803 = numericRow803 := by decide +kernel

theorem numericCheck803 (x : Master → ℝ) : Integer.Sparse.eval numericRow803 x =
    (1 : ℝ) * reducedSource803 x := by
  norm_num [numericRow803, reducedSource803, Integer.Sparse.eval, Sparse.eval, nodeValue2591, nodeValue3733, nodeValue3819, nodeValue3845, nodeValue3854, nodeValue3857, nodeValue4092]

noncomputable def reducedSource804 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

def numericRow804 : Integer.Sparse Master := [(Sum.inl 0, -500), (Sum.inl 5, -80), (Sum.inl 2, -200), (Sum.inl 51, 960), (Sum.inl 3, -1920), (Sum.inl 13, -640), (Sum.inl 55, 960), (Sum.inl 12, -320), (Sum.inl 4, -960), (Sum.inl 27, 240), (Sum.inl 1, 300), (Sum.inl 31, 960), (Sum.inr 2031, 17280), (Sum.inr 2032, 17280), (Sum.inr 2039, 17280), (Sum.inr 2049, 17280), (Sum.inr 2251, 17280), (Sum.inr 2606, 17280), (Sum.inr 2608, 17280), (Sum.inr 2632, 17280), (Sum.inr 2677, 17280), (Sum.inr 3527, 17280), (Sum.inr 3538, 17280), (Sum.inr 3540, 17280), (Sum.inr 3575, 17280), (Sum.inr 3696, 17280), (Sum.inr 3699, 17280), (Sum.inr 3780, 17280), (Sum.inr 3802, 17280), (Sum.inr 3811, 17280), (Sum.inr 3813, 17280), (Sum.inr 3827, 17280), (Sum.inr 3834, 17280), (Sum.inr 3840, 17280), (Sum.inr 3846, 17280), (Sum.inr 3850, 17280), (Sum.inr 3881, 34560)]

theorem reindexCheck804 : Integer.Sparse.reindex keyMap MixedData.row804 = numericRow804 := by decide +kernel

theorem numericCheck804 (x : Master → ℝ) : Integer.Sparse.eval numericRow804 x =
    (17280 : ℝ) * reducedSource804 x := by
  norm_num [numericRow804, reducedSource804, Integer.Sparse.eval, Sparse.eval, nodeValue2031, nodeValue2032, nodeValue2039, nodeValue2049, nodeValue2251, nodeValue2606, nodeValue2608, nodeValue2632, nodeValue2677, nodeValue3527, nodeValue3538, nodeValue3540, nodeValue3575, nodeValue3696, nodeValue3699, nodeValue3780, nodeValue3802, nodeValue3811, nodeValue3813, nodeValue3827, nodeValue3831, nodeValue3834, nodeValue3840, nodeValue3846, nodeValue3850, nodeValue3852, nodeValue3856, nodeValue3881, nodeValue3995]; ring

noncomputable def reducedSource805 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3374 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

def numericRow805 : Integer.Sparse Master := [(Sum.inl 0, -351), (Sum.inl 5, -60), (Sum.inl 2, -225), (Sum.inl 3, -1680), (Sum.inl 13, -240), (Sum.inl 23, 720), (Sum.inl 54, 720), (Sum.inl 12, -720), (Sum.inl 25, 1440), (Sum.inl 26, -240), (Sum.inl 4, -720), (Sum.inl 27, 180), (Sum.inl 1, 330), (Sum.inr 2078, 12960), (Sum.inr 2080, 12960), (Sum.inr 2081, 12960), (Sum.inr 2108, 12960), (Sum.inr 2217, 12960), (Sum.inr 2860, 12960), (Sum.inr 2867, 12960), (Sum.inr 2876, 12960), (Sum.inr 3086, 12960), (Sum.inr 3374, 12960), (Sum.inr 3379, 12960), (Sum.inr 3386, 12960), (Sum.inr 3570, 12960), (Sum.inr 3722, 12960), (Sum.inr 3752, 12960), (Sum.inr 3762, 12960), (Sum.inr 3771, 12960), (Sum.inr 3772, 12960), (Sum.inr 3788, 12960), (Sum.inr 3814, 12960), (Sum.inr 3872, 12960), (Sum.inr 3873, 12960), (Sum.inr 3884, 12960), (Sum.inr 3954, 12960), (Sum.inr 3958, 12960), (Sum.inr 3959, 12960)]

theorem reindexCheck805 : Integer.Sparse.reindex keyMap MixedData.row805 = numericRow805 := by decide +kernel

theorem numericCheck805 (x : Master → ℝ) : Integer.Sparse.eval numericRow805 x =
    (12960 : ℝ) * reducedSource805 x := by
  norm_num [numericRow805, reducedSource805, Integer.Sparse.eval, Sparse.eval, nodeValue2078, nodeValue2080, nodeValue2081, nodeValue2108, nodeValue2217, nodeValue2860, nodeValue2867, nodeValue2876, nodeValue3086, nodeValue3374, nodeValue3379, nodeValue3386, nodeValue3570, nodeValue3722, nodeValue3738, nodeValue3752, nodeValue3762, nodeValue3771, nodeValue3772, nodeValue3788, nodeValue3814, nodeValue3872, nodeValue3873, nodeValue3883, nodeValue3884, nodeValue3954, nodeValue3958, nodeValue3959, nodeValue3982, nodeValue4027]; ring

noncomputable def reducedSource806 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2872 x + ((1 : ℝ) * Sparse.eval nodeValue3175 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow806 : Integer.Sparse Master := [(Sum.inr 2619, 1), (Sum.inr 2872, 1), (Sum.inr 3175, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem reindexCheck806 : Integer.Sparse.reindex keyMap MixedData.row806 = numericRow806 := by decide +kernel

theorem numericCheck806 (x : Master → ℝ) : Integer.Sparse.eval numericRow806 x =
    (1 : ℝ) * reducedSource806 x := by
  norm_num [numericRow806, reducedSource806, Integer.Sparse.eval, Sparse.eval, nodeValue2619, nodeValue2872, nodeValue3175, nodeValue3180, nodeValue3198, nodeValue3877, nodeValue4092]

noncomputable def reducedSource807 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow807 : Integer.Sparse Master := [(Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 3788, 1), (Sum.inr 3809, 1), (Sum.inr 3877, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem reindexCheck807 : Integer.Sparse.reindex keyMap MixedData.row807 = numericRow807 := by decide +kernel

theorem numericCheck807 (x : Master → ℝ) : Integer.Sparse.eval numericRow807 x =
    (1 : ℝ) * reducedSource807 x := by
  norm_num [numericRow807, reducedSource807, Integer.Sparse.eval, Sparse.eval, nodeValue3180, nodeValue3732, nodeValue3788, nodeValue3809, nodeValue3877, nodeValue3959, nodeValue4092]

noncomputable def reducedSource808 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2873 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow808 : Integer.Sparse Master := [(Sum.inr 2634, 1), (Sum.inr 2873, 1), (Sum.inr 3699, 1), (Sum.inr 3828, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem reindexCheck808 : Integer.Sparse.reindex keyMap MixedData.row808 = numericRow808 := by decide +kernel

theorem numericCheck808 (x : Master → ℝ) : Integer.Sparse.eval numericRow808 x =
    (1 : ℝ) * reducedSource808 x := by
  norm_num [numericRow808, reducedSource808, Integer.Sparse.eval, Sparse.eval, nodeValue2634, nodeValue2873, nodeValue3699, nodeValue3828, nodeValue3877, nodeValue3884, nodeValue4092]

noncomputable def reducedSource809 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2870 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow809 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2870, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3874, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem reindexCheck809 : Integer.Sparse.reindex keyMap MixedData.row809 = numericRow809 := by decide +kernel

theorem numericCheck809 (x : Master → ℝ) : Integer.Sparse.eval numericRow809 x =
    (1 : ℝ) * reducedSource809 x := by
  norm_num [numericRow809, reducedSource809, Integer.Sparse.eval, Sparse.eval, nodeValue2616, nodeValue2870, nodeValue3698, nodeValue3788, nodeValue3874, nodeValue3877, nodeValue4092]

noncomputable def reducedSource810 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow810 : Integer.Sparse Master := [(Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem reindexCheck810 : Integer.Sparse.reindex keyMap MixedData.row810 = numericRow810 := by decide +kernel

theorem numericCheck810 (x : Master → ℝ) : Integer.Sparse.eval numericRow810 x =
    (1 : ℝ) * reducedSource810 x := by
  norm_num [numericRow810, reducedSource810, Integer.Sparse.eval, Sparse.eval, nodeValue2885, nodeValue3706, nodeValue3877, nodeValue3946, nodeValue3959, nodeValue3961, nodeValue4092]

noncomputable def reducedSource811 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow811 : Integer.Sparse Master := [(Sum.inr 3198, 1), (Sum.inr 3698, 1), (Sum.inr 3699, 1), (Sum.inr 3706, 1), (Sum.inr 3814, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem reindexCheck811 : Integer.Sparse.reindex keyMap MixedData.row811 = numericRow811 := by decide +kernel

theorem numericCheck811 (x : Master → ℝ) : Integer.Sparse.eval numericRow811 x =
    (1 : ℝ) * reducedSource811 x := by
  norm_num [numericRow811, reducedSource811, Integer.Sparse.eval, Sparse.eval, nodeValue3198, nodeValue3698, nodeValue3699, nodeValue3706, nodeValue3814, nodeValue3877, nodeValue4092]

noncomputable def reducedSource812 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow812 : Integer.Sparse Master := [(Sum.inr 2620, 1), (Sum.inr 3045, 1), (Sum.inr 3723, 1), (Sum.inr 3732, 1), (Sum.inr 3850, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem reindexCheck812 : Integer.Sparse.reindex keyMap MixedData.row812 = numericRow812 := by decide +kernel

theorem numericCheck812 (x : Master → ℝ) : Integer.Sparse.eval numericRow812 x =
    (1 : ℝ) * reducedSource812 x := by
  norm_num [numericRow812, reducedSource812, Integer.Sparse.eval, Sparse.eval, nodeValue2620, nodeValue3045, nodeValue3723, nodeValue3732, nodeValue3850, nodeValue3877, nodeValue4092]

noncomputable def reducedSource813 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4746 x + ((2 : ℝ) * Sparse.eval nodeValue4747 x + ((1 : ℝ) * Sparse.eval nodeValue4749 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5155 x + ((2 : ℝ) * Sparse.eval nodeValue5156 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5328 x + ((1 : ℝ) * Sparse.eval nodeValue5329 x + ((1 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((3 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))))))))

def numericRow813 : Integer.Sparse Master := [(Sum.inl 0, 127), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 240), (Sum.inl 1, 770), (Sum.inr 1925, -4320), (Sum.inr 1926, -4320), (Sum.inr 1928, -4320), (Sum.inr 1948, -4320), (Sum.inr 2279, -4320), (Sum.inr 2908, -4320), (Sum.inr 2911, -4320), (Sum.inr 2954, -4320), (Sum.inr 3054, -4320), (Sum.inr 3600, -4320), (Sum.inr 3606, -4320), (Sum.inr 3611, -4320), (Sum.inr 3626, -4320), (Sum.inr 3659, -4320), (Sum.inr 3660, -4320), (Sum.inr 3713, -4320), (Sum.inr 3732, -4320), (Sum.inr 3789, -4320), (Sum.inr 3810, -4320), (Sum.inr 3811, -4320), (Sum.inr 3814, -12960), (Sum.inr 3899, -4320), (Sum.inr 3902, -4320), (Sum.inr 3907, -4320)]

theorem reindexCheck813 : Integer.Sparse.reindex keyMap MixedData.row813 = numericRow813 := by decide +kernel

theorem numericCheck813 (x : Master → ℝ) : Integer.Sparse.eval numericRow813 x =
    (8640 : ℝ) * reducedSource813 x := by
  norm_num [numericRow813, reducedSource813, Integer.Sparse.eval, Sparse.eval, nodeValue4746, nodeValue4747, nodeValue4749, nodeValue4898, nodeValue5155, nodeValue5156, nodeValue5170, nodeValue5302, nodeValue5328, nodeValue5329, nodeValue5374, nodeValue5384, nodeValue5403, nodeValue5412, nodeValue5437, nodeValue5439, nodeValue5443, nodeValue5453, nodeValue5456]; ring

noncomputable def reducedSource814 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4817 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5287 x + ((2 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5407 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((3 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + 0)))))))))))))))))))))))))

def numericRow814 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 2515, -4320), (Sum.inr 3479, -4320), (Sum.inr 3706, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3796, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -12960), (Sum.inr 3812, -4320), (Sum.inr 3813, -12960), (Sum.inr 3814, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4816, 17280), (Sum.inr 4817, 17280), (Sum.inr 4821, 17280), (Sum.inr 4836, 17280), (Sum.inr 4891, 17280), (Sum.inr 5086, 17280), (Sum.inr 5090, 17280), (Sum.inr 5254, 17280), (Sum.inr 5260, 17280), (Sum.inr 5267, 34560), (Sum.inr 5287, 17280), (Sum.inr 5360, 34560), (Sum.inr 5361, 17280), (Sum.inr 5407, 17280), (Sum.inr 5425, 17280), (Sum.inr 5426, 17280), (Sum.inr 5436, 17280)]

theorem reindexCheck814 : Integer.Sparse.reindex keyMap MixedData.row814 = numericRow814 := by decide +kernel

theorem numericCheck814 (x : Master → ℝ) : Integer.Sparse.eval numericRow814 x =
    (17280 : ℝ) * reducedSource814 x := by
  norm_num [numericRow814, reducedSource814, Integer.Sparse.eval, Sparse.eval, nodeValue4816, nodeValue4817, nodeValue4821, nodeValue4836, nodeValue4891, nodeValue5086, nodeValue5090, nodeValue5105, nodeValue5254, nodeValue5260, nodeValue5267, nodeValue5287, nodeValue5360, nodeValue5361, nodeValue5370, nodeValue5397, nodeValue5406, nodeValue5407, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5425, nodeValue5426, nodeValue5434, nodeValue5435, nodeValue5436]; ring

noncomputable def reducedSource815 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))))))))))

def numericRow815 : Integer.Sparse Master := [(Sum.inl 0, -124), (Sum.inl 2, -95), (Sum.inl 3, -640), (Sum.inl 13, -240), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, 265), (Sum.inr 2196, 4320), (Sum.inr 2197, 4320), (Sum.inr 2207, 4320), (Sum.inr 2217, 4320), (Sum.inr 2253, 4320), (Sum.inr 3016, 4320), (Sum.inr 3025, 4320), (Sum.inr 3038, 4320), (Sum.inr 3086, 4320), (Sum.inr 3464, 4320), (Sum.inr 3479, 4320), (Sum.inr 3480, 4320), (Sum.inr 3541, 4320), (Sum.inr 3762, 8640), (Sum.inr 3771, 4320), (Sum.inr 3772, 4320), (Sum.inr 3796, 4320), (Sum.inr 3801, 4320), (Sum.inr 3803, 4320), (Sum.inr 3809, 4320), (Sum.inr 3813, 4320), (Sum.inr 3841, 4320), (Sum.inr 3872, 4320), (Sum.inr 3877, 4320)]

theorem reindexCheck815 : Integer.Sparse.reindex keyMap MixedData.row815 = numericRow815 := by decide +kernel

theorem numericCheck815 (x : Master → ℝ) : Integer.Sparse.eval numericRow815 x =
    (4320 : ℝ) * reducedSource815 x := by
  norm_num [numericRow815, reducedSource815, Integer.Sparse.eval, Sparse.eval, nodeValue2196, nodeValue2197, nodeValue2207, nodeValue2217, nodeValue2253, nodeValue3016, nodeValue3025, nodeValue3038, nodeValue3086, nodeValue3464, nodeValue3479, nodeValue3480, nodeValue3541, nodeValue3762, nodeValue3771, nodeValue3772, nodeValue3796, nodeValue3801, nodeValue3803, nodeValue3808, nodeValue3809, nodeValue3813, nodeValue3841, nodeValue3853, nodeValue3856, nodeValue3872, nodeValue3877, nodeValue3883, nodeValue3982]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
