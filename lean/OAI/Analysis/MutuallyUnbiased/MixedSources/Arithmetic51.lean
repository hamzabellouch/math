import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
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

noncomputable def reducedSource816 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4992 x + ((1 : ℝ) * Sparse.eval nodeValue4993 x + ((2 : ℝ) * Sparse.eval nodeValue4999 x + ((1 : ℝ) * Sparse.eval nodeValue5004 x + ((2 : ℝ) * Sparse.eval nodeValue5005 x + ((1 : ℝ) * Sparse.eval nodeValue5011 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

def numericRow816 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 90), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3902, -4320), (Sum.inr 3910, -4320), (Sum.inr 3957, -8640), (Sum.inr 4992, 17280), (Sum.inr 4993, 17280), (Sum.inr 4999, 34560), (Sum.inr 5004, 17280), (Sum.inr 5005, 34560), (Sum.inr 5011, 17280), (Sum.inr 5145, 34560), (Sum.inr 5251, 17280), (Sum.inr 5265, 17280), (Sum.inr 5282, 17280), (Sum.inr 5379, 34560), (Sum.inr 5414, 17280), (Sum.inr 5421, 34560), (Sum.inr 5446, 34560), (Sum.inr 5470, 34560)]

theorem reindexCheck816 : Integer.Sparse.reindex keyMap MixedData.row816 = numericRow816 := by decide +kernel

theorem numericCheck816 (x : Master → ℝ) : Integer.Sparse.eval numericRow816 x =
    (17280 : ℝ) * reducedSource816 x := by
  norm_num [numericRow816, reducedSource816, Integer.Sparse.eval, Sparse.eval, nodeValue4992, nodeValue4993, nodeValue4999, nodeValue5004, nodeValue5005, nodeValue5011, nodeValue5145, nodeValue5251, nodeValue5265, nodeValue5282, nodeValue5379, nodeValue5414, nodeValue5421, nodeValue5424, nodeValue5431, nodeValue5439, nodeValue5446, nodeValue5450, nodeValue5470, nodeValue5472, nodeValue5481]
  ring

noncomputable def reducedSource817 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2378 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2384 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2912 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3337 x + ((2 : ℝ) * Sparse.eval nodeValue3342 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3946 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

def numericRow817 : Integer.Sparse Master := [(Sum.inl 0, -93), (Sum.inl 2, 155), (Sum.inl 3, 2000), (Sum.inl 12, 800), (Sum.inl 25, -480), (Sum.inl 26, 480), (Sum.inl 4, 1120), (Sum.inl 1, -820), (Sum.inr 2378, 4320), (Sum.inr 2379, 4320), (Sum.inr 2384, 8640), (Sum.inr 2710, 4320), (Sum.inr 2912, 4320), (Sum.inr 2925, 8640), (Sum.inr 3078, 4320), (Sum.inr 3337, 4320), (Sum.inr 3342, 8640), (Sum.inr 3526, 4320), (Sum.inr 3720, 8640), (Sum.inr 3869, 4320), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3957, 4320), (Sum.inr 3959, 8640)]

theorem reindexCheck817 : Integer.Sparse.reindex keyMap MixedData.row817 = numericRow817 := by decide +kernel

theorem numericCheck817 (x : Master → ℝ) : Integer.Sparse.eval numericRow817 x =
    (4320 : ℝ) * reducedSource817 x := by
  norm_num [numericRow817, reducedSource817, Integer.Sparse.eval, Sparse.eval, nodeValue2378, nodeValue2379, nodeValue2384, nodeValue2710, nodeValue2912, nodeValue2925, nodeValue3078, nodeValue3337, nodeValue3342, nodeValue3526, nodeValue3720, nodeValue3869, nodeValue3946, nodeValue3955, nodeValue3957, nodeValue3959, nodeValue3979, nodeValue3990, nodeValue4012, nodeValue4026, nodeValue4029]
  ring

noncomputable def reducedSource818 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2389 x + ((2 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((2 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((2 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

def numericRow818 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 95), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 4, 160), (Sum.inl 1, -410), (Sum.inl 31, -480), (Sum.inr 2389, 4320), (Sum.inr 2390, 8640), (Sum.inr 2396, 4320), (Sum.inr 2730, 4320), (Sum.inr 3345, 4320), (Sum.inr 3346, 8640), (Sum.inr 3350, 4320), (Sum.inr 3539, 4320), (Sum.inr 3562, 8640), (Sum.inr 3580, 4320), (Sum.inr 3819, 4320), (Sum.inr 3832, 8640), (Sum.inr 3843, 8640), (Sum.inr 3873, 8640), (Sum.inr 3875, 8640), (Sum.inr 3884, 8640), (Sum.inr 3947, 8640)]

theorem reindexCheck818 : Integer.Sparse.reindex keyMap MixedData.row818 = numericRow818 := by decide +kernel

theorem numericCheck818 (x : Master → ℝ) : Integer.Sparse.eval numericRow818 x =
    (4320 : ℝ) * reducedSource818 x := by
  norm_num [numericRow818, reducedSource818, Integer.Sparse.eval, Sparse.eval, nodeValue2389, nodeValue2390, nodeValue2396, nodeValue2730, nodeValue3345, nodeValue3346, nodeValue3350, nodeValue3539, nodeValue3562, nodeValue3580, nodeValue3819, nodeValue3832, nodeValue3843, nodeValue3858, nodeValue3873, nodeValue3875, nodeValue3884, nodeValue3887, nodeValue3947, nodeValue3991, nodeValue4002]
  ring

noncomputable def reducedSource819 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow819 : Integer.Sparse Master := [(Sum.inr 3846, 1), (Sum.inr 3947, 2), (Sum.inr 3949, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem reindexCheck819 : Integer.Sparse.reindex keyMap MixedData.row819 = numericRow819 := by decide +kernel

theorem numericCheck819 (x : Master → ℝ) : Integer.Sparse.eval numericRow819 x =
    (1 : ℝ) * reducedSource819 x := by
  norm_num [numericRow819, reducedSource819, Integer.Sparse.eval, Sparse.eval, nodeValue3846, nodeValue3947, nodeValue3949, nodeValue3957, nodeValue4008, nodeValue4091]

noncomputable def reducedSource820 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow820 : Integer.Sparse Master := [(Sum.inr 2567, 1), (Sum.inr 3724, 1), (Sum.inr 3827, 1), (Sum.inr 3838, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

theorem reindexCheck820 : Integer.Sparse.reindex keyMap MixedData.row820 = numericRow820 := by decide +kernel

theorem numericCheck820 (x : Master → ℝ) : Integer.Sparse.eval numericRow820 x =
    (1 : ℝ) * reducedSource820 x := by
  norm_num [numericRow820, reducedSource820, Integer.Sparse.eval, Sparse.eval, nodeValue2567, nodeValue3724, nodeValue3827, nodeValue3838, nodeValue3846, nodeValue3849, nodeValue4091]

noncomputable def reducedSource821 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4791 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue5181 x + ((2 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5350 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))

def numericRow821 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3692, -8640), (Sum.inr 3731, -4320), (Sum.inr 3769, -8640), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3849, -4320), (Sum.inr 3867, -4320), (Sum.inr 3875, -4320), (Sum.inr 3909, -4320), (Sum.inr 3957, -17280), (Sum.inr 4025, -4320), (Sum.inr 4046, -4320), (Sum.inr 4791, 17280), (Sum.inr 4795, 17280), (Sum.inr 4799, 34560), (Sum.inr 4863, 17280), (Sum.inr 5181, 17280), (Sum.inr 5184, 34560), (Sum.inr 5243, 17280), (Sum.inr 5348, 17280), (Sum.inr 5350, 34560), (Sum.inr 5379, 34560), (Sum.inr 5414, 34560), (Sum.inr 5429, 34560), (Sum.inr 5430, 34560)]

theorem reindexCheck821 : Integer.Sparse.reindex keyMap MixedData.row821 = numericRow821 := by decide +kernel

theorem numericCheck821 (x : Master → ℝ) : Integer.Sparse.eval numericRow821 x =
    (17280 : ℝ) * reducedSource821 x := by
  norm_num [numericRow821, reducedSource821, Integer.Sparse.eval, Sparse.eval, nodeValue4791, nodeValue4795, nodeValue4799, nodeValue4863, nodeValue5181, nodeValue5184, nodeValue5243, nodeValue5348, nodeValue5350, nodeValue5354, nodeValue5379, nodeValue5383, nodeValue5406, nodeValue5414, nodeValue5429, nodeValue5430, nodeValue5431, nodeValue5447, nodeValue5471, nodeValue5472, nodeValue5482]
  ring

noncomputable def reducedSource822 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3688 x + ((2 : ℝ) * Sparse.eval nodeValue3818 x + ((2 : ℝ) * Sparse.eval nodeValue3819 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((2 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

def numericRow822 : Integer.Sparse Master := [(Sum.inl 0, -297), (Sum.inl 5, -240), (Sum.inl 2, 1290), (Sum.inl 7, 480), (Sum.inl 8, 480), (Sum.inl 51, -2880), (Sum.inl 3, 6960), (Sum.inl 13, 720), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -2880), (Sum.inl 12, 2880), (Sum.inl 4, 3840), (Sum.inl 27, 720), (Sum.inl 1, -3765), (Sum.inl 31, -2880), (Sum.inr 2008, 12960), (Sum.inr 2012, 12960), (Sum.inr 2017, 25920), (Sum.inr 2232, 12960), (Sum.inr 2609, 12960), (Sum.inr 2614, 25920), (Sum.inr 2697, 12960), (Sum.inr 3685, 12960), (Sum.inr 3688, 25920), (Sum.inr 3819, 25920), (Sum.inr 3832, 25920), (Sum.inr 3846, 25920), (Sum.inr 3848, 25920), (Sum.inr 3867, 12960), (Sum.inr 3875, 12960), (Sum.inr 3909, 12960)]

theorem reindexCheck822 : Integer.Sparse.reindex keyMap MixedData.row822 = numericRow822 := by decide +kernel

theorem numericCheck822 (x : Master → ℝ) : Integer.Sparse.eval numericRow822 x =
    (12960 : ℝ) * reducedSource822 x := by
  norm_num [numericRow822, reducedSource822, Integer.Sparse.eval, Sparse.eval, nodeValue2008, nodeValue2012, nodeValue2017, nodeValue2232, nodeValue2609, nodeValue2614, nodeValue2697, nodeValue3685, nodeValue3688, nodeValue3818, nodeValue3819, nodeValue3832, nodeValue3846, nodeValue3847, nodeValue3848, nodeValue3867, nodeValue3875, nodeValue3909, nodeValue3976, nodeValue3992, nodeValue4002]
  ring

noncomputable def reducedSource823 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2074 x + ((2 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((2 : ℝ) * Sparse.eval nodeValue3524 x + ((2 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3734 x + ((2 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + 0))))))))))))))))))))

def numericRow823 : Integer.Sparse Master := [(Sum.inl 0, -56), (Sum.inl 5, 60), (Sum.inl 2, 90), (Sum.inl 7, 80), (Sum.inl 3, 2080), (Sum.inl 13, 160), (Sum.inl 23, -720), (Sum.inl 54, -480), (Sum.inl 12, 1280), (Sum.inl 25, -960), (Sum.inl 26, 160), (Sum.inl 4, 1120), (Sum.inl 27, -180), (Sum.inl 1, -990), (Sum.inr 2074, 4320), (Sum.inr 2076, 8640), (Sum.inr 2104, 4320), (Sum.inr 2213, 4320), (Sum.inr 3488, 4320), (Sum.inr 3491, 4320), (Sum.inr 3524, 8640), (Sum.inr 3720, 8640), (Sum.inr 3750, 8640), (Sum.inr 3768, 4320), (Sum.inr 3769, 8640), (Sum.inr 3812, 4320), (Sum.inr 3869, 8640), (Sum.inr 3871, 8640), (Sum.inr 3874, 8640), (Sum.inr 3957, 8640)]

theorem reindexCheck823 : Integer.Sparse.reindex keyMap MixedData.row823 = numericRow823 := by decide +kernel

theorem numericCheck823 (x : Master → ℝ) : Integer.Sparse.eval numericRow823 x =
    (4320 : ℝ) * reducedSource823 x := by
  norm_num [numericRow823, reducedSource823, Integer.Sparse.eval, Sparse.eval, nodeValue2074, nodeValue2076, nodeValue2104, nodeValue2213, nodeValue3488, nodeValue3491, nodeValue3524, nodeValue3720, nodeValue3734, nodeValue3750, nodeValue3768, nodeValue3769, nodeValue3812, nodeValue3869, nodeValue3871, nodeValue3874, nodeValue3882, nodeValue3956, nodeValue3957, nodeValue3980, nodeValue4026]
  ring

noncomputable def reducedSource824 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue4046 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow824 : Integer.Sparse Master := [(Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 2), (Sum.inr 4046, 1), (Sum.inr 4091, -1)]

theorem reindexCheck824 : Integer.Sparse.reindex keyMap MixedData.row824 = numericRow824 := by decide +kernel

theorem numericCheck824 (x : Master → ℝ) : Integer.Sparse.eval numericRow824 x =
    (1 : ℝ) * reducedSource824 x := by
  norm_num [numericRow824, reducedSource824, Integer.Sparse.eval, Sparse.eval, nodeValue3849, nodeValue3953, nodeValue3954, nodeValue3957, nodeValue4046, nodeValue4091]

noncomputable def reducedSource825 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2858 x + ((2 : ℝ) * Sparse.eval nodeValue3176 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow825 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 3176, 2), (Sum.inr 3179, 1), (Sum.inr 3199, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck825 : Integer.Sparse.reindex keyMap MixedData.row825 = numericRow825 := by decide +kernel

theorem numericCheck825 (x : Master → ℝ) : Integer.Sparse.eval numericRow825 x =
    (1 : ℝ) * reducedSource825 x := by
  norm_num [numericRow825, reducedSource825, Integer.Sparse.eval, Sparse.eval, nodeValue2858, nodeValue3176, nodeValue3179, nodeValue3199, nodeValue3954, nodeValue4091]

noncomputable def reducedSource826 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3179 x + ((1 : ℝ) * Sparse.eval nodeValue3731 x + ((3 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow826 : Integer.Sparse Master := [(Sum.inr 3179, 1), (Sum.inr 3731, 1), (Sum.inr 3954, 3), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem reindexCheck826 : Integer.Sparse.reindex keyMap MixedData.row826 = numericRow826 := by decide +kernel

theorem numericCheck826 (x : Master → ℝ) : Integer.Sparse.eval numericRow826 x =
    (1 : ℝ) * reducedSource826 x := by
  norm_num [numericRow826, reducedSource826, Integer.Sparse.eval, Sparse.eval, nodeValue3179, nodeValue3731, nodeValue3954, nodeValue4025, nodeValue4091]

noncomputable def reducedSource827 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2859 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3935 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow827 : Integer.Sparse Master := [(Sum.inr 2859, 1), (Sum.inr 3685, 1), (Sum.inr 3935, 2), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck827 : Integer.Sparse.reindex keyMap MixedData.row827 = numericRow827 := by decide +kernel

theorem numericCheck827 (x : Master → ℝ) : Integer.Sparse.eval numericRow827 x =
    (1 : ℝ) * reducedSource827 x := by
  norm_num [numericRow827, reducedSource827, Integer.Sparse.eval, Sparse.eval, nodeValue2859, nodeValue3685, nodeValue3935, nodeValue3953, nodeValue3954, nodeValue4091]

noncomputable def reducedSource828 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3176 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3935 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow828 : Integer.Sparse Master := [(Sum.inr 3176, 1), (Sum.inr 3724, 1), (Sum.inr 3935, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem reindexCheck828 : Integer.Sparse.reindex keyMap MixedData.row828 = numericRow828 := by decide +kernel

theorem numericCheck828 (x : Master → ℝ) : Integer.Sparse.eval numericRow828 x =
    (1 : ℝ) * reducedSource828 x := by
  norm_num [numericRow828, reducedSource828, Integer.Sparse.eval, Sparse.eval, nodeValue3176, nodeValue3724, nodeValue3935, nodeValue3949, nodeValue3954, nodeValue3972, nodeValue4091]

noncomputable def reducedSource829 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((2 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow829 : Integer.Sparse Master := [(Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 2), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem reindexCheck829 : Integer.Sparse.reindex keyMap MixedData.row829 = numericRow829 := by decide +kernel

theorem numericCheck829 (x : Master → ℝ) : Integer.Sparse.eval numericRow829 x =
    (1 : ℝ) * reducedSource829 x := by
  norm_num [numericRow829, reducedSource829, Integer.Sparse.eval, Sparse.eval, nodeValue2864, nodeValue3692, nodeValue3949, nodeValue3954, nodeValue3957, nodeValue4091]

noncomputable def reducedSource830 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow830 : Integer.Sparse Master := [(Sum.inr 3199, 1), (Sum.inr 3685, 1), (Sum.inr 3692, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck830 : Integer.Sparse.reindex keyMap MixedData.row830 = numericRow830 := by decide +kernel

theorem numericCheck830 (x : Master → ℝ) : Integer.Sparse.eval numericRow830 x =
    (1 : ℝ) * reducedSource830 x := by
  norm_num [numericRow830, reducedSource830, Integer.Sparse.eval, Sparse.eval, nodeValue3199, nodeValue3685, nodeValue3692, nodeValue3801, nodeValue3954, nodeValue4091]

noncomputable def reducedSource831 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3030 x + ((2 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3731 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow831 : Integer.Sparse Master := [(Sum.inr 3030, 1), (Sum.inr 3724, 2), (Sum.inr 3731, 1), (Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck831 : Integer.Sparse.reindex keyMap MixedData.row831 = numericRow831 := by decide +kernel

theorem numericCheck831 (x : Master → ℝ) : Integer.Sparse.eval numericRow831 x =
    (1 : ℝ) * reducedSource831 x := by
  norm_num [numericRow831, reducedSource831, Integer.Sparse.eval, Sparse.eval, nodeValue3030, nodeValue3724, nodeValue3731, nodeValue3849, nodeValue3954, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
