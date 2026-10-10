import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
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

noncomputable def reducedSource880 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2869 x + ((1 : ℝ) * Sparse.eval nodeValue2871 x + ((1 : ℝ) * Sparse.eval nodeValue2873 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow880 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2871, 1), (Sum.inr 2873, 1), (Sum.inr 2882, 1), (Sum.inr 3044, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem reindexCheck880 : Integer.Sparse.reindex keyMap MixedData.row880 = numericRow880 := by decide +kernel

theorem numericCheck880 (x : Master → ℝ) : Integer.Sparse.eval numericRow880 x =
    (1 : ℝ) * reducedSource880 x := by
  norm_num [numericRow880, reducedSource880, Integer.Sparse.eval, Sparse.eval, nodeValue2869, nodeValue2871, nodeValue2873, nodeValue2882, nodeValue3044, nodeValue3884, nodeValue4092]

noncomputable def reducedSource881 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1949 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2853 x + ((1 : ℝ) * Sparse.eval nodeValue2856 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3370 x + ((1 : ℝ) * Sparse.eval nodeValue3372 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3653 x + ((1 : ℝ) * Sparse.eval nodeValue3666 x + ((1 : ℝ) * Sparse.eval nodeValue3778 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((3 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))))))))))))))))))))))

def numericRow881 : Integer.Sparse Master := [(Sum.inl 0, -87), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, 15), (Sum.inr 1913, 2160), (Sum.inr 1915, 2160), (Sum.inr 1917, 2160), (Sum.inr 1949, 2160), (Sum.inr 2266, 2160), (Sum.inr 2853, 2160), (Sum.inr 2856, 2160), (Sum.inr 2881, 2160), (Sum.inr 3077, 2160), (Sum.inr 3370, 2160), (Sum.inr 3372, 2160), (Sum.inr 3391, 2160), (Sum.inr 3564, 2160), (Sum.inr 3653, 2160), (Sum.inr 3666, 2160), (Sum.inr 3778, 2160), (Sum.inr 3782, 2160), (Sum.inr 3801, 2160), (Sum.inr 3804, 2160), (Sum.inr 3809, 6480), (Sum.inr 3815, 2160), (Sum.inr 3913, 2160), (Sum.inr 4010, 2160), (Sum.inr 4025, 2160)]

theorem reindexCheck881 : Integer.Sparse.reindex keyMap MixedData.row881 = numericRow881 := by decide +kernel

theorem numericCheck881 (x : Master → ℝ) : Integer.Sparse.eval numericRow881 x =
    (2160 : ℝ) * reducedSource881 x := by
  norm_num [numericRow881, reducedSource881, Integer.Sparse.eval, Sparse.eval, nodeValue1913, nodeValue1915, nodeValue1917, nodeValue1949, nodeValue2266, nodeValue2853, nodeValue2856, nodeValue2881, nodeValue3077, nodeValue3370, nodeValue3372, nodeValue3391, nodeValue3564, nodeValue3653, nodeValue3666, nodeValue3778, nodeValue3782, nodeValue3801, nodeValue3804, nodeValue3809, nodeValue3815, nodeValue3862, nodeValue3912, nodeValue3913, nodeValue4010, nodeValue4025, nodeValue4029, nodeValue4039]
  ring

noncomputable def reducedSource882 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5407 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))

def numericRow882 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3732, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3811, -4320), (Sum.inr 3813, -4320), (Sum.inr 3814, -17280), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 4852, 17280), (Sum.inr 4853, 17280), (Sum.inr 4856, 17280), (Sum.inr 4867, 17280), (Sum.inr 4891, 17280), (Sum.inr 5074, 17280), (Sum.inr 5260, 17280), (Sum.inr 5353, 17280), (Sum.inr 5402, 17280), (Sum.inr 5407, 17280), (Sum.inr 5425, 17280), (Sum.inr 5436, 17280), (Sum.inr 5445, 17280), (Sum.inr 5446, 34560)]

theorem reindexCheck882 : Integer.Sparse.reindex keyMap MixedData.row882 = numericRow882 := by decide +kernel

theorem numericCheck882 (x : Master → ℝ) : Integer.Sparse.eval numericRow882 x =
    (17280 : ℝ) * reducedSource882 x := by
  norm_num [numericRow882, reducedSource882, Integer.Sparse.eval, Sparse.eval, nodeValue4852, nodeValue4853, nodeValue4856, nodeValue4867, nodeValue4891, nodeValue5074, nodeValue5080, nodeValue5105, nodeValue5260, nodeValue5353, nodeValue5355, nodeValue5370, nodeValue5378, nodeValue5384, nodeValue5397, nodeValue5402, nodeValue5405, nodeValue5407, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5425, nodeValue5434, nodeValue5436, nodeValue5445, nodeValue5446, nodeValue5483]
  ring

noncomputable def reducedSource883 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + 0)))))))))))))))))))))))))))))

def numericRow883 : Integer.Sparse Master := [(Sum.inl 0, -154), (Sum.inl 2, -105), (Sum.inl 3, -480), (Sum.inl 13, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 165), (Sum.inr 2250, 4320), (Sum.inr 2251, 4320), (Sum.inr 2253, 4320), (Sum.inr 2259, 4320), (Sum.inr 2274, 4320), (Sum.inr 3463, 4320), (Sum.inr 3478, 4320), (Sum.inr 3479, 4320), (Sum.inr 3540, 4320), (Sum.inr 3761, 4320), (Sum.inr 3770, 4320), (Sum.inr 3771, 4320), (Sum.inr 3795, 4320), (Sum.inr 3796, 4320), (Sum.inr 3800, 4320), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3811, 4320), (Sum.inr 3814, 4320), (Sum.inr 3840, 4320), (Sum.inr 3854, 4320), (Sum.inr 3880, 4320), (Sum.inr 3881, 4320), (Sum.inr 3884, 4320)]

theorem reindexCheck883 : Integer.Sparse.reindex keyMap MixedData.row883 = numericRow883 := by decide +kernel

theorem numericCheck883 (x : Master → ℝ) : Integer.Sparse.eval numericRow883 x =
    (4320 : ℝ) * reducedSource883 x := by
  norm_num [numericRow883, reducedSource883, Integer.Sparse.eval, Sparse.eval, nodeValue2250, nodeValue2251, nodeValue2253, nodeValue2259, nodeValue2274, nodeValue3463, nodeValue3478, nodeValue3479, nodeValue3540, nodeValue3761, nodeValue3770, nodeValue3771, nodeValue3795, nodeValue3796, nodeValue3800, nodeValue3802, nodeValue3803, nodeValue3807, nodeValue3808, nodeValue3811, nodeValue3814, nodeValue3840, nodeValue3852, nodeValue3854, nodeValue3856, nodeValue3880, nodeValue3881, nodeValue3883, nodeValue3884, nodeValue3981]
  ring

noncomputable def reducedSource884 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5085 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((1 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))))))))))

def numericRow884 : Integer.Sparse Master := [(Sum.inl 0, 30), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 4, -16), (Sum.inl 1, -29), (Sum.inr 2512, -864), (Sum.inr 3054, -864), (Sum.inr 3471, -864), (Sum.inr 3626, -864), (Sum.inr 3705, -864), (Sum.inr 3767, -864), (Sum.inr 3781, -864), (Sum.inr 3794, -864), (Sum.inr 3801, -864), (Sum.inr 3809, -864), (Sum.inr 3812, -864), (Sum.inr 3813, -864), (Sum.inr 3814, -1728), (Sum.inr 3903, -864), (Sum.inr 3906, -864), (Sum.inr 3907, -864), (Sum.inr 3913, -864), (Sum.inr 5085, 3456), (Sum.inr 5086, 3456), (Sum.inr 5087, 3456), (Sum.inr 5090, 6912), (Sum.inr 5103, 3456), (Sum.inr 5266, 3456), (Sum.inr 5286, 3456), (Sum.inr 5287, 3456), (Sum.inr 5289, 3456), (Sum.inr 5299, 3456), (Sum.inr 5359, 3456), (Sum.inr 5360, 3456), (Sum.inr 5361, 3456), (Sum.inr 5425, 3456), (Sum.inr 5430, 3456), (Sum.inr 5446, 3456)]

theorem reindexCheck884 : Integer.Sparse.reindex keyMap MixedData.row884 = numericRow884 := by decide +kernel

theorem numericCheck884 (x : Master → ℝ) : Integer.Sparse.eval numericRow884 x =
    (3456 : ℝ) * reducedSource884 x := by
  norm_num [numericRow884, reducedSource884, Integer.Sparse.eval, Sparse.eval, nodeValue5085, nodeValue5086, nodeValue5087, nodeValue5090, nodeValue5102, nodeValue5103, nodeValue5266, nodeValue5286, nodeValue5287, nodeValue5289, nodeValue5299, nodeValue5302, nodeValue5359, nodeValue5360, nodeValue5361, nodeValue5368, nodeValue5395, nodeValue5406, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5413, nodeValue5425, nodeValue5430, nodeValue5434, nodeValue5435, nodeValue5443, nodeValue5446, nodeValue5451]
  ring

noncomputable def reducedSource885 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))))))))))

def numericRow885 : Integer.Sparse Master := [(Sum.inl 0, -30), (Sum.inl 2, -13), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, 29), (Sum.inr 3023, 864), (Sum.inr 3024, 864), (Sum.inr 3025, 864), (Sum.inr 3051, 864), (Sum.inr 3097, 864), (Sum.inr 3461, 864), (Sum.inr 3464, 864), (Sum.inr 3471, 864), (Sum.inr 3472, 864), (Sum.inr 3480, 1728), (Sum.inr 3535, 864), (Sum.inr 3626, 864), (Sum.inr 3759, 864), (Sum.inr 3762, 864), (Sum.inr 3767, 864), (Sum.inr 3772, 864), (Sum.inr 3794, 864), (Sum.inr 3801, 864), (Sum.inr 3809, 864), (Sum.inr 3814, 864), (Sum.inr 3839, 864), (Sum.inr 3959, 864), (Sum.inr 3972, 864)]

theorem reindexCheck885 : Integer.Sparse.reindex keyMap MixedData.row885 = numericRow885 := by decide +kernel

theorem numericCheck885 (x : Master → ℝ) : Integer.Sparse.eval numericRow885 x =
    (864 : ℝ) * reducedSource885 x := by
  norm_num [numericRow885, reducedSource885, Integer.Sparse.eval, Sparse.eval, nodeValue3023, nodeValue3024, nodeValue3025, nodeValue3051, nodeValue3097, nodeValue3461, nodeValue3464, nodeValue3471, nodeValue3472, nodeValue3480, nodeValue3535, nodeValue3626, nodeValue3759, nodeValue3762, nodeValue3767, nodeValue3772, nodeValue3794, nodeValue3801, nodeValue3808, nodeValue3809, nodeValue3814, nodeValue3817, nodeValue3839, nodeValue3853, nodeValue3862, nodeValue3959, nodeValue3972, nodeValue3982, nodeValue3987]
  ring

noncomputable def reducedSource886 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5064 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5181 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5350 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow886 : Integer.Sparse Master := [(Sum.inl 0, 8), (Sum.inl 2, -5), (Sum.inl 1, 15), (Sum.inr 3690, -720), (Sum.inr 3764, -720), (Sum.inr 3800, -360), (Sum.inr 3805, -360), (Sum.inr 3849, -360), (Sum.inr 3875, -360), (Sum.inr 3885, -720), (Sum.inr 3957, -1440), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4010, -360), (Sum.inr 4046, -360), (Sum.inr 5064, 1440), (Sum.inr 5067, 1440), (Sum.inr 5071, 2880), (Sum.inr 5181, 1440), (Sum.inr 5185, 2880), (Sum.inr 5244, 1440), (Sum.inr 5282, 1440), (Sum.inr 5348, 1440), (Sum.inr 5350, 2880), (Sum.inr 5421, 2880), (Sum.inr 5429, 1440), (Sum.inr 5470, 2880), (Sum.inr 5480, 2880)]

theorem reindexCheck886 : Integer.Sparse.reindex keyMap MixedData.row886 = numericRow886 := by decide +kernel

theorem numericCheck886 (x : Master → ℝ) : Integer.Sparse.eval numericRow886 x =
    (1440 : ℝ) * reducedSource886 x := by
  norm_num [numericRow886, reducedSource886, Integer.Sparse.eval, Sparse.eval, nodeValue5064, nodeValue5067, nodeValue5071, nodeValue5181, nodeValue5185, nodeValue5244, nodeValue5282, nodeValue5348, nodeValue5350, nodeValue5352, nodeValue5405, nodeValue5421, nodeValue5429, nodeValue5431, nodeValue5448, nodeValue5470, nodeValue5472, nodeValue5473, nodeValue5480, nodeValue5482, nodeValue5485]
  ring

noncomputable def reducedSource887 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((2 : ℝ) * Sparse.eval nodeValue3936 x + ((2 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4002 x + 0))))))))))))))))))))

def numericRow887 : Integer.Sparse Master := [(Sum.inl 0, -1140), (Sum.inl 5, -720), (Sum.inl 2, 2670), (Sum.inl 7, 960), (Sum.inl 8, 960), (Sum.inl 51, -2880), (Sum.inl 3, 6720), (Sum.inl 13, 480), (Sum.inl 24, -2880), (Sum.inl 12, 1920), (Sum.inl 4, 4800), (Sum.inl 27, 2880), (Sum.inl 1, -7110), (Sum.inl 30, -2880), (Sum.inl 31, -5760), (Sum.inr 2469, 25920), (Sum.inr 2473, 25920), (Sum.inr 2478, 51840), (Sum.inr 2609, 25920), (Sum.inr 2615, 51840), (Sum.inr 2698, 25920), (Sum.inr 2751, 25920), (Sum.inr 3685, 25920), (Sum.inr 3688, 51840), (Sum.inr 3846, 25920), (Sum.inr 3873, 51840), (Sum.inr 3875, 25920), (Sum.inr 3885, 25920), (Sum.inr 3947, 51840), (Sum.inr 3978, 51840)]

theorem reindexCheck887 : Integer.Sparse.reindex keyMap MixedData.row887 = numericRow887 := by decide +kernel

theorem numericCheck887 (x : Master → ℝ) : Integer.Sparse.eval numericRow887 x =
    (25920 : ℝ) * reducedSource887 x := by
  norm_num [numericRow887, reducedSource887, Integer.Sparse.eval, Sparse.eval, nodeValue2469, nodeValue2473, nodeValue2478, nodeValue2609, nodeValue2615, nodeValue2698, nodeValue2751, nodeValue3685, nodeValue3688, nodeValue3846, nodeValue3873, nodeValue3875, nodeValue3885, nodeValue3936, nodeValue3947, nodeValue3977, nodeValue3978, nodeValue3992, nodeValue3995, nodeValue3998, nodeValue4002]
  ring

noncomputable def reducedSource888 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3443 x + ((2 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3750 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3946 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + 0))))))))))))))))))))

def numericRow888 : Integer.Sparse Master := [(Sum.inl 0, -103), (Sum.inl 2, 125), (Sum.inl 3, 560), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 480), (Sum.inl 1, -560), (Sum.inr 3443, 4320), (Sum.inr 3445, 8640), (Sum.inr 3476, 4320), (Sum.inr 3491, 4320), (Sum.inr 3497, 4320), (Sum.inr 3529, 8640), (Sum.inr 3580, 4320), (Sum.inr 3750, 8640), (Sum.inr 3764, 8640), (Sum.inr 3768, 4320), (Sum.inr 3805, 4320), (Sum.inr 3874, 4320), (Sum.inr 3946, 8640), (Sum.inr 3955, 8640), (Sum.inr 3957, 8640), (Sum.inr 3961, 8640), (Sum.inr 3978, 8640)]

theorem reindexCheck888 : Integer.Sparse.reindex keyMap MixedData.row888 = numericRow888 := by decide +kernel

theorem numericCheck888 (x : Master → ℝ) : Integer.Sparse.eval numericRow888 x =
    (4320 : ℝ) * reducedSource888 x := by
  norm_num [numericRow888, reducedSource888, Integer.Sparse.eval, Sparse.eval, nodeValue3443, nodeValue3445, nodeValue3476, nodeValue3491, nodeValue3497, nodeValue3529, nodeValue3580, nodeValue3750, nodeValue3764, nodeValue3768, nodeValue3805, nodeValue3874, nodeValue3946, nodeValue3955, nodeValue3957, nodeValue3961, nodeValue3978, nodeValue3980, nodeValue3984, nodeValue4026, nodeValue4028]
  ring

noncomputable def reducedSource889 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow889 : Integer.Sparse Master := [(Sum.inr 2981, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 2), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

theorem reindexCheck889 : Integer.Sparse.reindex keyMap MixedData.row889 = numericRow889 := by decide +kernel

theorem numericCheck889 (x : Master → ℝ) : Integer.Sparse.eval numericRow889 x =
    (1 : ℝ) * reducedSource889 x := by
  norm_num [numericRow889, reducedSource889, Integer.Sparse.eval, Sparse.eval, nodeValue2981, nodeValue3685, nodeValue3690, nodeValue3800, nodeValue3953, nodeValue4091]

noncomputable def reducedSource890 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5183 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5399 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5402 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))

def numericRow890 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3689, -360), (Sum.inr 3703, -360), (Sum.inr 3757, -360), (Sum.inr 3758, -360), (Sum.inr 3786, -360), (Sum.inr 3799, -360), (Sum.inr 3800, -720), (Sum.inr 3805, -720), (Sum.inr 3845, -1440), (Sum.inr 3857, -720), (Sum.inr 3876, -720), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4047, -720), (Sum.inr 5183, 2880), (Sum.inr 5187, 1440), (Sum.inr 5197, 1440), (Sum.inr 5263, 1440), (Sum.inr 5353, 2880), (Sum.inr 5399, 2880), (Sum.inr 5402, 2880), (Sum.inr 5414, 2880), (Sum.inr 5429, 1440), (Sum.inr 5446, 2880)]

theorem reindexCheck890 : Integer.Sparse.reindex keyMap MixedData.row890 = numericRow890 := by decide +kernel

theorem numericCheck890 (x : Master → ℝ) : Integer.Sparse.eval numericRow890 x =
    (1440 : ℝ) * reducedSource890 x := by
  norm_num [numericRow890, reducedSource890, Integer.Sparse.eval, Sparse.eval, nodeValue5183, nodeValue5187, nodeValue5197, nodeValue5263, nodeValue5351, nodeValue5353, nodeValue5365, nodeValue5399, nodeValue5400, nodeValue5402, nodeValue5405, nodeValue5414, nodeValue5428, nodeValue5429, nodeValue5438, nodeValue5446, nodeValue5471, nodeValue5473, nodeValue5483]
  ring

noncomputable def reducedSource891 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3501 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3785 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4023 x + 0))))))))))))))))))))

def numericRow891 : Integer.Sparse Master := [(Sum.inl 0, -615), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, -195), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 1680), (Sum.inl 13, 240), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 480), (Sum.inl 25, -1440), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 27, -180), (Sum.inl 1, 555), (Sum.inr 3501, 25920), (Sum.inr 3505, 12960), (Sum.inr 3537, 12960), (Sum.inr 3569, 12960), (Sum.inr 3757, 12960), (Sum.inr 3758, 12960), (Sum.inr 3761, 25920), (Sum.inr 3785, 25920), (Sum.inr 3788, 25920), (Sum.inr 3800, 12960), (Sum.inr 3845, 25920), (Sum.inr 3869, 12960), (Sum.inr 3884, 25920), (Sum.inr 3949, 12960), (Sum.inr 3954, 12960), (Sum.inr 3958, 25920)]

theorem reindexCheck891 : Integer.Sparse.reindex keyMap MixedData.row891 = numericRow891 := by decide +kernel

theorem numericCheck891 (x : Master → ℝ) : Integer.Sparse.eval numericRow891 x =
    (12960 : ℝ) * reducedSource891 x := by
  norm_num [numericRow891, reducedSource891, Integer.Sparse.eval, Sparse.eval, nodeValue3501, nodeValue3505, nodeValue3537, nodeValue3569, nodeValue3757, nodeValue3758, nodeValue3761, nodeValue3785, nodeValue3788, nodeValue3800, nodeValue3845, nodeValue3869, nodeValue3884, nodeValue3949, nodeValue3954, nodeValue3958, nodeValue3976, nodeValue3977, nodeValue3981, nodeValue3993, nodeValue4023]
  ring

noncomputable def reducedSource892 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue3783 x + ((2 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + 0))))))))))))))))))))

def numericRow892 : Integer.Sparse Master := [(Sum.inl 0, -1992), (Sum.inl 5, -240), (Sum.inl 2, -930), (Sum.inl 7, 480), (Sum.inl 8, 480), (Sum.inl 51, -2880), (Sum.inl 3, 1920), (Sum.inl 13, 480), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -2880), (Sum.inl 12, 960), (Sum.inl 4, 960), (Sum.inl 27, 720), (Sum.inl 1, 1230), (Sum.inr 2613, 51840), (Sum.inr 2617, 25920), (Sum.inr 2631, 25920), (Sum.inr 2728, 25920), (Sum.inr 3783, 51840), (Sum.inr 3785, 51840), (Sum.inr 3799, 25920), (Sum.inr 3800, 25920), (Sum.inr 3802, 51840), (Sum.inr 3846, 25920), (Sum.inr 3869, 25920), (Sum.inr 3876, 51840), (Sum.inr 3881, 51840), (Sum.inr 3949, 25920)]

theorem reindexCheck892 : Integer.Sparse.reindex keyMap MixedData.row892 = numericRow892 := by decide +kernel

theorem numericCheck892 (x : Master → ℝ) : Integer.Sparse.eval numericRow892 x =
    (25920 : ℝ) * reducedSource892 x := by
  norm_num [numericRow892, reducedSource892, Integer.Sparse.eval, Sparse.eval, nodeValue2613, nodeValue2617, nodeValue2631, nodeValue2728, nodeValue3783, nodeValue3785, nodeValue3799, nodeValue3800, nodeValue3802, nodeValue3846, nodeValue3869, nodeValue3876, nodeValue3881, nodeValue3937, nodeValue3938, nodeValue3949, nodeValue3953, nodeValue3977, nodeValue3981, nodeValue3995, nodeValue4003]
  ring

noncomputable def reducedSource893 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3689 x + ((2 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow893 : Integer.Sparse Master := [(Sum.inr 3689, 1), (Sum.inr 3691, 2), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

theorem reindexCheck893 : Integer.Sparse.reindex keyMap MixedData.row893 = numericRow893 := by decide +kernel

theorem numericCheck893 (x : Master → ℝ) : Integer.Sparse.eval numericRow893 x =
    (1 : ℝ) * reducedSource893 x := by
  norm_num [numericRow893, reducedSource893, Integer.Sparse.eval, Sparse.eval, nodeValue3689, nodeValue3691, nodeValue3703, nodeValue3805, nodeValue3956, nodeValue4092]

noncomputable def reducedSource894 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3923 x + ((1 : ℝ) * Sparse.eval nodeValue3969 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

def numericRow894 : Integer.Sparse Master := [(Sum.inl 0, -184), (Sum.inl 5, 40), (Sum.inl 6, -10), (Sum.inl 2, 500), (Sum.inl 51, -480), (Sum.inl 3, 2720), (Sum.inl 13, 320), (Sum.inl 52, 160), (Sum.inl 12, 1120), (Sum.inl 26, 160), (Sum.inl 4, 1760), (Sum.inl 1, -1570), (Sum.inl 31, -960), (Sum.inr 2453, 8640), (Sum.inr 2456, 8640), (Sum.inr 2460, 8640), (Sum.inr 2493, 8640), (Sum.inr 2533, 8640), (Sum.inr 2537, 8640), (Sum.inr 2567, 8640), (Sum.inr 2662, 8640), (Sum.inr 2731, 8640), (Sum.inr 3568, 8640), (Sum.inr 3569, 8640), (Sum.inr 3571, 8640), (Sum.inr 3574, 8640), (Sum.inr 3680, 8640), (Sum.inr 3697, 8640), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3879, 8640), (Sum.inr 3880, 17280), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640)]

theorem reindexCheck894 : Integer.Sparse.reindex keyMap MixedData.row894 = numericRow894 := by decide +kernel

theorem numericCheck894 (x : Master → ℝ) : Integer.Sparse.eval numericRow894 x =
    (8640 : ℝ) * reducedSource894 x := by
  norm_num [numericRow894, reducedSource894, Integer.Sparse.eval, Sparse.eval, nodeValue2453, nodeValue2456, nodeValue2460, nodeValue2493, nodeValue2533, nodeValue2537, nodeValue2567, nodeValue2662, nodeValue2731, nodeValue3568, nodeValue3569, nodeValue3571, nodeValue3574, nodeValue3680, nodeValue3697, nodeValue3840, nodeValue3848, nodeValue3849, nodeValue3851, nodeValue3879, nodeValue3880, nodeValue3882, nodeValue3884, nodeValue3885, nodeValue3887, nodeValue3923, nodeValue3969, nodeValue3994, nodeValue3995]
  ring

noncomputable def reducedSource895 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow895 : Integer.Sparse Master := [(Sum.inr 2976, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 2), (Sum.inr 3909, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem reindexCheck895 : Integer.Sparse.reindex keyMap MixedData.row895 = numericRow895 := by decide +kernel

theorem numericCheck895 (x : Master → ℝ) : Integer.Sparse.eval numericRow895 x =
    (1 : ℝ) * reducedSource895 x := by
  norm_num [numericRow895, reducedSource895, Integer.Sparse.eval, Sparse.eval, nodeValue2976, nodeValue3878, nodeValue3880, nodeValue3909, nodeValue3945, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
