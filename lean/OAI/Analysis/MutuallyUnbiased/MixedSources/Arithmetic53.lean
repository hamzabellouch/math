import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
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

noncomputable def reducedSource848 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow848 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 3871, 1), (Sum.inr 3927, 1), (Sum.inr 3974, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem reindexCheck848 : Integer.Sparse.reindex keyMap MixedData.row848 = numericRow848 := by decide +kernel

theorem numericCheck848 (x : Master → ℝ) : Integer.Sparse.eval numericRow848 x =
    (1 : ℝ) * reducedSource848 x := by
  norm_num [numericRow848, reducedSource848, Integer.Sparse.eval, Sparse.eval, nodeValue2951, nodeValue3871, nodeValue3927, nodeValue3974, nodeValue3978, nodeValue3983, nodeValue4091]

noncomputable def reducedSource849 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow849 : Integer.Sparse Master := [(Sum.inr 2984, 1), (Sum.inr 3783, 1), (Sum.inr 3787, 1), (Sum.inr 3800, 1), (Sum.inr 3871, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

theorem reindexCheck849 : Integer.Sparse.reindex keyMap MixedData.row849 = numericRow849 := by decide +kernel

theorem numericCheck849 (x : Master → ℝ) : Integer.Sparse.eval numericRow849 x =
    (1 : ℝ) * reducedSource849 x := by
  norm_num [numericRow849, reducedSource849, Integer.Sparse.eval, Sparse.eval, nodeValue2984, nodeValue3783, nodeValue3787, nodeValue3800, nodeValue3871, nodeValue3978, nodeValue4091]

noncomputable def reducedSource850 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow850 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 3091, 1), (Sum.inr 3787, 1), (Sum.inr 3871, 1), (Sum.inr 3875, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem reindexCheck850 : Integer.Sparse.reindex keyMap MixedData.row850 = numericRow850 := by decide +kernel

theorem numericCheck850 (x : Master → ℝ) : Integer.Sparse.eval numericRow850 x =
    (1 : ℝ) * reducedSource850 x := by
  norm_num [numericRow850, reducedSource850, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue3091, nodeValue3787, nodeValue3871, nodeValue3875, nodeValue3876, nodeValue4091]

noncomputable def reducedSource851 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4797 x + ((1 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4825 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5132 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5350 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5362 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))))))))))

def numericRow851 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 3721, -4320), (Sum.inr 3789, -4320), (Sum.inr 3801, -4320), (Sum.inr 3810, -4320), (Sum.inr 3812, -4320), (Sum.inr 3836, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3900, -4320), (Sum.inr 3909, -4320), (Sum.inr 3964, -4320), (Sum.inr 3974, -8640), (Sum.inr 4025, -4320), (Sum.inr 4046, -4320), (Sum.inr 4797, 17280), (Sum.inr 4799, 17280), (Sum.inr 4803, 17280), (Sum.inr 4825, 17280), (Sum.inr 4851, 17280), (Sum.inr 5129, 17280), (Sum.inr 5132, 17280), (Sum.inr 5144, 17280), (Sum.inr 5249, 17280), (Sum.inr 5350, 17280), (Sum.inr 5353, 17280), (Sum.inr 5362, 17280), (Sum.inr 5377, 17280), (Sum.inr 5379, 17280), (Sum.inr 5414, 17280), (Sum.inr 5419, 17280), (Sum.inr 5425, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 34560), (Sum.inr 5480, 17280)]

theorem reindexCheck851 : Integer.Sparse.reindex keyMap MixedData.row851 = numericRow851 := by decide +kernel

theorem numericCheck851 (x : Master → ℝ) : Integer.Sparse.eval numericRow851 x =
    (17280 : ℝ) * reducedSource851 x := by
  norm_num [numericRow851, reducedSource851, Integer.Sparse.eval, Sparse.eval, nodeValue4797, nodeValue4799, nodeValue4803, nodeValue4825, nodeValue4851, nodeValue5129, nodeValue5132, nodeValue5144, nodeValue5249, nodeValue5350, nodeValue5353, nodeValue5362, nodeValue5377, nodeValue5379, nodeValue5380, nodeValue5403, nodeValue5406, nodeValue5414, nodeValue5419, nodeValue5422, nodeValue5424, nodeValue5425, nodeValue5429, nodeValue5430, nodeValue5447, nodeValue5478, nodeValue5480, nodeValue5481, nodeValue5482]; ring

noncomputable def reducedSource852 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2073 x + ((1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3726 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3750 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((1 : ℝ) * Sparse.eval nodeValue3829 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + 0))))))))))))))))))))))))))))

def numericRow852 : Integer.Sparse Master := [(Sum.inl 0, -178), (Sum.inl 6, -10), (Sum.inl 2, 600), (Sum.inl 7, 480), (Sum.inl 35, 320), (Sum.inl 51, -480), (Sum.inl 3, 4960), (Sum.inl 13, 320), (Sum.inl 52, 160), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 55, -960), (Sum.inl 12, 1600), (Sum.inl 26, 960), (Sum.inl 4, 2880), (Sum.inl 27, 120), (Sum.inl 1, -2180), (Sum.inl 31, -480), (Sum.inr 2070, 8640), (Sum.inr 2073, 8640), (Sum.inr 2076, 8640), (Sum.inr 2088, 8640), (Sum.inr 2195, 8640), (Sum.inr 2545, 8640), (Sum.inr 2551, 8640), (Sum.inr 2566, 8640), (Sum.inr 2708, 8640), (Sum.inr 3716, 8640), (Sum.inr 3720, 8640), (Sum.inr 3748, 8640), (Sum.inr 3750, 8640), (Sum.inr 3761, 8640), (Sum.inr 3810, 8640), (Sum.inr 3812, 8640), (Sum.inr 3825, 8640), (Sum.inr 3840, 8640), (Sum.inr 3869, 8640), (Sum.inr 3871, 17280), (Sum.inr 3874, 8640), (Sum.inr 3978, 8640)]

theorem reindexCheck852 : Integer.Sparse.reindex keyMap MixedData.row852 = numericRow852 := by decide +kernel

theorem numericCheck852 (x : Master → ℝ) : Integer.Sparse.eval numericRow852 x =
    (8640 : ℝ) * reducedSource852 x := by
  norm_num [numericRow852, reducedSource852, Integer.Sparse.eval, Sparse.eval, nodeValue2070, nodeValue2073, nodeValue2076, nodeValue2088, nodeValue2195, nodeValue2545, nodeValue2551, nodeValue2566, nodeValue2708, nodeValue3716, nodeValue3720, nodeValue3726, nodeValue3748, nodeValue3750, nodeValue3761, nodeValue3810, nodeValue3812, nodeValue3825, nodeValue3829, nodeValue3840, nodeValue3869, nodeValue3871, nodeValue3874, nodeValue3882, nodeValue3978, nodeValue3979, nodeValue3980, nodeValue3990, nodeValue3994]; ring

noncomputable def reducedSource853 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue3499 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3688 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3700 x + ((1 : ℝ) * Sparse.eval nodeValue3819 x + ((1 : ℝ) * Sparse.eval nodeValue3822 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + 0))))))))))))))))))))))))))))

def numericRow853 : Integer.Sparse Master := [(Sum.inl 0, -237), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, 330), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 2640), (Sum.inl 13, 1440), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 1200), (Sum.inl 25, -720), (Sum.inl 4, 960), (Sum.inl 27, -180), (Sum.inl 1, -1590), (Sum.inr 2015, 12960), (Sum.inr 2017, 12960), (Sum.inr 2021, 12960), (Sum.inr 2044, 12960), (Sum.inr 2240, 12960), (Sum.inr 3499, 12960), (Sum.inr 3502, 12960), (Sum.inr 3516, 12960), (Sum.inr 3557, 12960), (Sum.inr 3688, 12960), (Sum.inr 3691, 12960), (Sum.inr 3700, 12960), (Sum.inr 3819, 12960), (Sum.inr 3832, 12960), (Sum.inr 3835, 12960), (Sum.inr 3836, 12960), (Sum.inr 3839, 12960), (Sum.inr 3842, 12960), (Sum.inr 3843, 12960), (Sum.inr 3846, 12960), (Sum.inr 3848, 25920), (Sum.inr 3900, 12960), (Sum.inr 3909, 12960), (Sum.inr 3974, 12960), (Sum.inr 3978, 12960)]

theorem reindexCheck853 : Integer.Sparse.reindex keyMap MixedData.row853 = numericRow853 := by decide +kernel

theorem numericCheck853 (x : Master → ℝ) : Integer.Sparse.eval numericRow853 x =
    (12960 : ℝ) * reducedSource853 x := by
  norm_num [numericRow853, reducedSource853, Integer.Sparse.eval, Sparse.eval, nodeValue2015, nodeValue2017, nodeValue2021, nodeValue2044, nodeValue2240, nodeValue3499, nodeValue3502, nodeValue3516, nodeValue3557, nodeValue3688, nodeValue3691, nodeValue3700, nodeValue3819, nodeValue3822, nodeValue3832, nodeValue3835, nodeValue3836, nodeValue3839, nodeValue3842, nodeValue3843, nodeValue3846, nodeValue3847, nodeValue3848, nodeValue3900, nodeValue3909, nodeValue3974, nodeValue3978, nodeValue3991, nodeValue3992]; ring

noncomputable def reducedSource854 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow854 : Integer.Sparse Master := [(Sum.inr 2916, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem reindexCheck854 : Integer.Sparse.reindex keyMap MixedData.row854 = numericRow854 := by decide +kernel

theorem numericCheck854 (x : Master → ℝ) : Integer.Sparse.eval numericRow854 x =
    (1 : ℝ) * reducedSource854 x := by
  norm_num [numericRow854, reducedSource854, Integer.Sparse.eval, Sparse.eval, nodeValue2916, nodeValue3716, nodeValue3721, nodeValue3724, nodeValue3838, nodeValue3972, nodeValue4091]

noncomputable def reducedSource855 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow855 : Integer.Sparse Master := [(Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 3964, 1), (Sum.inr 3972, 2), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem reindexCheck855 : Integer.Sparse.reindex keyMap MixedData.row855 = numericRow855 := by decide +kernel

theorem numericCheck855 (x : Master → ℝ) : Integer.Sparse.eval numericRow855 x =
    (1 : ℝ) * reducedSource855 x := by
  norm_num [numericRow855, reducedSource855, Integer.Sparse.eval, Sparse.eval, nodeValue3172, nodeValue3721, nodeValue3964, nodeValue3972, nodeValue4025, nodeValue4091]

noncomputable def reducedSource856 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3789 x + ((1 : ℝ) * Sparse.eval nodeValue3949 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow856 : Integer.Sparse Master := [(Sum.inr 3066, 1), (Sum.inr 3789, 1), (Sum.inr 3949, 1), (Sum.inr 3972, 2), (Sum.inr 4091, -1)]

theorem reindexCheck856 : Integer.Sparse.reindex keyMap MixedData.row856 = numericRow856 := by decide +kernel

theorem numericCheck856 (x : Master → ℝ) : Integer.Sparse.eval numericRow856 x =
    (1 : ℝ) * reducedSource856 x := by
  norm_num [numericRow856, reducedSource856, Integer.Sparse.eval, Sparse.eval, nodeValue3066, nodeValue3789, nodeValue3949, nodeValue3972, nodeValue4008, nodeValue4091]

noncomputable def reducedSource857 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5082 x + ((1 : ℝ) * Sparse.eval nodeValue5083 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5091 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5146 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5357 x + ((1 : ℝ) * Sparse.eval nodeValue5358 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0))))))))))))))))))))))))))))

def numericRow857 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -85), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5082, 17280), (Sum.inr 5083, 17280), (Sum.inr 5086, 17280), (Sum.inr 5091, 17280), (Sum.inr 5144, 17280), (Sum.inr 5146, 17280), (Sum.inr 5160, 17280), (Sum.inr 5289, 17280), (Sum.inr 5299, 17280), (Sum.inr 5357, 17280), (Sum.inr 5358, 17280), (Sum.inr 5360, 17280), (Sum.inr 5381, 17280), (Sum.inr 5382, 17280), (Sum.inr 5420, 17280), (Sum.inr 5421, 17280), (Sum.inr 5425, 34560), (Sum.inr 5446, 17280)]

theorem reindexCheck857 : Integer.Sparse.reindex keyMap MixedData.row857 = numericRow857 := by decide +kernel

theorem numericCheck857 (x : Master → ℝ) : Integer.Sparse.eval numericRow857 x =
    (17280 : ℝ) * reducedSource857 x := by
  norm_num [numericRow857, reducedSource857, Integer.Sparse.eval, Sparse.eval, nodeValue5082, nodeValue5083, nodeValue5086, nodeValue5091, nodeValue5144, nodeValue5146, nodeValue5160, nodeValue5289, nodeValue5299, nodeValue5357, nodeValue5358, nodeValue5360, nodeValue5381, nodeValue5382, nodeValue5395, nodeValue5411, nodeValue5420, nodeValue5421, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5432, nodeValue5434, nodeValue5438, nodeValue5446, nodeValue5451, nodeValue5468, nodeValue5473, nodeValue5477]; ring

noncomputable def reducedSource858 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2500 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3968 x + ((1 : ℝ) * Sparse.eval nodeValue3970 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

def numericRow858 : Integer.Sparse Master := [(Sum.inl 0, -179), (Sum.inl 5, 20), (Sum.inl 6, -5), (Sum.inl 2, -35), (Sum.inl 51, -240), (Sum.inl 3, 160), (Sum.inl 52, 80), (Sum.inl 1, 205), (Sum.inr 2490, 4320), (Sum.inr 2491, 4320), (Sum.inr 2494, 4320), (Sum.inr 2500, 4320), (Sum.inr 2773, 4320), (Sum.inr 3557, 4320), (Sum.inr 3558, 4320), (Sum.inr 3560, 4320), (Sum.inr 3572, 4320), (Sum.inr 3695, 4320), (Sum.inr 3696, 4320), (Sum.inr 3698, 4320), (Sum.inr 3827, 4320), (Sum.inr 3834, 4320), (Sum.inr 3837, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3850, 4320), (Sum.inr 3866, 4320), (Sum.inr 3870, 4320), (Sum.inr 3872, 4320), (Sum.inr 3876, 4320), (Sum.inr 3881, 4320)]

theorem reindexCheck858 : Integer.Sparse.reindex keyMap MixedData.row858 = numericRow858 := by decide +kernel

theorem numericCheck858 (x : Master → ℝ) : Integer.Sparse.eval numericRow858 x =
    (4320 : ℝ) * reducedSource858 x := by
  norm_num [numericRow858, reducedSource858, Integer.Sparse.eval, Sparse.eval, nodeValue2490, nodeValue2491, nodeValue2494, nodeValue2500, nodeValue2773, nodeValue3557, nodeValue3558, nodeValue3560, nodeValue3572, nodeValue3695, nodeValue3696, nodeValue3698, nodeValue3827, nodeValue3834, nodeValue3837, nodeValue3838, nodeValue3840, nodeValue3850, nodeValue3852, nodeValue3866, nodeValue3870, nodeValue3872, nodeValue3876, nodeValue3881, nodeValue3883, nodeValue3888, nodeValue3968, nodeValue3970, nodeValue3989, nodeValue3995]; ring

noncomputable def reducedSource859 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2921 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3441 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))))))))))))))

def numericRow859 : Integer.Sparse Master := [(Sum.inl 0, -336), (Sum.inl 2, -190), (Sum.inl 3, 800), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, 250), (Sum.inr 2921, 8640), (Sum.inr 2922, 8640), (Sum.inr 2928, 8640), (Sum.inr 2951, 8640), (Sum.inr 3097, 8640), (Sum.inr 3441, 8640), (Sum.inr 3447, 8640), (Sum.inr 3464, 8640), (Sum.inr 3573, 8640), (Sum.inr 3718, 8640), (Sum.inr 3722, 8640), (Sum.inr 3730, 8640), (Sum.inr 3752, 8640), (Sum.inr 3762, 8640), (Sum.inr 3794, 8640), (Sum.inr 3809, 8640), (Sum.inr 3839, 8640), (Sum.inr 3872, 8640), (Sum.inr 3873, 8640), (Sum.inr 3958, 8640), (Sum.inr 3959, 8640), (Sum.inr 4022, 8640)]

theorem reindexCheck859 : Integer.Sparse.reindex keyMap MixedData.row859 = numericRow859 := by decide +kernel

theorem numericCheck859 (x : Master → ℝ) : Integer.Sparse.eval numericRow859 x =
    (8640 : ℝ) * reducedSource859 x := by
  norm_num [numericRow859, reducedSource859, Integer.Sparse.eval, Sparse.eval, nodeValue2921, nodeValue2922, nodeValue2928, nodeValue2951, nodeValue3097, nodeValue3441, nodeValue3447, nodeValue3464, nodeValue3573, nodeValue3718, nodeValue3722, nodeValue3730, nodeValue3752, nodeValue3762, nodeValue3794, nodeValue3809, nodeValue3839, nodeValue3872, nodeValue3873, nodeValue3950, nodeValue3958, nodeValue3959, nodeValue3971, nodeValue3982, nodeValue3987, nodeValue3990, nodeValue3993, nodeValue4022, nodeValue4027, nodeValue4032]; ring

noncomputable def reducedSource860 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue4044 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow860 : Integer.Sparse Master := [(Sum.inr 3781, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem reindexCheck860 : Integer.Sparse.reindex keyMap MixedData.row860 = numericRow860 := by decide +kernel

theorem numericCheck860 (x : Master → ℝ) : Integer.Sparse.eval numericRow860 x =
    (1 : ℝ) * reducedSource860 x := by
  norm_num [numericRow860, reducedSource860, Integer.Sparse.eval, Sparse.eval, nodeValue3781, nodeValue3848, nodeValue3944, nodeValue3946, nodeValue3961, nodeValue4044, nodeValue4092]

noncomputable def reducedSource861 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2977 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3725 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3946 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow861 : Integer.Sparse Master := [(Sum.inr 2977, 1), (Sum.inr 3723, 1), (Sum.inr 3725, 1), (Sum.inr 3730, 1), (Sum.inr 3848, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

theorem reindexCheck861 : Integer.Sparse.reindex keyMap MixedData.row861 = numericRow861 := by decide +kernel

theorem numericCheck861 (x : Master → ℝ) : Integer.Sparse.eval numericRow861 x =
    (1 : ℝ) * reducedSource861 x := by
  norm_num [numericRow861, reducedSource861, Integer.Sparse.eval, Sparse.eval, nodeValue2977, nodeValue3723, nodeValue3725, nodeValue3730, nodeValue3848, nodeValue3946, nodeValue4092]

noncomputable def reducedSource862 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3828 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow862 : Integer.Sparse Master := [(Sum.inr 2975, 1), (Sum.inr 3826, 1), (Sum.inr 3828, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem reindexCheck862 : Integer.Sparse.reindex keyMap MixedData.row862 = numericRow862 := by decide +kernel

theorem numericCheck862 (x : Master → ℝ) : Integer.Sparse.eval numericRow862 x =
    (1 : ℝ) * reducedSource862 x := by
  norm_num [numericRow862, reducedSource862, Integer.Sparse.eval, Sparse.eval, nodeValue2975, nodeValue3826, nodeValue3828, nodeValue3848, nodeValue3884, nodeValue3944, nodeValue4092]

noncomputable def reducedSource863 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))))))

def numericRow863 : Integer.Sparse Master := [(Sum.inl 0, 52), (Sum.inl 2, -3), (Sum.inl 3, 48), (Sum.inl 4, 80), (Sum.inl 1, -51), (Sum.inr 2515, -864), (Sum.inr 2519, -432), (Sum.inr 2522, -432), (Sum.inr 2684, -864), (Sum.inr 2685, -432), (Sum.inr 2686, -432), (Sum.inr 2782, -432), (Sum.inr 2884, -864), (Sum.inr 2889, -432), (Sum.inr 3394, -864), (Sum.inr 3397, -432), (Sum.inr 3479, -864), (Sum.inr 3486, -432), (Sum.inr 3583, -432), (Sum.inr 3621, -864), (Sum.inr 3627, -432), (Sum.inr 3631, -432), (Sum.inr 3633, -432), (Sum.inr 3706, -864), (Sum.inr 3771, -864), (Sum.inr 3900, -864), (Sum.inr 3903, -864), (Sum.inr 3907, -432), (Sum.inr 3910, -864), (Sum.inr 3913, -864), (Sum.inr 3964, -864), (Sum.inr 3983, -1728)]

theorem reindexCheck863 : Integer.Sparse.reindex keyMap MixedData.row863 = numericRow863 := by decide +kernel

theorem numericCheck863 (x : Master → ℝ) : Integer.Sparse.eval numericRow863 x =
    (1728 : ℝ) * reducedSource863 x := by
  norm_num [numericRow863, reducedSource863, Integer.Sparse.eval, Sparse.eval, nodeValue5105, nodeValue5109, nodeValue5110, nodeValue5203, nodeValue5207, nodeValue5237, nodeValue5238, nodeValue5293, nodeValue5304, nodeValue5310, nodeValue5370, nodeValue5422, nodeValue5434, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5454, nodeValue5455, nodeValue5484, nodeValue5492, nodeValue5494]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
