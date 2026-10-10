import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
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

noncomputable def reducedSource912 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5047 x + ((2 : ℝ) * Sparse.eval nodeValue5050 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0)))))))))))))))))

def numericRow912 : Integer.Sparse Master := [(Sum.inl 0, 4974), (Sum.inl 5, -120), (Sum.inl 6, 30), (Sum.inl 2, -660), (Sum.inl 8, -960), (Sum.inl 3, -960), (Sum.inl 4, -1920), (Sum.inl 27, 360), (Sum.inl 1, 6240), (Sum.inl 30, 1440), (Sum.inr 2449, -25920), (Sum.inr 2452, -51840), (Sum.inr 2462, -51840), (Sum.inr 2480, -51840), (Sum.inr 2723, -51840), (Sum.inr 3432, -25920), (Sum.inr 3433, -51840), (Sum.inr 3436, -51840), (Sum.inr 3467, -51840), (Sum.inr 3544, -51840), (Sum.inr 3678, -25920), (Sum.inr 3683, -51840), (Sum.inr 3690, -51840), (Sum.inr 3744, -25920), (Sum.inr 3746, -51840), (Sum.inr 3764, -51840), (Sum.inr 3838, -51840), (Sum.inr 3843, -51840), (Sum.inr 3942, -51840), (Sum.inr 3958, -51840), (Sum.inr 3961, -51840), (Sum.inr 3974, -103680), (Sum.inr 4045, -25920), (Sum.inr 4046, -51840), (Sum.inr 4047, -51840)]

theorem reindexCheck912 : Integer.Sparse.reindex keyMap MixedData.row912 = numericRow912 := by decide +kernel

theorem numericCheck912 (x : Master → ℝ) : Integer.Sparse.eval numericRow912 x =
    (103680 : ℝ) * reducedSource912 x := by
  norm_num [numericRow912, reducedSource912, Integer.Sparse.eval, Sparse.eval, nodeValue5047, nodeValue5050, nodeValue5059, nodeValue5073, nodeValue5259, nodeValue5341, nodeValue5346, nodeValue5352, nodeValue5424, nodeValue5467, nodeValue5473, nodeValue5476, nodeValue5478, nodeValue5482, nodeValue5483, nodeValue5490, nodeValue5491, nodeValue5500]
  ring

noncomputable def reducedSource913 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2449 x + ((2 : ℝ) * Sparse.eval nodeValue2452 x + ((2 : ℝ) * Sparse.eval nodeValue2462 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3678 x + ((2 : ℝ) * Sparse.eval nodeValue3683 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3942 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + 0)))))))))))))))))

def numericRow913 : Integer.Sparse Master := [(Sum.inl 0, -3318), (Sum.inl 5, 120), (Sum.inl 6, -30), (Sum.inl 2, 660), (Sum.inl 8, 960), (Sum.inl 3, 960), (Sum.inl 4, 1920), (Sum.inl 27, -360), (Sum.inl 1, -4440), (Sum.inl 30, -1440), (Sum.inr 2449, 25920), (Sum.inr 2452, 51840), (Sum.inr 2462, 51840), (Sum.inr 2480, 51840), (Sum.inr 2723, 51840), (Sum.inr 3678, 25920), (Sum.inr 3683, 51840), (Sum.inr 3690, 51840), (Sum.inr 3838, 51840), (Sum.inr 3942, 25920), (Sum.inr 3958, 51840), (Sum.inr 3974, 51840)]

theorem reindexCheck913 : Integer.Sparse.reindex keyMap MixedData.row913 = numericRow913 := by decide +kernel

theorem numericCheck913 (x : Master → ℝ) : Integer.Sparse.eval numericRow913 x =
    (25920 : ℝ) * reducedSource913 x := by
  norm_num [numericRow913, reducedSource913, Integer.Sparse.eval, Sparse.eval, nodeValue2449, nodeValue2452, nodeValue2462, nodeValue2480, nodeValue2723, nodeValue3678, nodeValue3683, nodeValue3690, nodeValue3838, nodeValue3942, nodeValue3958, nodeValue3965, nodeValue3974, nodeValue3980, nodeValue3981, nodeValue4013, nodeValue4014, nodeValue4053]
  ring

noncomputable def reducedSource914 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))

def numericRow914 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 3781, -4320), (Sum.inr 3782, -4320), (Sum.inr 3794, -4320), (Sum.inr 3796, -4320), (Sum.inr 3837, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3903, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320), (Sum.inr 5420, 8640), (Sum.inr 5421, 17280), (Sum.inr 5425, 17280), (Sum.inr 5430, 17280), (Sum.inr 5445, 17280)]

theorem reindexCheck914 : Integer.Sparse.reindex keyMap MixedData.row914 = numericRow914 := by decide +kernel

theorem numericCheck914 (x : Master → ℝ) : Integer.Sparse.eval numericRow914 x =
    (8640 : ℝ) * reducedSource914 x := by
  norm_num [numericRow914, reducedSource914, Integer.Sparse.eval, Sparse.eval, nodeValue5394, nodeValue5395, nodeValue5397, nodeValue5410, nodeValue5420, nodeValue5421, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5430, nodeValue5434, nodeValue5445, nodeValue5468, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5487]
  ring

noncomputable def reducedSource915 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3793 x + ((2 : ℝ) * Sparse.eval nodeValue3794 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((2 : ℝ) * Sparse.eval nodeValue3873 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((2 : ℝ) * Sparse.eval nodeValue3972 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + 0)))))))))))))))))

def numericRow915 : Integer.Sparse Master := [(Sum.inl 0, -141), (Sum.inl 2, -55), (Sum.inl 3, 480), (Sum.inl 12, 160), (Sum.inl 25, -120), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 10), (Sum.inr 3794, 4320), (Sum.inr 3796, 4320), (Sum.inr 3838, 4320), (Sum.inr 3870, 2160), (Sum.inr 3872, 4320), (Sum.inr 3873, 4320), (Sum.inr 3880, 4320), (Sum.inr 3958, 4320), (Sum.inr 3972, 4320)]

theorem reindexCheck915 : Integer.Sparse.reindex keyMap MixedData.row915 = numericRow915 := by decide +kernel

theorem numericCheck915 (x : Master → ℝ) : Integer.Sparse.eval numericRow915 x =
    (2160 : ℝ) * reducedSource915 x := by
  norm_num [numericRow915, reducedSource915, Integer.Sparse.eval, Sparse.eval, nodeValue3793, nodeValue3794, nodeValue3796, nodeValue3808, nodeValue3838, nodeValue3870, nodeValue3872, nodeValue3873, nodeValue3880, nodeValue3950, nodeValue3958, nodeValue3972, nodeValue3981, nodeValue3982, nodeValue3986, nodeValue3989, nodeValue3990, nodeValue4032]
  ring

noncomputable def reducedSource916 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))))))))))

def numericRow916 : Integer.Sparse Master := [(Sum.inl 0, 40), (Sum.inl 2, -30), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 210), (Sum.inr 2556, -2160), (Sum.inr 2723, -2160), (Sum.inr 2924, -2160), (Sum.inr 3521, -2160), (Sum.inr 3544, -2160), (Sum.inr 3605, -2160), (Sum.inr 3721, -2160), (Sum.inr 3779, -2160), (Sum.inr 3797, -2160), (Sum.inr 3836, -2160), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3849, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3902, -2160), (Sum.inr 3974, -4320), (Sum.inr 4046, -2160), (Sum.inr 5128, 8640), (Sum.inr 5129, 8640), (Sum.inr 5138, 8640), (Sum.inr 5145, 8640), (Sum.inr 5251, 8640), (Sum.inr 5377, 8640), (Sum.inr 5379, 8640), (Sum.inr 5419, 8640), (Sum.inr 5421, 8640), (Sum.inr 5429, 8640), (Sum.inr 5430, 8640), (Sum.inr 5480, 8640)]

theorem reindexCheck916 : Integer.Sparse.reindex keyMap MixedData.row916 = numericRow916 := by decide +kernel

theorem numericCheck916 (x : Master → ℝ) : Integer.Sparse.eval numericRow916 x =
    (8640 : ℝ) * reducedSource916 x := by
  norm_num [numericRow916, reducedSource916, Integer.Sparse.eval, Sparse.eval, nodeValue5128, nodeValue5129, nodeValue5130, nodeValue5137, nodeValue5138, nodeValue5145, nodeValue5149, nodeValue5251, nodeValue5259, nodeValue5377, nodeValue5379, nodeValue5380, nodeValue5393, nodeValue5396, nodeValue5410, nodeValue5419, nodeValue5421, nodeValue5424, nodeValue5427, nodeValue5429, nodeValue5430, nodeValue5431, nodeValue5438, nodeValue5439, nodeValue5440, nodeValue5478, nodeValue5480, nodeValue5481, nodeValue5482]
  ring

noncomputable def reducedSource917 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + 0))))))))))))))))))))))))))))

def numericRow917 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 2, 30), (Sum.inl 12, -40), (Sum.inl 4, 80), (Sum.inl 1, -210), (Sum.inr 3516, 2160), (Sum.inr 3517, 2160), (Sum.inr 3519, 2160), (Sum.inr 3521, 2160), (Sum.inr 3539, 2160), (Sum.inr 3544, 2160), (Sum.inr 3562, 2160), (Sum.inr 3605, 2160), (Sum.inr 3797, 2160), (Sum.inr 3832, 2160), (Sum.inr 3835, 2160), (Sum.inr 3836, 2160), (Sum.inr 3842, 2160), (Sum.inr 3843, 4320), (Sum.inr 3848, 2160), (Sum.inr 3857, 2160), (Sum.inr 3873, 2160), (Sum.inr 3874, 2160), (Sum.inr 3875, 2160), (Sum.inr 3974, 2160), (Sum.inr 3978, 2160)]

theorem reindexCheck917 : Integer.Sparse.reindex keyMap MixedData.row917 = numericRow917 := by decide +kernel

theorem numericCheck917 (x : Master → ℝ) : Integer.Sparse.eval numericRow917 x =
    (2160 : ℝ) * reducedSource917 x := by
  norm_num [numericRow917, reducedSource917, Integer.Sparse.eval, Sparse.eval, nodeValue3516, nodeValue3517, nodeValue3519, nodeValue3520, nodeValue3521, nodeValue3539, nodeValue3544, nodeValue3562, nodeValue3605, nodeValue3797, nodeValue3798, nodeValue3816, nodeValue3832, nodeValue3835, nodeValue3836, nodeValue3842, nodeValue3843, nodeValue3844, nodeValue3848, nodeValue3857, nodeValue3858, nodeValue3859, nodeValue3873, nodeValue3874, nodeValue3875, nodeValue3974, nodeValue3978, nodeValue3991, nodeValue3992]
  ring

noncomputable def reducedSource918 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5341 x + ((1 : ℝ) * Sparse.eval nodeValue5344 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))))))))))

def numericRow918 : Integer.Sparse Master := [(Sum.inl 0, 1662), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -510), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -1920), (Sum.inl 24, 720), (Sum.inl 12, -720), (Sum.inl 4, -2160), (Sum.inl 27, 180), (Sum.inl 1, 2445), (Sum.inr 1987, -12960), (Sum.inr 1990, -12960), (Sum.inr 1996, -12960), (Sum.inr 1997, -12960), (Sum.inr 2000, -25920), (Sum.inr 2020, -12960), (Sum.inr 2051, -12960), (Sum.inr 2191, -12960), (Sum.inr 2202, -12960), (Sum.inr 2452, -12960), (Sum.inr 2459, -12960), (Sum.inr 2479, -12960), (Sum.inr 2722, -12960), (Sum.inr 3429, -12960), (Sum.inr 3433, -12960), (Sum.inr 3459, -12960), (Sum.inr 3533, -12960), (Sum.inr 3678, -12960), (Sum.inr 3681, -25920), (Sum.inr 3683, -25920), (Sum.inr 3689, -12960), (Sum.inr 3690, -12960), (Sum.inr 3703, -12960), (Sum.inr 3744, -12960), (Sum.inr 3746, -25920), (Sum.inr 3757, -12960), (Sum.inr 3758, -12960), (Sum.inr 3764, -12960), (Sum.inr 3837, -25920), (Sum.inr 3838, -25920), (Sum.inr 3843, -25920), (Sum.inr 3845, -25920), (Sum.inr 3896, -12960), (Sum.inr 3901, -25920), (Sum.inr 3902, -12960), (Sum.inr 3903, -12960), (Sum.inr 3974, -25920), (Sum.inr 4046, -12960)]

theorem reindexCheck918 : Integer.Sparse.reindex keyMap MixedData.row918 = numericRow918 := by decide +kernel

theorem numericCheck918 (x : Master → ℝ) : Integer.Sparse.eval numericRow918 x =
    (51840 : ℝ) * reducedSource918 x := by
  norm_num [numericRow918, reducedSource918, Integer.Sparse.eval, Sparse.eval, nodeValue4779, nodeValue4782, nodeValue4787, nodeValue4802, nodeValue4831, nodeValue5050, nodeValue5056, nodeValue5072, nodeValue5258, nodeValue5341, nodeValue5344, nodeValue5346, nodeValue5351, nodeValue5352, nodeValue5365, nodeValue5416, nodeValue5423, nodeValue5424, nodeValue5428, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5490, nodeValue5500]
  ring

noncomputable def reducedSource919 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue1990 x + ((1 : ℝ) * Sparse.eval nodeValue2000 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3678 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3746 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + 0)))))))))))))))))))))))))))))

def numericRow919 : Integer.Sparse Master := [(Sum.inl 0, -993), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, 360), (Sum.inl 7, 240), (Sum.inl 8, 240), (Sum.inl 3, 1440), (Sum.inl 24, -720), (Sum.inl 12, 480), (Sum.inl 4, 1440), (Sum.inl 27, -180), (Sum.inl 1, -1200), (Sum.inr 1987, 12960), (Sum.inr 1990, 12960), (Sum.inr 2000, 12960), (Sum.inr 2020, 12960), (Sum.inr 2191, 12960), (Sum.inr 2452, 12960), (Sum.inr 2459, 12960), (Sum.inr 2479, 12960), (Sum.inr 2722, 12960), (Sum.inr 3678, 12960), (Sum.inr 3681, 12960), (Sum.inr 3683, 12960), (Sum.inr 3689, 12960), (Sum.inr 3690, 12960), (Sum.inr 3746, 12960), (Sum.inr 3758, 12960), (Sum.inr 3837, 12960), (Sum.inr 3838, 12960), (Sum.inr 3843, 12960), (Sum.inr 3845, 12960), (Sum.inr 3901, 12960), (Sum.inr 3902, 12960), (Sum.inr 3974, 12960)]

theorem reindexCheck919 : Integer.Sparse.reindex keyMap MixedData.row919 = numericRow919 := by decide +kernel

theorem numericCheck919 (x : Master → ℝ) : Integer.Sparse.eval numericRow919 x =
    (12960 : ℝ) * reducedSource919 x := by
  norm_num [numericRow919, reducedSource919, Integer.Sparse.eval, Sparse.eval, nodeValue1987, nodeValue1990, nodeValue2000, nodeValue2020, nodeValue2191, nodeValue2452, nodeValue2459, nodeValue2479, nodeValue2722, nodeValue3678, nodeValue3681, nodeValue3683, nodeValue3689, nodeValue3690, nodeValue3746, nodeValue3758, nodeValue3821, nodeValue3837, nodeValue3838, nodeValue3843, nodeValue3845, nodeValue3851, nodeValue3852, nodeValue3901, nodeValue3902, nodeValue3971, nodeValue3974, nodeValue3980, nodeValue4013, nodeValue4053]
  ring

noncomputable def reducedSource920 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5426 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))

def numericRow920 : Integer.Sparse Master := [(Sum.inl 0, 150), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -255), (Sum.inr 2553, -4320), (Sum.inr 2739, -4320), (Sum.inr 3514, -4320), (Sum.inr 3534, -4320), (Sum.inr 3719, -4320), (Sum.inr 3781, -4320), (Sum.inr 3782, -4320), (Sum.inr 3794, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4047, -4320), (Sum.inr 5138, 17280), (Sum.inr 5160, 17280), (Sum.inr 5379, 17280), (Sum.inr 5381, 17280), (Sum.inr 5382, 17280), (Sum.inr 5425, 51840), (Sum.inr 5426, 17280), (Sum.inr 5430, 17280), (Sum.inr 5445, 17280)]

theorem reindexCheck920 : Integer.Sparse.reindex keyMap MixedData.row920 = numericRow920 := by decide +kernel

theorem numericCheck920 (x : Master → ℝ) : Integer.Sparse.eval numericRow920 x =
    (17280 : ℝ) * reducedSource920 x := by
  norm_num [numericRow920, reducedSource920, Integer.Sparse.eval, Sparse.eval, nodeValue5134, nodeValue5135, nodeValue5138, nodeValue5160, nodeValue5271, nodeValue5378, nodeValue5379, nodeValue5381, nodeValue5382, nodeValue5394, nodeValue5395, nodeValue5397, nodeValue5409, nodeValue5410, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5426, nodeValue5428, nodeValue5430, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5442, nodeValue5445, nodeValue5477, nodeValue5483]
  ring

noncomputable def reducedSource921 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0)))))))))))))))))))))))))))))

def numericRow921 : Integer.Sparse Master := [(Sum.inl 0, -328), (Sum.inl 2, -100), (Sum.inl 3, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 340), (Sum.inr 3514, 8640), (Sum.inr 3517, 8640), (Sum.inr 3534, 8640), (Sum.inr 3558, 8640), (Sum.inr 3794, 8640), (Sum.inr 3795, 8640), (Sum.inr 3796, 8640), (Sum.inr 3832, 8640), (Sum.inr 3834, 8640), (Sum.inr 3837, 8640), (Sum.inr 3839, 8640), (Sum.inr 3840, 8640), (Sum.inr 3841, 8640), (Sum.inr 3845, 8640), (Sum.inr 3866, 8640), (Sum.inr 3871, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3880, 8640)]

theorem reindexCheck921 : Integer.Sparse.reindex keyMap MixedData.row921 = numericRow921 := by decide +kernel

theorem numericCheck921 (x : Master → ℝ) : Integer.Sparse.eval numericRow921 x =
    (8640 : ℝ) * reducedSource921 x := by
  norm_num [numericRow921, reducedSource921, Integer.Sparse.eval, Sparse.eval, nodeValue3514, nodeValue3515, nodeValue3517, nodeValue3534, nodeValue3558, nodeValue3793, nodeValue3794, nodeValue3795, nodeValue3796, nodeValue3807, nodeValue3808, nodeValue3832, nodeValue3834, nodeValue3837, nodeValue3839, nodeValue3840, nodeValue3841, nodeValue3845, nodeValue3852, nodeValue3853, nodeValue3861, nodeValue3866, nodeValue3871, nodeValue3872, nodeValue3876, nodeValue3880, nodeValue3971, nodeValue3981, nodeValue3989, nodeValue3990]
  ring

noncomputable def reducedSource922 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((4 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((4 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))

def numericRow922 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 1, 25), (Sum.inr 3607, -1440), (Sum.inr 3608, -360), (Sum.inr 3616, -720), (Sum.inr 3627, -720), (Sum.inr 4042, -1440), (Sum.inr 4043, -360), (Sum.inr 4045, -720), (Sum.inr 4047, -1440)]

theorem reindexCheck922 : Integer.Sparse.reindex keyMap MixedData.row922 = numericRow922 := by decide +kernel

theorem numericCheck922 (x : Master → ℝ) : Integer.Sparse.eval numericRow922 x =
    (1440 : ℝ) * reducedSource922 x := by
  norm_num [numericRow922, reducedSource922, Integer.Sparse.eval, Sparse.eval, nodeValue4096, nodeValue5169, nodeValue5171, nodeValue5177, nodeValue5293, nodeValue5465, nodeValue5466, nodeValue5476, nodeValue5483, nodeValue5486, nodeValue5487, nodeValue5491, nodeValue5493]
  ring

noncomputable def reducedSource923 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

def numericRow923 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 4, -80), (Sum.inl 1, -105), (Sum.inr 3607, -4320), (Sum.inr 3613, -4320), (Sum.inr 3614, -2160), (Sum.inr 3615, -2160), (Sum.inr 3616, -2160), (Sum.inr 3632, -2160), (Sum.inr 3892, -4320), (Sum.inr 3894, -2160), (Sum.inr 3896, -4320), (Sum.inr 3898, -4320), (Sum.inr 3903, -4320), (Sum.inr 3913, -2160), (Sum.inr 4010, -4320)]

theorem reindexCheck923 : Integer.Sparse.reindex keyMap MixedData.row923 = numericRow923 := by decide +kernel

theorem numericCheck923 (x : Master → ℝ) : Integer.Sparse.eval numericRow923 x =
    (8640 : ℝ) * reducedSource923 x := by
  norm_num [numericRow923, reducedSource923, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5169, nodeValue5172, nodeValue5174, nodeValue5176, nodeValue5177, nodeValue5294, nodeValue5309, nodeValue5388, nodeValue5390, nodeValue5416, nodeValue5418, nodeValue5434, nodeValue5440, nodeValue5442, nodeValue5451, nodeValue5455, nodeValue5485, nodeValue5492, nodeValue5493]
  ring

noncomputable def reducedSource924 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))))))

def numericRow924 : Integer.Sparse Master := [(Sum.inl 0, 83), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 80), (Sum.inl 4, 320), (Sum.inl 1, -150), (Sum.inr 2884, -4320), (Sum.inr 2931, -4320), (Sum.inr 3612, -4320), (Sum.inr 3621, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3764, -4320), (Sum.inr 3773, -4320), (Sum.inr 3885, -8640), (Sum.inr 3910, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -8640), (Sum.inr 3983, -8640), (Sum.inr 4010, -4320), (Sum.inr 5145, 17280), (Sum.inr 5147, 17280), (Sum.inr 5164, 17280), (Sum.inr 5185, 17280), (Sum.inr 5189, 17280), (Sum.inr 5266, 17280), (Sum.inr 5282, 17280), (Sum.inr 5445, 17280), (Sum.inr 5446, 17280), (Sum.inr 5463, 17280), (Sum.inr 5470, 17280)]

theorem reindexCheck924 : Integer.Sparse.reindex keyMap MixedData.row924 = numericRow924 := by decide +kernel

theorem numericCheck924 (x : Master → ℝ) : Integer.Sparse.eval numericRow924 x =
    (17280 : ℝ) * reducedSource924 x := by
  norm_num [numericRow924, reducedSource924, Integer.Sparse.eval, Sparse.eval, nodeValue5145, nodeValue5147, nodeValue5152, nodeValue5164, nodeValue5185, nodeValue5189, nodeValue5203, nodeValue5266, nodeValue5282, nodeValue5352, nodeValue5356, nodeValue5369, nodeValue5410, nodeValue5445, nodeValue5446, nodeValue5448, nodeValue5450, nodeValue5459, nodeValue5463, nodeValue5469, nodeValue5470, nodeValue5471, nodeValue5472, nodeValue5473, nodeValue5474, nodeValue5478, nodeValue5484, nodeValue5485, nodeValue5486]
  ring

noncomputable def reducedSource925 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3952 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((1 : ℝ) * Sparse.eval nodeValue4024 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))))))))))

def numericRow925 : Integer.Sparse Master := [(Sum.inl 0, -91), (Sum.inl 2, 35), (Sum.inl 3, -400), (Sum.inl 12, -240), (Sum.inl 25, 240), (Sum.inl 4, -320), (Sum.inl 1, 50), (Sum.inr 3529, 4320), (Sum.inr 3530, 4320), (Sum.inr 3535, 4320), (Sum.inr 3542, 4320), (Sum.inr 3562, 4320), (Sum.inr 3565, 4320), (Sum.inr 3580, 4320), (Sum.inr 3612, 4320), (Sum.inr 3621, 4320), (Sum.inr 3764, 4320), (Sum.inr 3773, 4320), (Sum.inr 3952, 4320), (Sum.inr 3955, 4320), (Sum.inr 3957, 4320), (Sum.inr 3959, 4320), (Sum.inr 3960, 4320), (Sum.inr 3961, 8640), (Sum.inr 3974, 4320), (Sum.inr 3983, 4320), (Sum.inr 4024, 4320)]

theorem reindexCheck925 : Integer.Sparse.reindex keyMap MixedData.row925 = numericRow925 := by decide +kernel

theorem numericCheck925 (x : Master → ℝ) : Integer.Sparse.eval numericRow925 x =
    (4320 : ℝ) * reducedSource925 x := by
  norm_num [numericRow925, reducedSource925, Integer.Sparse.eval, Sparse.eval, nodeValue3529, nodeValue3530, nodeValue3535, nodeValue3542, nodeValue3562, nodeValue3565, nodeValue3580, nodeValue3612, nodeValue3621, nodeValue3764, nodeValue3773, nodeValue3774, nodeValue3816, nodeValue3951, nodeValue3952, nodeValue3955, nodeValue3956, nodeValue3957, nodeValue3959, nodeValue3960, nodeValue3961, nodeValue3962, nodeValue3974, nodeValue3983, nodeValue3984, nodeValue3985, nodeValue4024, nodeValue4028, nodeValue4029]
  ring

noncomputable def reducedSource926 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5346 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))

def numericRow926 : Integer.Sparse Master := [(Sum.inl 0, 571), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 10), (Sum.inr 2383, -4320), (Sum.inr 2385, -4320), (Sum.inr 2388, -4320), (Sum.inr 2398, -4320), (Sum.inr 2399, -4320), (Sum.inr 2400, -4320), (Sum.inr 2404, -8640), (Sum.inr 2462, -4320), (Sum.inr 2467, -4320), (Sum.inr 2512, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 3341, -4320), (Sum.inr 3344, -4320), (Sum.inr 3352, -4320), (Sum.inr 3353, -4320), (Sum.inr 3354, -4320), (Sum.inr 3357, -8640), (Sum.inr 3436, -4320), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3548, -4320), (Sum.inr 3683, -4320), (Sum.inr 3705, -4320), (Sum.inr 3746, -4320), (Sum.inr 3767, -4320), (Sum.inr 3845, -8640), (Sum.inr 3942, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3963, -8640), (Sum.inr 3974, -8640), (Sum.inr 4010, -4320), (Sum.inr 4047, -4320)]

theorem reindexCheck926 : Integer.Sparse.reindex keyMap MixedData.row926 = numericRow926 := by decide +kernel

theorem numericCheck926 (x : Master → ℝ) : Integer.Sparse.eval numericRow926 x =
    (17280 : ℝ) * reducedSource926 x := by
  norm_num [numericRow926, reducedSource926, Integer.Sparse.eval, Sparse.eval, nodeValue4998, nodeValue5000, nodeValue5003, nodeValue5013, nodeValue5014, nodeValue5015, nodeValue5018, nodeValue5059, nodeValue5102, nodeValue5259, nodeValue5271, nodeValue5275, nodeValue5346, nodeValue5368, nodeValue5428, nodeValue5467, nodeValue5469, nodeValue5472, nodeValue5473, nodeValue5475, nodeValue5477, nodeValue5478, nodeValue5483, nodeValue5485, nodeValue5490, nodeValue5491, nodeValue5492]
  ring

noncomputable def reducedSource927 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2467 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3341 x + ((1 : ℝ) * Sparse.eval nodeValue3344 x + ((1 : ℝ) * Sparse.eval nodeValue3357 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3942 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4050 x + 0)))))))))))))))))))))))))))))

def numericRow927 : Integer.Sparse Master := [(Sum.inl 0, -343), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 50), (Sum.inr 2383, 4320), (Sum.inr 2385, 4320), (Sum.inr 2388, 4320), (Sum.inr 2404, 4320), (Sum.inr 2462, 4320), (Sum.inr 2467, 4320), (Sum.inr 2512, 4320), (Sum.inr 2723, 4320), (Sum.inr 2743, 4320), (Sum.inr 3341, 4320), (Sum.inr 3344, 4320), (Sum.inr 3357, 4320), (Sum.inr 3534, 4320), (Sum.inr 3683, 4320), (Sum.inr 3705, 4320), (Sum.inr 3845, 4320), (Sum.inr 3942, 4320), (Sum.inr 3945, 4320), (Sum.inr 3957, 4320), (Sum.inr 3958, 4320), (Sum.inr 3961, 4320), (Sum.inr 3963, 4320), (Sum.inr 3974, 4320)]

theorem reindexCheck927 : Integer.Sparse.reindex keyMap MixedData.row927 = numericRow927 := by decide +kernel

theorem numericCheck927 (x : Master → ℝ) : Integer.Sparse.eval numericRow927 x =
    (4320 : ℝ) * reducedSource927 x := by
  norm_num [numericRow927, reducedSource927, Integer.Sparse.eval, Sparse.eval, nodeValue2383, nodeValue2385, nodeValue2388, nodeValue2404, nodeValue2462, nodeValue2467, nodeValue2512, nodeValue2723, nodeValue2743, nodeValue3341, nodeValue3344, nodeValue3357, nodeValue3534, nodeValue3683, nodeValue3705, nodeValue3845, nodeValue3942, nodeValue3945, nodeValue3957, nodeValue3958, nodeValue3961, nodeValue3963, nodeValue3971, nodeValue3974, nodeValue3981, nodeValue3984, nodeValue4013, nodeValue4014, nodeValue4015, nodeValue4050]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
