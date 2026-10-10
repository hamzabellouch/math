import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
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

noncomputable def reducedSource784 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue3717 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3729 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow784 : Integer.Sparse Master := [(Sum.inr 2971, 1), (Sum.inr 3717, 1), (Sum.inr 3720, 1), (Sum.inr 3729, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem reindexCheck784 : Integer.Sparse.reindex keyMap MixedData.row784 = numericRow784 := by decide +kernel

theorem numericCheck784 (x : Master → ℝ) : Integer.Sparse.eval numericRow784 x =
    (1 : ℝ) * reducedSource784 x := by
  norm_num [numericRow784, reducedSource784, Integer.Sparse.eval, Sparse.eval, nodeValue2971, nodeValue3717, nodeValue3720, nodeValue3729, nodeValue3730, nodeValue3840, nodeValue4092]

noncomputable def reducedSource785 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2578 x + ((1 : ℝ) * Sparse.eval nodeValue3717 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow785 : Integer.Sparse Master := [(Sum.inr 2549, 1), (Sum.inr 2578, 1), (Sum.inr 3717, 1), (Sum.inr 3780, 1), (Sum.inr 3840, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem reindexCheck785 : Integer.Sparse.reindex keyMap MixedData.row785 = numericRow785 := by decide +kernel

theorem numericCheck785 (x : Master → ℝ) : Integer.Sparse.eval numericRow785 x =
    (1 : ℝ) * reducedSource785 x := by
  norm_num [numericRow785, reducedSource785, Integer.Sparse.eval, Sparse.eval, nodeValue2549, nodeValue2578, nodeValue3717, nodeValue3780, nodeValue3840, nodeValue3841, nodeValue4092]

noncomputable def reducedSource786 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3698 x + ((1 : ℝ) * Sparse.eval nodeValue3712 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0))))))))))))))))))))))))))))

def numericRow786 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 5, 40), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 35, 80), (Sum.inl 51, -240), (Sum.inl 3, 640), (Sum.inl 13, 80), (Sum.inl 52, 80), (Sum.inl 55, -240), (Sum.inl 12, 240), (Sum.inl 26, 160), (Sum.inl 4, 400), (Sum.inl 27, -60), (Sum.inl 1, -40), (Sum.inr 1992, 4320), (Sum.inr 1993, 4320), (Sum.inr 2001, 4320), (Sum.inr 2034, 4320), (Sum.inr 2196, 4320), (Sum.inr 2905, 4320), (Sum.inr 2907, 4320), (Sum.inr 2933, 4320), (Sum.inr 3038, 4320), (Sum.inr 3517, 4320), (Sum.inr 3518, 4320), (Sum.inr 3541, 4320), (Sum.inr 3561, 4320), (Sum.inr 3679, 4320), (Sum.inr 3698, 4320), (Sum.inr 3712, 4320), (Sum.inr 3723, 4320), (Sum.inr 3762, 4320), (Sum.inr 3796, 4320), (Sum.inr 3814, 4320), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3839, 4320), (Sum.inr 3840, 4320), (Sum.inr 3872, 8640)]

theorem reindexCheck786 : Integer.Sparse.reindex keyMap MixedData.row786 = numericRow786 := by decide +kernel

theorem numericCheck786 (x : Master → ℝ) : Integer.Sparse.eval numericRow786 x =
    (4320 : ℝ) * reducedSource786 x := by
  norm_num [numericRow786, reducedSource786, Integer.Sparse.eval, Sparse.eval, nodeValue1992, nodeValue1993, nodeValue2001, nodeValue2034, nodeValue2196, nodeValue2905, nodeValue2907, nodeValue2933, nodeValue3038, nodeValue3517, nodeValue3518, nodeValue3541, nodeValue3561, nodeValue3679, nodeValue3698, nodeValue3712, nodeValue3723, nodeValue3762, nodeValue3796, nodeValue3814, nodeValue3830, nodeValue3834, nodeValue3838, nodeValue3839, nodeValue3840, nodeValue3853, nodeValue3856, nodeValue3872, nodeValue3990]; ring

noncomputable def reducedSource787 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))))))))

def numericRow787 : Integer.Sparse Master := [(Sum.inl 0, 111), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 200), (Sum.inl 1, 640), (Sum.inr 2110, -2160), (Sum.inr 2112, -1080), (Sum.inr 2115, -1080), (Sum.inr 2275, -2160), (Sum.inr 2276, -1080), (Sum.inr 2279, -2160), (Sum.inr 2287, -1080), (Sum.inr 2954, -2160), (Sum.inr 3606, -2160), (Sum.inr 3614, -1080), (Sum.inr 3633, -1080), (Sum.inr 3732, -2160), (Sum.inr 3789, -2160), (Sum.inr 3810, -2160), (Sum.inr 3811, -2160), (Sum.inr 3814, -4320), (Sum.inr 3885, -4320), (Sum.inr 3886, -2160), (Sum.inr 3891, -2160), (Sum.inr 3893, -1080), (Sum.inr 3902, -2160), (Sum.inr 3907, -3240)]

theorem reindexCheck787 : Integer.Sparse.reindex keyMap MixedData.row787 = numericRow787 := by decide +kernel

theorem numericCheck787 (x : Master → ℝ) : Integer.Sparse.eval numericRow787 x =
    (4320 : ℝ) * reducedSource787 x := by
  norm_num [numericRow787, reducedSource787, Integer.Sparse.eval, Sparse.eval, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue5170, nodeValue5176, nodeValue5310, nodeValue5384, nodeValue5387, nodeValue5389, nodeValue5403, nodeValue5412, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5448, nodeValue5449, nodeValue5455, nodeValue5456, nodeValue5491]; ring

noncomputable def reducedSource788 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3732 x + ((2 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((2 : ℝ) * Sparse.eval nodeValue3789 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((2 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((2 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + ((2 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

def numericRow788 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -310), (Sum.inr 2110, 1440), (Sum.inr 2112, 720), (Sum.inr 2115, 720), (Sum.inr 2279, 720), (Sum.inr 2954, 1440), (Sum.inr 3732, 1440), (Sum.inr 3789, 1440), (Sum.inr 3814, 1440), (Sum.inr 3885, 1440), (Sum.inr 3886, 720), (Sum.inr 3907, 720)]

theorem reindexCheck788 : Integer.Sparse.reindex keyMap MixedData.row788 = numericRow788 := by decide +kernel

theorem numericCheck788 (x : Master → ℝ) : Integer.Sparse.eval numericRow788 x =
    (720 : ℝ) * reducedSource788 x := by
  norm_num [numericRow788, reducedSource788, Integer.Sparse.eval, Sparse.eval, nodeValue2110, nodeValue2112, nodeValue2115, nodeValue2279, nodeValue2954, nodeValue2968, nodeValue3121, nodeValue3732, nodeValue3739, nodeValue3740, nodeValue3789, nodeValue3814, nodeValue3885, nodeValue3886, nodeValue3889, nodeValue3907, nodeValue3916, nodeValue4012, nodeValue4014, nodeValue4019, nodeValue4037]; ring

noncomputable def reducedSource789 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))))))))))))))

def numericRow789 : Integer.Sparse Master := [(Sum.inl 0, 211), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, -160), (Sum.inl 1, -260), (Sum.inr 2058, -4320), (Sum.inr 2062, -2160), (Sum.inr 2065, -2160), (Sum.inr 2216, -4320), (Sum.inr 2218, -2160), (Sum.inr 2230, -2160), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2672, -4320), (Sum.inr 2686, -2160), (Sum.inr 2765, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3582, -2160), (Sum.inr 3624, -4320), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160), (Sum.inr 3706, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3796, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3906, -4320), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320)]

theorem reindexCheck789 : Integer.Sparse.reindex keyMap MixedData.row789 = numericRow789 := by decide +kernel

theorem numericCheck789 (x : Master → ℝ) : Integer.Sparse.eval numericRow789 x =
    (8640 : ℝ) * reducedSource789 x := by
  norm_num [numericRow789, reducedSource789, Integer.Sparse.eval, Sparse.eval, nodeValue4839, nodeValue4843, nodeValue4845, nodeValue4896, nodeValue5204, nodeValue5207, nodeValue5228, nodeValue5238, nodeValue5291, nodeValue5294, nodeValue5370, nodeValue5397, nodeValue5411, nodeValue5435, nodeValue5438, nodeValue5450, nodeValue5451, nodeValue5453, nodeValue5454, nodeValue5492]; ring

noncomputable def reducedSource790 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((2 : ℝ) * Sparse.eval nodeValue3706 x + ((2 : ℝ) * Sparse.eval nodeValue3782 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

def numericRow790 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 140), (Sum.inr 2058, 2160), (Sum.inr 2062, 1080), (Sum.inr 2065, 1080), (Sum.inr 2266, 1080), (Sum.inr 2881, 2160), (Sum.inr 2889, 1080), (Sum.inr 3391, 2160), (Sum.inr 3397, 1080), (Sum.inr 3582, 1080), (Sum.inr 3706, 2160), (Sum.inr 3782, 2160), (Sum.inr 3809, 2160), (Sum.inr 3857, 2160), (Sum.inr 3913, 1080)]

theorem reindexCheck790 : Integer.Sparse.reindex keyMap MixedData.row790 = numericRow790 := by decide +kernel

theorem numericCheck790 (x : Master → ℝ) : Integer.Sparse.eval numericRow790 x =
    (1080 : ℝ) * reducedSource790 x := by
  norm_num [numericRow790, reducedSource790, Integer.Sparse.eval, Sparse.eval, nodeValue2058, nodeValue2062, nodeValue2065, nodeValue2266, nodeValue2881, nodeValue2889, nodeValue3101, nodeValue3391, nodeValue3397, nodeValue3582, nodeValue3706, nodeValue3782, nodeValue3809, nodeValue3853, nodeValue3857, nodeValue3912, nodeValue3913, nodeValue3987, nodeValue4015, nodeValue4029, nodeValue4040]; ring

noncomputable def reducedSource791 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5436 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))

def numericRow791 : Integer.Sparse Master := [(Sum.inl 0, 69), (Sum.inl 2, 30), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, -135), (Sum.inr 2743, -2160), (Sum.inr 2782, -2160), (Sum.inr 3054, -2160), (Sum.inr 3548, -2160), (Sum.inr 3583, -2160), (Sum.inr 3626, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3906, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5268, 8640), (Sum.inr 5276, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 17280), (Sum.inr 5425, 17280), (Sum.inr 5436, 17280)]

theorem reindexCheck791 : Integer.Sparse.reindex keyMap MixedData.row791 = numericRow791 := by decide +kernel

theorem numericCheck791 (x : Master → ℝ) : Integer.Sparse.eval numericRow791 x =
    (8640 : ℝ) * reducedSource791 x := by
  norm_num [numericRow791, reducedSource791, Integer.Sparse.eval, Sparse.eval, nodeValue5266, nodeValue5267, nodeValue5268, nodeValue5275, nodeValue5276, nodeValue5299, nodeValue5300, nodeValue5302, nodeValue5304, nodeValue5411, nodeValue5413, nodeValue5425, nodeValue5428, nodeValue5435, nodeValue5436, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5451]; ring

noncomputable def reducedSource792 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

def numericRow792 : Integer.Sparse Master := [(Sum.inl 0, -51), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 110), (Sum.inr 2732, 1440), (Sum.inr 2734, 720), (Sum.inr 2744, 720), (Sum.inr 3039, 1440), (Sum.inr 3055, 720), (Sum.inr 3573, 1440), (Sum.inr 3583, 720), (Sum.inr 3584, 720), (Sum.inr 3872, 1440), (Sum.inr 3876, 1440), (Sum.inr 3877, 1440)]

theorem reindexCheck792 : Integer.Sparse.reindex keyMap MixedData.row792 = numericRow792 := by decide +kernel

theorem numericCheck792 (x : Master → ℝ) : Integer.Sparse.eval numericRow792 x =
    (720 : ℝ) * reducedSource792 x := by
  norm_num [numericRow792, reducedSource792, Integer.Sparse.eval, Sparse.eval, nodeValue2732, nodeValue2734, nodeValue2744, nodeValue2776, nodeValue3039, nodeValue3055, nodeValue3110, nodeValue3573, nodeValue3583, nodeValue3584, nodeValue3853, nodeValue3861, nodeValue3862, nodeValue3872, nodeValue3876, nodeValue3877, nodeValue3883, nodeValue3888, nodeValue4001, nodeValue4003, nodeValue4006]; ring

noncomputable def reducedSource793 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))))

def numericRow793 : Integer.Sparse Master := [(Sum.inl 0, 641), (Sum.inl 2, -100), (Sum.inl 3, -320), (Sum.inl 4, -400), (Sum.inl 1, -685), (Sum.inr 2483, -4320), (Sum.inr 2485, -4320), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 2931, -4320), (Sum.inr 3477, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3481, -4320), (Sum.inr 3607, -4320), (Sum.inr 3612, -4320), (Sum.inr 3627, -4320), (Sum.inr 3632, -4320), (Sum.inr 3692, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3721, -4320), (Sum.inr 3769, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3836, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3892, -4320), (Sum.inr 3896, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -8640), (Sum.inr 3906, -4320), (Sum.inr 3913, -4320), (Sum.inr 3964, -4320), (Sum.inr 3983, -8640)]

theorem reindexCheck793 : Integer.Sparse.reindex keyMap MixedData.row793 = numericRow793 := by decide +kernel

theorem numericCheck793 (x : Master → ℝ) : Integer.Sparse.eval numericRow793 x =
    (17280 : ℝ) * reducedSource793 x := by
  norm_num [numericRow793, reducedSource793, Integer.Sparse.eval, Sparse.eval, nodeValue5076, nodeValue5078, nodeValue5080, nodeValue5105, nodeValue5148, nodeValue5152, nodeValue5169, nodeValue5293, nodeValue5294, nodeValue5354, nodeValue5355, nodeValue5370, nodeValue5380, nodeValue5388, nodeValue5416, nodeValue5422, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5442, nodeValue5451, nodeValue5454, nodeValue5455, nodeValue5481, nodeValue5484, nodeValue5490, nodeValue5492]; ring

noncomputable def reducedSource794 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))))))))))

def numericRow794 : Integer.Sparse Master := [(Sum.inl 0, -132), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 145), (Sum.inr 2483, 1080), (Sum.inr 2485, 1080), (Sum.inr 2488, 1080), (Sum.inr 2515, 1080), (Sum.inr 2931, 1080), (Sum.inr 3692, 1080), (Sum.inr 3693, 1080), (Sum.inr 3706, 1080), (Sum.inr 3721, 1080), (Sum.inr 3876, 1080), (Sum.inr 3964, 1080), (Sum.inr 3983, 1080)]

theorem reindexCheck794 : Integer.Sparse.reindex keyMap MixedData.row794 = numericRow794 := by decide +kernel

theorem numericCheck794 (x : Master → ℝ) : Integer.Sparse.eval numericRow794 x =
    (1080 : ℝ) * reducedSource794 x := by
  norm_num [numericRow794, reducedSource794, Integer.Sparse.eval, Sparse.eval, nodeValue2483, nodeValue2485, nodeValue2488, nodeValue2515, nodeValue2768, nodeValue2927, nodeValue2931, nodeValue2960, nodeValue3102, nodeValue3692, nodeValue3693, nodeValue3706, nodeValue3721, nodeValue3737, nodeValue3853, nodeValue3876, nodeValue3964, nodeValue3967, nodeValue3979, nodeValue3982, nodeValue3983, nodeValue3987, nodeValue4001, nodeValue4013, nodeValue4017, nodeValue4019, nodeValue4033, nodeValue4036, nodeValue4040]; ring

noncomputable def reducedSource795 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))))))))))))))))))))))

def numericRow795 : Integer.Sparse Master := [(Sum.inl 0, 355), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2020, -2160), (Sum.inr 2022, -2160), (Sum.inr 2029, -2160), (Sum.inr 2054, -2160), (Sum.inr 2202, -2160), (Sum.inr 2203, -2160), (Sum.inr 2206, -2160), (Sum.inr 2225, -2160), (Sum.inr 2244, -2160), (Sum.inr 2262, -2160), (Sum.inr 2553, -2160), (Sum.inr 2561, -2160), (Sum.inr 2722, -2160), (Sum.inr 3514, -2160), (Sum.inr 3522, -2160), (Sum.inr 3533, -2160), (Sum.inr 3603, -2160), (Sum.inr 3690, -2160), (Sum.inr 3694, -2160), (Sum.inr 3705, -2160), (Sum.inr 3764, -2160), (Sum.inr 3767, -2160), (Sum.inr 3773, -2160), (Sum.inr 3779, -2160), (Sum.inr 3781, -2160), (Sum.inr 3794, -2160), (Sum.inr 3797, -2160), (Sum.inr 3800, -2160), (Sum.inr 3805, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3845, -4320), (Sum.inr 3896, -2160), (Sum.inr 3898, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 4046, -2160), (Sum.inr 4047, -2160)]

theorem reindexCheck795 : Integer.Sparse.reindex keyMap MixedData.row795 = numericRow795 := by decide +kernel

theorem numericCheck795 (x : Master → ℝ) : Integer.Sparse.eval numericRow795 x =
    (8640 : ℝ) * reducedSource795 x := by
  norm_num [numericRow795, reducedSource795, Integer.Sparse.eval, Sparse.eval, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4835, nodeValue4888, nodeValue5134, nodeValue5141, nodeValue5168, nodeValue5258, nodeValue5352, nodeValue5356, nodeValue5368, nodeValue5393, nodeValue5395, nodeValue5405, nodeValue5416, nodeValue5418, nodeValue5424, nodeValue5428, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5452, nodeValue5482, nodeValue5483, nodeValue5486, nodeValue5490, nodeValue5499]; ring

noncomputable def reducedSource796 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3824 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3911 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + 0))))))))))))))))))))))))))))

def numericRow796 : Integer.Sparse Master := [(Sum.inl 0, -36), (Sum.inl 2, 5), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, -19), (Sum.inr 2020, 288), (Sum.inr 2022, 288), (Sum.inr 2029, 288), (Sum.inr 2054, 288), (Sum.inr 2244, 288), (Sum.inr 2553, 288), (Sum.inr 2561, 288), (Sum.inr 2722, 288), (Sum.inr 3690, 288), (Sum.inr 3694, 288), (Sum.inr 3705, 288), (Sum.inr 3779, 288), (Sum.inr 3781, 288), (Sum.inr 3800, 288), (Sum.inr 3838, 288), (Sum.inr 3845, 288), (Sum.inr 3902, 288)]

theorem reindexCheck796 : Integer.Sparse.reindex keyMap MixedData.row796 = numericRow796 := by decide +kernel

theorem numericCheck796 (x : Master → ℝ) : Integer.Sparse.eval numericRow796 x =
    (288 : ℝ) * reducedSource796 x := by
  norm_num [numericRow796, reducedSource796, Integer.Sparse.eval, Sparse.eval, nodeValue2020, nodeValue2022, nodeValue2029, nodeValue2054, nodeValue2244, nodeValue2553, nodeValue2561, nodeValue2594, nodeValue2722, nodeValue3690, nodeValue3694, nodeValue3705, nodeValue3779, nodeValue3781, nodeValue3800, nodeValue3821, nodeValue3824, nodeValue3838, nodeValue3845, nodeValue3851, nodeValue3852, nodeValue3858, nodeValue3902, nodeValue3911, nodeValue3981, nodeValue3992, nodeValue3999, nodeValue4013, nodeValue4054]; ring

noncomputable def reducedSource797 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))))))))))

def numericRow797 : Integer.Sparse Master := [(Sum.inl 0, 186), (Sum.inl 2, 85), (Sum.inl 3, 80), (Sum.inl 12, 160), (Sum.inl 4, -80), (Sum.inl 1, -305), (Sum.inr 2722, -4320), (Sum.inr 2739, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3800, -4320), (Sum.inr 3801, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -8640), (Sum.inr 3812, -4320), (Sum.inr 3813, -8640), (Sum.inr 3814, -8640), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320), (Sum.inr 5260, 17280), (Sum.inr 5289, 17280), (Sum.inr 5425, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5446, 17280)]

theorem reindexCheck797 : Integer.Sparse.reindex keyMap MixedData.row797 = numericRow797 := by decide +kernel

theorem numericCheck797 (x : Master → ℝ) : Integer.Sparse.eval numericRow797 x =
    (17280 : ℝ) * reducedSource797 x := by
  norm_num [numericRow797, reducedSource797, Integer.Sparse.eval, Sparse.eval, nodeValue5256, nodeValue5258, nodeValue5260, nodeValue5271, nodeValue5289, nodeValue5405, nodeValue5406, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5429, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5435, nodeValue5436, nodeValue5441, nodeValue5442, nodeValue5446, nodeValue5451, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5487]; ring

noncomputable def reducedSource798 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))))))))))))

def numericRow798 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, -35), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 85), (Sum.inr 3086, 1080), (Sum.inr 3097, 1080), (Sum.inr 3801, 1080), (Sum.inr 3809, 1080), (Sum.inr 3814, 1080), (Sum.inr 3872, 1080), (Sum.inr 3877, 1080), (Sum.inr 3954, 1080), (Sum.inr 3958, 1080), (Sum.inr 3959, 1080), (Sum.inr 3972, 1080)]

theorem reindexCheck798 : Integer.Sparse.reindex keyMap MixedData.row798 = numericRow798 := by decide +kernel

theorem numericCheck798 (x : Master → ℝ) : Integer.Sparse.eval numericRow798 x =
    (1080 : ℝ) * reducedSource798 x := by
  norm_num [numericRow798, reducedSource798, Integer.Sparse.eval, Sparse.eval, nodeValue3085, nodeValue3086, nodeValue3089, nodeValue3097, nodeValue3109, nodeValue3801, nodeValue3808, nodeValue3809, nodeValue3814, nodeValue3853, nodeValue3872, nodeValue3877, nodeValue3883, nodeValue3954, nodeValue3958, nodeValue3959, nodeValue3971, nodeValue3972, nodeValue3977, nodeValue3981, nodeValue3982, nodeValue3986, nodeValue3987, nodeValue3990, nodeValue3996, nodeValue4001, nodeValue4027, nodeValue4032, nodeValue4035, nodeValue4037]; ring

noncomputable def reducedSource799 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))))))))))

def numericRow799 : Integer.Sparse Master := [(Sum.inl 0, 573), (Sum.inl 2, -70), (Sum.inl 3, -320), (Sum.inl 12, -560), (Sum.inl 4, 240), (Sum.inl 1, -115), (Sum.inr 2023, -4320), (Sum.inr 2025, -4320), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -4320), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -4320), (Sum.inr 3692, -4320), (Sum.inr 3693, -4320), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3769, -4320), (Sum.inr 3770, -4320), (Sum.inr 3771, -4320), (Sum.inr 3782, -4320), (Sum.inr 3795, -4320), (Sum.inr 3796, -4320), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3849, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3875, -4320), (Sum.inr 3876, -4320), (Sum.inr 3891, -4320), (Sum.inr 3897, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -8640), (Sum.inr 3907, -4320), (Sum.inr 3910, -4320)]

theorem reindexCheck799 : Integer.Sparse.reindex keyMap MixedData.row799 = numericRow799 := by decide +kernel

theorem numericCheck799 (x : Master → ℝ) : Integer.Sparse.eval numericRow799 x =
    (17280 : ℝ) * reducedSource799 x := by
  norm_num [numericRow799, reducedSource799, Integer.Sparse.eval, Sparse.eval, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4839, nodeValue4889, nodeValue5149, nodeValue5152, nodeValue5172, nodeValue5294, nodeValue5354, nodeValue5355, nodeValue5370, nodeValue5378, nodeValue5387, nodeValue5397, nodeValue5406, nodeValue5417, nodeValue5431, nodeValue5432, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5443, nodeValue5450, nodeValue5453, nodeValue5454, nodeValue5490]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
