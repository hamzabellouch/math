import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
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

noncomputable def reducedSource944 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5127 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + 0)))))))))))))))))

def numericRow944 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3719, -4320), (Sum.inr 3795, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 5129, 17280), (Sum.inr 5144, 17280), (Sum.inr 5376, 8640), (Sum.inr 5381, 17280), (Sum.inr 5420, 8640), (Sum.inr 5425, 17280), (Sum.inr 5430, 17280)]

theorem reindexCheck944 : Integer.Sparse.reindex keyMap MixedData.row944 = numericRow944 := by decide +kernel

theorem numericCheck944 (x : Master → ℝ) : Integer.Sparse.eval numericRow944 x =
    (8640 : ℝ) * reducedSource944 x := by
  norm_num [numericRow944, reducedSource944, Integer.Sparse.eval, Sparse.eval, nodeValue5127, nodeValue5129, nodeValue5134, nodeValue5144, nodeValue5258, nodeValue5376, nodeValue5378, nodeValue5381, nodeValue5394, nodeValue5409, nodeValue5420, nodeValue5424, nodeValue5425, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5441, nodeValue5477]; ring

noncomputable def reducedSource945 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3513 x + ((2 : ℝ) * Sparse.eval nodeValue3514 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((2 : ℝ) * Sparse.eval nodeValue3795 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + 0)))))))))))))))))

def numericRow945 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 3514, 4320), (Sum.inr 3516, 4320), (Sum.inr 3533, 4320), (Sum.inr 3557, 4320), (Sum.inr 3795, 4320), (Sum.inr 3833, 2160), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3850, 4320), (Sum.inr 3870, 2160), (Sum.inr 3871, 4320)]

theorem reindexCheck945 : Integer.Sparse.reindex keyMap MixedData.row945 = numericRow945 := by decide +kernel

theorem numericCheck945 (x : Master → ℝ) : Integer.Sparse.eval numericRow945 x =
    (2160 : ℝ) * reducedSource945 x := by
  norm_num [numericRow945, reducedSource945, Integer.Sparse.eval, Sparse.eval, nodeValue3513, nodeValue3514, nodeValue3516, nodeValue3533, nodeValue3557, nodeValue3793, nodeValue3795, nodeValue3807, nodeValue3833, nodeValue3834, nodeValue3838, nodeValue3840, nodeValue3850, nodeValue3852, nodeValue3860, nodeValue3870, nodeValue3871, nodeValue3989]; ring

noncomputable def reducedSource946 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4778 x + ((4 : ℝ) * Sparse.eval nodeValue4782 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5344 x + ((4 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((2 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))

def numericRow946 : Integer.Sparse Master := [(Sum.inl 0, 117), (Sum.inl 5, -12), (Sum.inl 6, 3), (Sum.inl 2, -42), (Sum.inl 7, -96), (Sum.inl 3, -480), (Sum.inl 23, 144), (Sum.inl 12, -288), (Sum.inl 4, -288), (Sum.inl 27, 36), (Sum.inl 1, 366), (Sum.inr 1986, -2592), (Sum.inr 1990, -5184), (Sum.inr 1997, -5184), (Sum.inr 2019, -5184), (Sum.inr 2190, -5184), (Sum.inr 3678, -2592), (Sum.inr 3681, -5184), (Sum.inr 3689, -5184), (Sum.inr 3744, -2592), (Sum.inr 3757, -5184), (Sum.inr 3837, -5184), (Sum.inr 3838, -5184), (Sum.inr 3843, -5184), (Sum.inr 3895, -2592), (Sum.inr 3901, -5184)]

theorem reindexCheck946 : Integer.Sparse.reindex keyMap MixedData.row946 = numericRow946 := by decide +kernel

theorem numericCheck946 (x : Master → ℝ) : Integer.Sparse.eval numericRow946 x =
    (5184 : ℝ) * reducedSource946 x := by
  norm_num [numericRow946, reducedSource946, Integer.Sparse.eval, Sparse.eval, nodeValue4778, nodeValue4782, nodeValue4801, nodeValue5341, nodeValue5344, nodeValue5351, nodeValue5415, nodeValue5423, nodeValue5424, nodeValue5433, nodeValue5500]; ring

noncomputable def reducedSource947 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))

def numericRow947 : Integer.Sparse Master := [(Sum.inl 0, 2), (Sum.inl 1, 10), (Sum.inr 3603, -180), (Sum.inr 3608, -45), (Sum.inr 3614, -90), (Sum.inr 3891, -180), (Sum.inr 3893, -45), (Sum.inr 3895, -90), (Sum.inr 3902, -180), (Sum.inr 3907, -90)]

theorem reindexCheck947 : Integer.Sparse.reindex keyMap MixedData.row947 = numericRow947 := by decide +kernel

theorem numericCheck947 (x : Master → ℝ) : Integer.Sparse.eval numericRow947 x =
    (180 : ℝ) * reducedSource947 x := by
  norm_num [numericRow947, reducedSource947, Integer.Sparse.eval, Sparse.eval, nodeValue4094, nodeValue5168, nodeValue5171, nodeValue5176, nodeValue5308, nodeValue5387, nodeValue5389, nodeValue5415, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5455, nodeValue5491]; ring

noncomputable def reducedSource948 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

def numericRow948 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2479, -4320), (Sum.inr 2482, -4320), (Sum.inr 2488, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 3459, -4320), (Sum.inr 3468, -4320), (Sum.inr 3478, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3533, -4320), (Sum.inr 3564, -4320), (Sum.inr 3689, -4320), (Sum.inr 3693, -4320), (Sum.inr 3719, -4320), (Sum.inr 3732, -4320), (Sum.inr 3757, -4320), (Sum.inr 3770, -4320), (Sum.inr 3786, -4320), (Sum.inr 3795, -4320), (Sum.inr 3799, -4320), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3811, -4320), (Sum.inr 3813, -4320), (Sum.inr 3837, -8640), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 4092, 17280)]

theorem reindexCheck948 : Integer.Sparse.reindex keyMap MixedData.row948 = numericRow948 := by decide +kernel

theorem numericCheck948 (x : Master → ℝ) : Integer.Sparse.eval numericRow948 x =
    (17280 : ℝ) * reducedSource948 x := by
  norm_num [numericRow948, reducedSource948, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue5072, nodeValue5075, nodeValue5080, nodeValue5101, nodeValue5134, nodeValue5141, nodeValue5163, nodeValue5258, nodeValue5274, nodeValue5351, nodeValue5355, nodeValue5367, nodeValue5378, nodeValue5384, nodeValue5394, nodeValue5400, nodeValue5405, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5423, nodeValue5424, nodeValue5428, nodeValue5432, nodeValue5434, nodeValue5438, nodeValue5441, nodeValue5442, nodeValue5483]; ring

noncomputable def reducedSource949 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4090 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + ((1 : ℝ) * Sparse.eval nodeValue4096 x + 0)))))))))))

def numericRow949 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 1, -35), (Sum.inr 4080, 1440), (Sum.inr 4081, 360), (Sum.inr 4082, 720), (Sum.inr 4084, 720), (Sum.inr 4088, 1440), (Sum.inr 4089, 360), (Sum.inr 4090, 720), (Sum.inr 4091, 1440), (Sum.inr 4092, 2160)]

theorem reindexCheck949 : Integer.Sparse.reindex keyMap MixedData.row949 = numericRow949 := by decide +kernel

theorem numericCheck949 (x : Master → ℝ) : Integer.Sparse.eval numericRow949 x =
    (360 : ℝ) * reducedSource949 x := by
  norm_num [numericRow949, reducedSource949, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4084, nodeValue4088, nodeValue4089, nodeValue4090, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4094, nodeValue4096]; ring

noncomputable def reducedSource950 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5166 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))))))))

def numericRow950 : Integer.Sparse Master := [(Sum.inl 0, 613), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, -400), (Sum.inl 1, 2910), (Sum.inr 2954, -8640), (Sum.inr 3603, -4320), (Sum.inr 3606, -8640), (Sum.inr 3623, -4320), (Sum.inr 3731, -4320), (Sum.inr 3732, -8640), (Sum.inr 3789, -8640), (Sum.inr 3810, -8640), (Sum.inr 3811, -8640), (Sum.inr 3814, -17280), (Sum.inr 3867, -4320), (Sum.inr 3885, -8640), (Sum.inr 3891, -4320), (Sum.inr 3895, -4320), (Sum.inr 3899, -8640), (Sum.inr 3902, -17280), (Sum.inr 3907, -8640)]

theorem reindexCheck950 : Integer.Sparse.reindex keyMap MixedData.row950 = numericRow950 := by decide +kernel

theorem numericCheck950 (x : Master → ℝ) : Integer.Sparse.eval numericRow950 x =
    (17280 : ℝ) * reducedSource950 x := by
  norm_num [numericRow950, reducedSource950, Integer.Sparse.eval, Sparse.eval, nodeValue5166, nodeValue5168, nodeValue5170, nodeValue5306, nodeValue5383, nodeValue5384, nodeValue5387, nodeValue5403, nodeValue5412, nodeValue5415, nodeValue5437, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5448, nodeValue5453, nodeValue5455, nodeValue5488, nodeValue5491]; ring

noncomputable def reducedSource951 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

def numericRow951 : Integer.Sparse Master := [(Sum.inl 0, 773), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, 20), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -320), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, 240), (Sum.inl 4, 160), (Sum.inl 27, 180), (Sum.inl 1, -1080), (Sum.inr 2924, -8640), (Sum.inr 3602, -4320), (Sum.inr 3605, -8640), (Sum.inr 3622, -4320), (Sum.inr 3719, -8640), (Sum.inr 3721, -4320), (Sum.inr 3782, -8640), (Sum.inr 3795, -8640), (Sum.inr 3796, -8640), (Sum.inr 3801, -8640), (Sum.inr 3812, -8640), (Sum.inr 3836, -4320), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3890, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3903, -8640), (Sum.inr 3906, -8640), (Sum.inr 3910, -4320), (Sum.inr 3964, -4320)]

theorem reindexCheck951 : Integer.Sparse.reindex keyMap MixedData.row951 = numericRow951 := by decide +kernel

theorem numericCheck951 (x : Master → ℝ) : Integer.Sparse.eval numericRow951 x =
    (17280 : ℝ) * reducedSource951 x := by
  norm_num [numericRow951, reducedSource951, Integer.Sparse.eval, Sparse.eval, nodeValue5148, nodeValue5149, nodeValue5167, nodeValue5292, nodeValue5378, nodeValue5380, nodeValue5386, nodeValue5397, nodeValue5406, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5440, nodeValue5450, nodeValue5452, nodeValue5454, nodeValue5481, nodeValue5489, nodeValue5490]; ring

noncomputable def reducedSource952 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + 0))))))))))))))))))

def numericRow952 : Integer.Sparse Master := [(Sum.inl 0, 914), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -215), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -1360), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -400), (Sum.inl 4, -1440), (Sum.inl 27, 180), (Sum.inl 1, 1340), (Sum.inr 2019, -4320), (Sum.inr 2020, -8640), (Sum.inr 2051, -4320), (Sum.inr 2190, -4320), (Sum.inr 2191, -4320), (Sum.inr 2202, -8640), (Sum.inr 2243, -8640), (Sum.inr 3689, -4320), (Sum.inr 3690, -8640), (Sum.inr 3703, -4320), (Sum.inr 3757, -4320), (Sum.inr 3758, -4320), (Sum.inr 3764, -8640), (Sum.inr 3837, -17280), (Sum.inr 3838, -17280), (Sum.inr 3843, -17280), (Sum.inr 3895, -4320), (Sum.inr 3896, -8640), (Sum.inr 3901, -12960), (Sum.inr 3902, -4320), (Sum.inr 3903, -8640), (Sum.inr 4046, -4320)]

theorem reindexCheck952 : Integer.Sparse.reindex keyMap MixedData.row952 = numericRow952 := by decide +kernel

theorem numericCheck952 (x : Master → ℝ) : Integer.Sparse.eval numericRow952 x =
    (17280 : ℝ) * reducedSource952 x := by
  norm_num [numericRow952, reducedSource952, Integer.Sparse.eval, Sparse.eval, nodeValue4801, nodeValue4802, nodeValue4831, nodeValue4887, nodeValue5351, nodeValue5352, nodeValue5365, nodeValue5415, nodeValue5416, nodeValue5423, nodeValue5424, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5452, nodeValue5482, nodeValue5497, nodeValue5499, nodeValue5500]; ring

noncomputable def reducedSource953 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

def numericRow953 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2721, -2160), (Sum.inr 3532, -2160), (Sum.inr 3800, -1080), (Sum.inr 3801, -1080), (Sum.inr 3805, -1080), (Sum.inr 3812, -1080), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3899, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -1080), (Sum.inr 3909, -1080), (Sum.inr 3910, -1080), (Sum.inr 3974, -4320), (Sum.inr 4025, -1080), (Sum.inr 4046, -1080), (Sum.inr 5251, 4320), (Sum.inr 5281, 4320), (Sum.inr 5425, 8640), (Sum.inr 5430, 8640), (Sum.inr 5445, 8640)]

theorem reindexCheck953 : Integer.Sparse.reindex keyMap MixedData.row953 = numericRow953 := by decide +kernel

theorem numericCheck953 (x : Master → ℝ) : Integer.Sparse.eval numericRow953 x =
    (4320 : ℝ) * reducedSource953 x := by
  norm_num [numericRow953, reducedSource953, Integer.Sparse.eval, Sparse.eval, nodeValue5250, nodeValue5251, nodeValue5257, nodeValue5281, nodeValue5405, nodeValue5406, nodeValue5408, nodeValue5425, nodeValue5430, nodeValue5431, nodeValue5433, nodeValue5437, nodeValue5439, nodeValue5440, nodeValue5445, nodeValue5447, nodeValue5450, nodeValue5478, nodeValue5479, nodeValue5482, nodeValue5486]; ring

noncomputable def reducedSource954 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue5155 x + ((2 : ℝ) * Sparse.eval nodeValue5166 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5383 x + ((6 : ℝ) * Sparse.eval nodeValue5412 x + ((6 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))

def numericRow954 : Integer.Sparse Master := [(Sum.inl 0, 73), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 1, 310), (Sum.inr 2908, -4320), (Sum.inr 3053, -1440), (Sum.inr 3600, -4320), (Sum.inr 3619, -1440), (Sum.inr 3713, -4320), (Sum.inr 3731, -1440), (Sum.inr 3814, -8640), (Sum.inr 3867, -1440), (Sum.inr 3902, -4320)]

theorem reindexCheck954 : Integer.Sparse.reindex keyMap MixedData.row954 = numericRow954 := by decide +kernel

theorem numericCheck954 (x : Master → ℝ) : Integer.Sparse.eval numericRow954 x =
    (2880 : ℝ) * reducedSource954 x := by
  norm_num [numericRow954, reducedSource954, Integer.Sparse.eval, Sparse.eval, nodeValue5155, nodeValue5166, nodeValue5301, nodeValue5374, nodeValue5383, nodeValue5412, nodeValue5439, nodeValue5453]; ring

noncomputable def reducedSource955 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4815 x + ((1 : ℝ) * Sparse.eval nodeValue4830 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((3 : ℝ) * Sparse.eval nodeValue5359 x + ((3 : ℝ) * Sparse.eval nodeValue5406 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((6 : ℝ) * Sparse.eval nodeValue5425 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + 0)))))))))))

def numericRow955 : Integer.Sparse Master := [(Sum.inl 0, 29), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 90), (Sum.inr 3801, -4320), (Sum.inr 3812, -4320), (Sum.inr 3900, -4320), (Sum.inr 3901, -4320), (Sum.inr 3909, -2880), (Sum.inr 3964, -4320), (Sum.inr 4025, -2880), (Sum.inr 4815, 17280), (Sum.inr 4830, 5760), (Sum.inr 4885, 5760), (Sum.inr 5251, 17280), (Sum.inr 5277, 5760), (Sum.inr 5359, 17280), (Sum.inr 5425, 34560)]

theorem reindexCheck955 : Integer.Sparse.reindex keyMap MixedData.row955 = numericRow955 := by decide +kernel

theorem numericCheck955 (x : Master → ℝ) : Integer.Sparse.eval numericRow955 x =
    (5760 : ℝ) * reducedSource955 x := by
  norm_num [numericRow955, reducedSource955, Integer.Sparse.eval, Sparse.eval, nodeValue4815, nodeValue4830, nodeValue4885, nodeValue5251, nodeValue5277, nodeValue5359, nodeValue5406, nodeValue5422, nodeValue5425, nodeValue5433, nodeValue5447, nodeValue5479]; ring

noncomputable def reducedSource956 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4864 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

def numericRow956 : Integer.Sparse Master := [(Sum.inl 0, 56), (Sum.inl 2, 5), (Sum.inl 1, -55), (Sum.inr 2105, -360), (Sum.inr 2106, -360), (Sum.inr 2107, -720), (Sum.inr 2241, -360), (Sum.inr 2242, -360), (Sum.inr 2245, -360), (Sum.inr 2260, -720), (Sum.inr 2277, -360), (Sum.inr 3786, -360), (Sum.inr 3787, -720), (Sum.inr 3799, -360), (Sum.inr 3801, -360), (Sum.inr 3804, -720), (Sum.inr 3812, -360), (Sum.inr 3849, -720), (Sum.inr 3850, -1440), (Sum.inr 3857, -720), (Sum.inr 3875, -720), (Sum.inr 3876, -720), (Sum.inr 3890, -360), (Sum.inr 3891, -360), (Sum.inr 3892, -720), (Sum.inr 3906, -720), (Sum.inr 3910, -360), (Sum.inr 3913, -720)]

theorem reindexCheck956 : Integer.Sparse.reindex keyMap MixedData.row956 = numericRow956 := by decide +kernel

theorem numericCheck956 (x : Master → ℝ) : Integer.Sparse.eval numericRow956 x =
    (1440 : ℝ) * reducedSource956 x := by
  norm_num [numericRow956, reducedSource956, Integer.Sparse.eval, Sparse.eval, nodeValue4864, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue5386, nodeValue5387, nodeValue5388, nodeValue5400, nodeValue5401, nodeValue5406, nodeValue5431, nodeValue5432, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5450, nodeValue5451, nodeValue5453, nodeValue5489, nodeValue5490, nodeValue5493]; ring

noncomputable def reducedSource957 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

def numericRow957 : Integer.Sparse Master := [(Sum.inl 0, 65), (Sum.inl 2, -35), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 40), (Sum.inr 2764, -4320), (Sum.inr 3053, -2160), (Sum.inr 3581, -4320), (Sum.inr 3619, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3885, -8640), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 3909, -2160), (Sum.inr 3910, -4320), (Sum.inr 3957, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4025, -2160), (Sum.inr 5265, 8640), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640), (Sum.inr 5429, 8640), (Sum.inr 5445, 17280), (Sum.inr 5446, 17280)]

theorem reindexCheck957 : Integer.Sparse.reindex keyMap MixedData.row957 = numericRow957 := by decide +kernel

theorem numericCheck957 (x : Master → ℝ) : Integer.Sparse.eval numericRow957 x =
    (8640 : ℝ) * reducedSource957 x := by
  norm_num [numericRow957, reducedSource957, Integer.Sparse.eval, Sparse.eval, nodeValue5265, nodeValue5266, nodeValue5270, nodeValue5281, nodeValue5282, nodeValue5290, nodeValue5301, nodeValue5429, nodeValue5431, nodeValue5433, nodeValue5439, nodeValue5440, nodeValue5445, nodeValue5446, nodeValue5447, nodeValue5448, nodeValue5450, nodeValue5472, nodeValue5473, nodeValue5474, nodeValue5486]; ring

noncomputable def reducedSource958 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue5123 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5192 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5391 x + ((6 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5450 x + ((3 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))

def numericRow958 : Integer.Sparse Master := [(Sum.inl 0, 223), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 12, 240), (Sum.inl 4, 320), (Sum.inl 1, -450), (Sum.inr 2536, -4320), (Sum.inr 2589, -1440), (Sum.inr 2671, -1440), (Sum.inr 2853, -4320), (Sum.inr 2880, -1440), (Sum.inr 3370, -4320), (Sum.inr 3390, -1440), (Sum.inr 3563, -1440), (Sum.inr 3617, -1440), (Sum.inr 3620, -4320), (Sum.inr 3776, -4320), (Sum.inr 3778, -4320), (Sum.inr 3809, -8640), (Sum.inr 3813, -8640), (Sum.inr 3909, -1440), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320), (Sum.inr 4025, -1440)]

theorem reindexCheck958 : Integer.Sparse.reindex keyMap MixedData.row958 = numericRow958 := by decide +kernel

theorem numericCheck958 (x : Master → ℝ) : Integer.Sparse.eval numericRow958 x =
    (5760 : ℝ) * reducedSource958 x := by
  norm_num [numericRow958, reducedSource958, Integer.Sparse.eval, Sparse.eval, nodeValue5123, nodeValue5162, nodeValue5192, nodeValue5202, nodeValue5227, nodeValue5283, nodeValue5391, nodeValue5411, nodeValue5447, nodeValue5450, nodeValue5452, nodeValue5462, nodeValue5485]; ring

noncomputable def reducedSource959 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2853 x + ((1 : ℝ) * Sparse.eval nodeValue2880 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((3 : ℝ) * Sparse.eval nodeValue3370 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((3 : ℝ) * Sparse.eval nodeValue3778 x + ((6 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue4007 x + ((3 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4029 x + ((3 : ℝ) * Sparse.eval nodeValue4039 x + 0))))))))))))

def numericRow959 : Integer.Sparse Master := [(Sum.inl 0, -52), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 125), (Sum.inr 2853, 2160), (Sum.inr 2880, 720), (Sum.inr 3370, 2160), (Sum.inr 3390, 720), (Sum.inr 3563, 720), (Sum.inr 3778, 2160), (Sum.inr 3809, 4320), (Sum.inr 4010, 2160), (Sum.inr 4025, 720)]

theorem reindexCheck959 : Integer.Sparse.reindex keyMap MixedData.row959 = numericRow959 := by decide +kernel

theorem numericCheck959 (x : Master → ℝ) : Integer.Sparse.eval numericRow959 x =
    (720 : ℝ) * reducedSource959 x := by
  norm_num [numericRow959, reducedSource959, Integer.Sparse.eval, Sparse.eval, nodeValue2853, nodeValue2880, nodeValue3076, nodeValue3370, nodeValue3390, nodeValue3563, nodeValue3778, nodeValue3809, nodeValue4007, nodeValue4010, nodeValue4025, nodeValue4029, nodeValue4039]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
