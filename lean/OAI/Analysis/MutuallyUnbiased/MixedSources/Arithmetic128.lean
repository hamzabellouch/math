import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
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

noncomputable def reducedSource2048 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4950 x + ((4 : ℝ) * Sparse.eval nodeValue4952 x + ((4 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5457 x + ((8 : ℝ) * Sparse.eval nodeValue5465 x + ((4 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))

def numericRow2048 : Integer.Sparse Master := [(Sum.inl 0, 528), (Sum.inl 27, -360), (Sum.inl 1, 120), (Sum.inl 30, -1440), (Sum.inr 2342, -25920), (Sum.inr 2344, -12960), (Sum.inr 3421, -25920), (Sum.inr 3422, -12960), (Sum.inr 3616, -12960), (Sum.inr 4042, -25920)]

theorem reindexCheck2048 : Integer.Sparse.reindex keyMap MixedData.row2048 = numericRow2048 := by decide +kernel

theorem numericCheck2048 (x : Master → ℝ) : Integer.Sparse.eval numericRow2048 x =
    (12960 : ℝ) * reducedSource2048 x := by
  norm_num [numericRow2048, reducedSource2048, Integer.Sparse.eval, Sparse.eval, nodeValue4950, nodeValue4952, nodeValue5177, nodeValue5457, nodeValue5465, nodeValue5487]
  ring

noncomputable def reducedSource2049 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue2342 x + ((4 : ℝ) * Sparse.eval nodeValue2344 x + ((4 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue3917 x + ((8 : ℝ) * Sparse.eval nodeValue3931 x + ((4 : ℝ) * Sparse.eval nodeValue4000 x + 0)))))

def numericRow2049 : Integer.Sparse Master := [(Sum.inl 0, -528), (Sum.inl 27, 360), (Sum.inl 1, -120), (Sum.inl 30, 1440), (Sum.inr 2342, 25920), (Sum.inr 2344, 12960)]

theorem reindexCheck2049 : Integer.Sparse.reindex keyMap MixedData.row2049 = numericRow2049 := by decide +kernel

theorem numericCheck2049 (x : Master → ℝ) : Integer.Sparse.eval numericRow2049 x =
    (3240 : ℝ) * reducedSource2049 x := by
  norm_num [numericRow2049, reducedSource2049, Integer.Sparse.eval, Sparse.eval, nodeValue2342, nodeValue2344, nodeValue2605, nodeValue3917, nodeValue3931, nodeValue4000]
  ring

noncomputable def reducedSource2050 (x : Master → ℝ) : ℝ :=
  (16 : ℝ) * Sparse.eval nodeValue5356 x + ((8 : ℝ) * Sparse.eval nodeValue5371 x + ((4 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5458 x + 0)))

def numericRow2050 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -45), (Sum.inr 3694, -12960), (Sum.inr 3773, -12960), (Sum.inr 3894, -3240)]

theorem reindexCheck2050 : Integer.Sparse.reindex keyMap MixedData.row2050 = numericRow2050 := by decide +kernel

theorem numericCheck2050 (x : Master → ℝ) : Integer.Sparse.eval numericRow2050 x =
    (3240 : ℝ) * reducedSource2050 x := by
  norm_num [numericRow2050, reducedSource2050, Integer.Sparse.eval, Sparse.eval, nodeValue5356, nodeValue5371, nodeValue5390, nodeValue5458]
  ring

noncomputable def reducedSource2051 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4932 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((2 : ℝ) * Sparse.eval nodeValue4934 x + ((2 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((2 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + 0))))))))))))))))))))

def numericRow2051 : Integer.Sparse Master := [(Sum.inr 2342, -1), (Sum.inr 2489, -1), (Sum.inr 2818, -1), (Sum.inr 2931, -2), (Sum.inr 3421, -1), (Sum.inr 3482, -1), (Sum.inr 3592, -1), (Sum.inr 3612, -2), (Sum.inr 3672, -1), (Sum.inr 3690, -2), (Sum.inr 3756, -1), (Sum.inr 3764, -2), (Sum.inr 3779, -1), (Sum.inr 3790, -1), (Sum.inr 3797, -1), (Sum.inr 3815, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4933, 8), (Sum.inr 4934, 8), (Sum.inr 4935, 8), (Sum.inr 4951, 8), (Sum.inr 4958, 4), (Sum.inr 5189, 4), (Sum.inr 5340, 4), (Sum.inr 5463, 4)]

theorem reindexCheck2051 : Integer.Sparse.reindex keyMap MixedData.row2051 = numericRow2051 := by decide +kernel

theorem numericCheck2051 (x : Master → ℝ) : Integer.Sparse.eval numericRow2051 x =
    (4 : ℝ) * reducedSource2051 x := by
  norm_num [numericRow2051, reducedSource2051, Integer.Sparse.eval, Sparse.eval, nodeValue4932, nodeValue4933, nodeValue4934, nodeValue4935, nodeValue4950, nodeValue4951, nodeValue4958, nodeValue4974, nodeValue5081, nodeValue5152, nodeValue5189, nodeValue5337, nodeValue5340, nodeValue5352, nodeValue5369, nodeValue5393, nodeValue5404, nodeValue5410, nodeValue5459, nodeValue5463, nodeValue5473]
  ring

noncomputable def reducedSource2052 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3409 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((2 : ℝ) * Sparse.eval nodeValue3415 x + ((2 : ℝ) * Sparse.eval nodeValue3418 x + ((2 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3421 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3511 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3592 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3756 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((2 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + 0))))))))))))))))))))

def numericRow2052 : Integer.Sparse Master := [(Sum.inr 3414, 2), (Sum.inr 3415, 2), (Sum.inr 3418, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3482, 1), (Sum.inr 3511, 1), (Sum.inr 3542, 1), (Sum.inr 3592, 1), (Sum.inr 3612, 2), (Sum.inr 3756, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2)]

theorem reindexCheck2052 : Integer.Sparse.reindex keyMap MixedData.row2052 = numericRow2052 := by decide +kernel

theorem numericCheck2052 (x : Master → ℝ) : Integer.Sparse.eval numericRow2052 x =
    (1 : ℝ) * reducedSource2052 x := by
  norm_num [numericRow2052, reducedSource2052, Integer.Sparse.eval, Sparse.eval, nodeValue3409, nodeValue3414, nodeValue3415, nodeValue3418, nodeValue3419, nodeValue3421, nodeValue3482, nodeValue3511, nodeValue3542, nodeValue3592, nodeValue3612, nodeValue3756, nodeValue3763, nodeValue3764, nodeValue3774, nodeValue3797, nodeValue3815, nodeValue3816, nodeValue3951, nodeValue3960, nodeValue3961]

noncomputable def reducedSource2053 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue3672 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3920 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow2053 : Integer.Sparse Master := [(Sum.inr 2822, 2), (Sum.inr 3672, 1), (Sum.inr 3694, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

theorem reindexCheck2053 : Integer.Sparse.reindex keyMap MixedData.row2053 = numericRow2053 := by decide +kernel

theorem numericCheck2053 (x : Master → ℝ) : Integer.Sparse.eval numericRow2053 x =
    (1 : ℝ) * reducedSource2053 x := by
  norm_num [numericRow2053, reducedSource2053, Integer.Sparse.eval, Sparse.eval, nodeValue2822, nodeValue3672, nodeValue3694, nodeValue3779, nodeValue3920, nodeValue4091]

noncomputable def reducedSource2054 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2322 x + ((1 : ℝ) * Sparse.eval nodeValue2799 x + ((1 : ℝ) * Sparse.eval nodeValue3675 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow2054 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 3675, 1), (Sum.inr 3690, 2), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem reindexCheck2054 : Integer.Sparse.reindex keyMap MixedData.row2054 = numericRow2054 := by decide +kernel

theorem numericCheck2054 (x : Master → ℝ) : Integer.Sparse.eval numericRow2054 x =
    (1 : ℝ) * reducedSource2054 x := by
  norm_num [numericRow2054, reducedSource2054, Integer.Sparse.eval, Sparse.eval, nodeValue2322, nodeValue2799, nodeValue3675, nodeValue3690, nodeValue3694, nodeValue4091]

noncomputable def reducedSource2055 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue3675 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3790 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow2055 : Integer.Sparse Master := [(Sum.inr 2827, 2), (Sum.inr 3675, 1), (Sum.inr 3694, 1), (Sum.inr 3790, 1), (Sum.inr 3929, 1), (Sum.inr 4091, -1)]

theorem reindexCheck2055 : Integer.Sparse.reindex keyMap MixedData.row2055 = numericRow2055 := by decide +kernel

theorem numericCheck2055 (x : Master → ℝ) : Integer.Sparse.eval numericRow2055 x =
    (1 : ℝ) * reducedSource2055 x := by
  norm_num [numericRow2055, reducedSource2055, Integer.Sparse.eval, Sparse.eval, nodeValue2827, nodeValue3675, nodeValue3694, nodeValue3790, nodeValue3929, nodeValue4091]

noncomputable def reducedSource2056 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((4 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((4 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5335 x + ((4 : ℝ) * Sparse.eval nodeValue5367 x + ((4 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))

def numericRow2056 : Integer.Sparse Master := [(Sum.inr 2337, -4), (Sum.inr 2344, -1), (Sum.inr 2345, -2), (Sum.inr 2813, -4), (Sum.inr 2820, -1), (Sum.inr 2889, -2), (Sum.inr 3412, -4), (Sum.inr 3422, -1), (Sum.inr 3423, -2), (Sum.inr 3595, -4), (Sum.inr 3596, -1), (Sum.inr 3631, -2), (Sum.inr 3670, -2), (Sum.inr 3705, -4), (Sum.inr 3753, -2), (Sum.inr 3767, -4), (Sum.inr 3963, -2), (Sum.inr 4092, 4)]

theorem reindexCheck2056 : Integer.Sparse.reindex keyMap MixedData.row2056 = numericRow2056 := by decide +kernel

theorem numericCheck2056 (x : Master → ℝ) : Integer.Sparse.eval numericRow2056 x =
    (4 : ℝ) * reducedSource2056 x := by
  norm_num [numericRow2056, reducedSource2056, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4946, nodeValue4952, nodeValue4953, nodeValue4977, nodeValue4979, nodeValue5111, nodeValue5207, nodeValue5335, nodeValue5367, nodeValue5368, nodeValue5413, nodeValue5475]
  ring

noncomputable def reducedSource2057 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3485 x + ((4 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((2 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3753 x + ((4 : ℝ) * Sparse.eval nodeValue3766 x + ((4 : ℝ) * Sparse.eval nodeValue3767 x + ((2 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

def numericRow2057 : Integer.Sparse Master := [(Sum.inr 3412, 4), (Sum.inr 3422, 1), (Sum.inr 3423, 2), (Sum.inr 3595, 4), (Sum.inr 3596, 1), (Sum.inr 3631, 2), (Sum.inr 3753, 2), (Sum.inr 3767, 4), (Sum.inr 3963, 1), (Sum.inr 4092, 1)]

theorem reindexCheck2057 : Integer.Sparse.reindex keyMap MixedData.row2057 = numericRow2057 := by decide +kernel

theorem numericCheck2057 (x : Master → ℝ) : Integer.Sparse.eval numericRow2057 x =
    (1 : ℝ) * reducedSource2057 x := by
  norm_num [numericRow2057, reducedSource2057, Integer.Sparse.eval, Sparse.eval, nodeValue3412, nodeValue3422, nodeValue3423, nodeValue3485, nodeValue3595, nodeValue3596, nodeValue3631, nodeValue3753, nodeValue3766, nodeValue3767, nodeValue3817, nodeValue3963, nodeValue4092]

noncomputable def reducedSource2058 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4075 x + ((4 : ℝ) * Sparse.eval nodeValue4076 x + ((4 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4086 x + ((8 : ℝ) * Sparse.eval nodeValue4088 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow2058 : Integer.Sparse Master := [(Sum.inr 4075, 8), (Sum.inr 4076, 4), (Sum.inr 4082, 4), (Sum.inr 4086, 2), (Sum.inr 4088, 8), (Sum.inr 4092, 4)]

theorem reindexCheck2058 : Integer.Sparse.reindex keyMap MixedData.row2058 = numericRow2058 := by decide +kernel

theorem numericCheck2058 (x : Master → ℝ) : Integer.Sparse.eval numericRow2058 x =
    (1 : ℝ) * reducedSource2058 x := by
  norm_num [numericRow2058, reducedSource2058, Integer.Sparse.eval, Sparse.eval, nodeValue4075, nodeValue4076, nodeValue4082, nodeValue4086, nodeValue4088, nodeValue4092]

noncomputable def reducedSource2059 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5372 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + 0))))))))))))))))))))

def numericRow2059 : Integer.Sparse Master := [(Sum.inl 0, 342), (Sum.inl 5, -60), (Sum.inl 2, 30), (Sum.inl 7, -240), (Sum.inl 3, -480), (Sum.inl 23, 720), (Sum.inl 12, -240), (Sum.inl 27, 180), (Sum.inl 1, 1800), (Sum.inr 1811, -4320), (Sum.inr 1812, -4320), (Sum.inr 1814, -8640), (Sum.inr 2110, -4320), (Sum.inr 2156, -4320), (Sum.inr 2157, -8640), (Sum.inr 2165, -4320), (Sum.inr 2275, -4320), (Sum.inr 2814, -4320), (Sum.inr 2815, -4320), (Sum.inr 2817, -8640), (Sum.inr 2896, -4320), (Sum.inr 3585, -4320), (Sum.inr 3588, -4320), (Sum.inr 3591, -8640), (Sum.inr 3597, -4320), (Sum.inr 3603, -4320), (Sum.inr 3614, -8640), (Sum.inr 3708, -8640), (Sum.inr 3731, -4320), (Sum.inr 3732, -8640), (Sum.inr 3789, -4320), (Sum.inr 3791, -8640), (Sum.inr 3810, -4320), (Sum.inr 3811, -8640), (Sum.inr 3867, -4320), (Sum.inr 3885, -8640), (Sum.inr 3891, -8640), (Sum.inr 3893, -8640), (Sum.inr 3895, -4320), (Sum.inr 3902, -4320), (Sum.inr 3907, -8640)]

theorem reindexCheck2059 : Integer.Sparse.reindex keyMap MixedData.row2059 = numericRow2059 := by decide +kernel

theorem numericCheck2059 (x : Master → ℝ) : Integer.Sparse.eval numericRow2059 x =
    (17280 : ℝ) * reducedSource2059 x := by
  norm_num [numericRow2059, reducedSource2059, Integer.Sparse.eval, Sparse.eval, nodeValue4685, nodeValue4686, nodeValue4688, nodeValue4869, nodeValue4967, nodeValue4970, nodeValue4973, nodeValue5114, nodeValue5168, nodeValue5176, nodeValue5372, nodeValue5383, nodeValue5384, nodeValue5387, nodeValue5389, nodeValue5403, nodeValue5415, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5448]
  ring

noncomputable def reducedSource2060 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5336 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + 0))))))))))))))))))))

def numericRow2060 : Integer.Sparse Master := [(Sum.inl 0, 90), (Sum.inl 5, -12), (Sum.inl 2, 6), (Sum.inl 7, -48), (Sum.inl 3, -96), (Sum.inl 23, 144), (Sum.inl 12, -48), (Sum.inl 27, 36), (Sum.inl 1, -180), (Sum.inr 1802, -1296), (Sum.inr 1804, -1296), (Sum.inr 1810, -2592), (Sum.inr 1966, -1296), (Sum.inr 1970, -1296), (Sum.inr 2028, -2592), (Sum.inr 2106, -1296), (Sum.inr 2141, -1296), (Sum.inr 2143, -1296), (Sum.inr 2152, -2592), (Sum.inr 2177, -1296), (Sum.inr 2186, -1296), (Sum.inr 2215, -2592), (Sum.inr 2242, -1296), (Sum.inr 2807, -1296), (Sum.inr 2813, -2592), (Sum.inr 3590, -1296), (Sum.inr 3595, -2592), (Sum.inr 3613, -1296), (Sum.inr 3671, -2592), (Sum.inr 3693, -2592), (Sum.inr 3719, -2592), (Sum.inr 3754, -2592), (Sum.inr 3770, -2592), (Sum.inr 3786, -1296), (Sum.inr 3795, -2592), (Sum.inr 3799, -1296), (Sum.inr 3850, -5184), (Sum.inr 3890, -1296), (Sum.inr 3892, -2592), (Sum.inr 3897, -1296), (Sum.inr 3906, -2592), (Sum.inr 3910, -1296)]

theorem reindexCheck2060 : Integer.Sparse.reindex keyMap MixedData.row2060 = numericRow2060 := by decide +kernel

theorem numericCheck2060 (x : Master → ℝ) : Integer.Sparse.eval numericRow2060 x =
    (5184 : ℝ) * reducedSource2060 x := by
  norm_num [numericRow2060, reducedSource2060, Integer.Sparse.eval, Sparse.eval, nodeValue4676, nodeValue4678, nodeValue4684, nodeValue4766, nodeValue4770, nodeValue4810, nodeValue4865, nodeValue4971, nodeValue4977, nodeValue5172, nodeValue5336, nodeValue5355, nodeValue5378, nodeValue5386, nodeValue5388, nodeValue5400, nodeValue5417, nodeValue5432, nodeValue5435, nodeValue5440, nodeValue5450]
  ring

noncomputable def reducedSource2061 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((2 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + 0))))))))))))))))))))

def numericRow2061 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 5, 30), (Sum.inl 2, -10), (Sum.inl 7, 80), (Sum.inl 8, 40), (Sum.inl 3, 160), (Sum.inl 24, -360), (Sum.inl 4, 80), (Sum.inl 27, -90), (Sum.inl 1, -125), (Sum.inr 2672, -4320), (Sum.inr 2684, -2160), (Sum.inr 2705, -2160), (Sum.inr 3391, -4320), (Sum.inr 3394, -2160), (Sum.inr 3498, -2160), (Sum.inr 3689, -2160), (Sum.inr 3692, -2160), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3721, -2160), (Sum.inr 3732, -4320), (Sum.inr 3757, -2160), (Sum.inr 3769, -2160), (Sum.inr 3771, -4320), (Sum.inr 3795, -4320), (Sum.inr 3811, -4320), (Sum.inr 3836, -2160), (Sum.inr 3892, -4320), (Sum.inr 3898, -2160), (Sum.inr 5219, 8640), (Sum.inr 5222, 8640), (Sum.inr 5231, 8640), (Sum.inr 5233, 17280), (Sum.inr 5243, 8640), (Sum.inr 5264, 17280), (Sum.inr 5279, 8640), (Sum.inr 5381, 17280)]

theorem reindexCheck2061 : Integer.Sparse.reindex keyMap MixedData.row2061 = numericRow2061 := by decide +kernel

theorem numericCheck2061 (x : Master → ℝ) : Integer.Sparse.eval numericRow2061 x =
    (8640 : ℝ) * reducedSource2061 x := by
  norm_num [numericRow2061, reducedSource2061, Integer.Sparse.eval, Sparse.eval, nodeValue5219, nodeValue5222, nodeValue5228, nodeValue5231, nodeValue5233, nodeValue5237, nodeValue5243, nodeValue5248, nodeValue5264, nodeValue5279, nodeValue5351, nodeValue5354, nodeValue5367, nodeValue5369, nodeValue5370, nodeValue5378, nodeValue5380, nodeValue5381, nodeValue5384, nodeValue5388, nodeValue5418]
  ring

noncomputable def reducedSource2062 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5373 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))))))))))

def numericRow2062 : Integer.Sparse Master := [(Sum.inl 0, 423), (Sum.inl 5, -60), (Sum.inl 2, 30), (Sum.inl 7, -240), (Sum.inl 3, -480), (Sum.inl 24, 720), (Sum.inl 4, -240), (Sum.inl 27, 180), (Sum.inl 1, -225), (Sum.inr 1805, -4320), (Sum.inr 1807, -4320), (Sum.inr 1810, -4320), (Sum.inr 1815, -4320), (Sum.inr 2107, -4320), (Sum.inr 2150, -4320), (Sum.inr 2151, -4320), (Sum.inr 2152, -4320), (Sum.inr 2166, -4320), (Sum.inr 2260, -4320), (Sum.inr 2431, -4320), (Sum.inr 2434, -4320), (Sum.inr 2488, -4320), (Sum.inr 2809, -4320), (Sum.inr 2813, -4320), (Sum.inr 2818, -4320), (Sum.inr 3453, -4320), (Sum.inr 3457, -4320), (Sum.inr 3478, -4320), (Sum.inr 3587, -4320), (Sum.inr 3592, -4320), (Sum.inr 3595, -4320), (Sum.inr 3607, -4320), (Sum.inr 3614, -4320), (Sum.inr 3671, -4320), (Sum.inr 3693, -4320), (Sum.inr 3709, -4320), (Sum.inr 3721, -4320), (Sum.inr 3754, -4320), (Sum.inr 3770, -4320), (Sum.inr 3787, -4320), (Sum.inr 3792, -4320), (Sum.inr 3804, -4320), (Sum.inr 3836, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3890, -4320), (Sum.inr 3891, -4320), (Sum.inr 3892, -8640), (Sum.inr 3894, -4320), (Sum.inr 3896, -4320), (Sum.inr 3903, -4320), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320)]

theorem reindexCheck2062 : Integer.Sparse.reindex keyMap MixedData.row2062 = numericRow2062 := by decide +kernel

theorem numericCheck2062 (x : Master → ℝ) : Integer.Sparse.eval numericRow2062 x =
    (17280 : ℝ) * reducedSource2062 x := by
  norm_num [numericRow2062, reducedSource2062, Integer.Sparse.eval, Sparse.eval, nodeValue4679, nodeValue4681, nodeValue4684, nodeValue4689, nodeValue4866, nodeValue4968, nodeValue4972, nodeValue4974, nodeValue4977, nodeValue5038, nodeValue5080, nodeValue5169, nodeValue5176, nodeValue5336, nodeValue5355, nodeValue5373, nodeValue5380, nodeValue5386, nodeValue5387, nodeValue5388, nodeValue5390, nodeValue5401, nodeValue5416, nodeValue5434, nodeValue5438, nodeValue5440, nodeValue5442, nodeValue5450, nodeValue5451]
  ring

noncomputable def reducedSource2063 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5226 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5288 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + 0))))))))))))))))

def numericRow2063 : Integer.Sparse Master := [(Sum.inl 0, 978), (Sum.inl 5, 480), (Sum.inl 2, -180), (Sum.inl 7, 1440), (Sum.inl 8, 480), (Sum.inl 3, 2880), (Sum.inl 23, -2880), (Sum.inl 24, -1440), (Sum.inl 12, 960), (Sum.inl 4, 480), (Sum.inl 27, -1440), (Sum.inl 1, 1050), (Sum.inl 30, -1440), (Sum.inr 2672, -51840), (Sum.inr 2684, -51840), (Sum.inr 3391, -51840), (Sum.inr 3394, -51840), (Sum.inr 3690, -51840), (Sum.inr 3705, -51840), (Sum.inr 3719, -51840), (Sum.inr 3721, -51840), (Sum.inr 3732, -51840), (Sum.inr 3764, -51840), (Sum.inr 3767, -51840), (Sum.inr 3795, -51840), (Sum.inr 3811, -51840), (Sum.inr 3836, -51840), (Sum.inr 3891, -51840), (Sum.inr 3892, -25920), (Sum.inr 4042, -25920), (Sum.inr 5226, 207360), (Sum.inr 5229, 207360), (Sum.inr 5288, 103680), (Sum.inr 5379, 207360), (Sum.inr 5385, 103680)]

theorem reindexCheck2063 : Integer.Sparse.reindex keyMap MixedData.row2063 = numericRow2063 := by decide +kernel

theorem numericCheck2063 (x : Master → ℝ) : Integer.Sparse.eval numericRow2063 x =
    (103680 : ℝ) * reducedSource2063 x := by
  norm_num [numericRow2063, reducedSource2063, Integer.Sparse.eval, Sparse.eval, nodeValue5226, nodeValue5228, nodeValue5229, nodeValue5237, nodeValue5288, nodeValue5352, nodeValue5367, nodeValue5368, nodeValue5369, nodeValue5378, nodeValue5379, nodeValue5380, nodeValue5384, nodeValue5385, nodeValue5387, nodeValue5388, nodeValue5465]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
