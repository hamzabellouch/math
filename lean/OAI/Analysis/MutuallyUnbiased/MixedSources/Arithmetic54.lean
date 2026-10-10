import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
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

noncomputable def reducedSource864 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3394 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((2 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3964 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((2 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

def numericRow864 : Integer.Sparse Master := [(Sum.inl 0, -72), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 65), (Sum.inr 2515, 1440), (Sum.inr 2519, 720), (Sum.inr 2522, 720), (Sum.inr 2884, 1440), (Sum.inr 2889, 720), (Sum.inr 3394, 1440), (Sum.inr 3397, 720), (Sum.inr 3583, 720), (Sum.inr 3706, 1440), (Sum.inr 3964, 1440), (Sum.inr 3983, 1440)]

theorem reindexCheck864 : Integer.Sparse.reindex keyMap MixedData.row864 = numericRow864 := by decide +kernel

theorem numericCheck864 (x : Master → ℝ) : Integer.Sparse.eval numericRow864 x =
    (720 : ℝ) * reducedSource864 x := by
  norm_num [numericRow864, reducedSource864, Integer.Sparse.eval, Sparse.eval, nodeValue2515, nodeValue2519, nodeValue2522, nodeValue2788, nodeValue2884, nodeValue2889, nodeValue3102, nodeValue3394, nodeValue3397, nodeValue3583, nodeValue3706, nodeValue3862, nodeValue3964, nodeValue3982, nodeValue3983, nodeValue3987, nodeValue4015, nodeValue4019, nodeValue4020, nodeValue4029, nodeValue4040]
  ring

noncomputable def reducedSource865 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

def numericRow865 : Integer.Sparse Master := [(Sum.inl 0, 137), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2107, -2160), (Sum.inr 2109, -1080), (Sum.inr 2116, -1080), (Sum.inr 2260, -2160), (Sum.inr 2261, -1080), (Sum.inr 2266, -1080), (Sum.inr 2278, -1080), (Sum.inr 2288, -1080), (Sum.inr 2590, -2160), (Sum.inr 2765, -1080), (Sum.inr 3564, -2160), (Sum.inr 3582, -1080), (Sum.inr 3614, -1080), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3804, -2160), (Sum.inr 3809, -2160), (Sum.inr 3813, -2160), (Sum.inr 3815, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3892, -2160), (Sum.inr 3894, -1080), (Sum.inr 3907, -1080), (Sum.inr 3910, -2160), (Sum.inr 3913, -1080), (Sum.inr 4010, -2160)]

theorem reindexCheck865 : Integer.Sparse.reindex keyMap MixedData.row865 = numericRow865 := by decide +kernel

theorem numericCheck865 (x : Master → ℝ) : Integer.Sparse.eval numericRow865 x =
    (4320 : ℝ) * reducedSource865 x := by
  norm_num [numericRow865, reducedSource865, Integer.Sparse.eval, Sparse.eval, nodeValue4866, nodeValue4868, nodeValue4875, nodeValue4896, nodeValue5163, nodeValue5176, nodeValue5291, nodeValue5388, nodeValue5390, nodeValue5401, nodeValue5404, nodeValue5411, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5453, nodeValue5485, nodeValue5492, nodeValue5493]
  ring

noncomputable def reducedSource866 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3787 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3915 x + ((2 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

def numericRow866 : Integer.Sparse Master := [(Sum.inl 0, -72), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 65), (Sum.inr 2107, 1440), (Sum.inr 2109, 720), (Sum.inr 2116, 720), (Sum.inr 2278, 720), (Sum.inr 2590, 1440), (Sum.inr 2765, 720), (Sum.inr 3787, 1440), (Sum.inr 3790, 1440), (Sum.inr 3813, 1440), (Sum.inr 3876, 1440), (Sum.inr 3907, 720)]

theorem reindexCheck866 : Integer.Sparse.reindex keyMap MixedData.row866 = numericRow866 := by decide +kernel

theorem numericCheck866 (x : Master → ℝ) : Integer.Sparse.eval numericRow866 x =
    (720 : ℝ) * reducedSource866 x := by
  norm_num [numericRow866, reducedSource866, Integer.Sparse.eval, Sparse.eval, nodeValue2107, nodeValue2109, nodeValue2116, nodeValue2278, nodeValue2590, nodeValue2604, nodeValue2765, nodeValue3737, nodeValue3741, nodeValue3787, nodeValue3790, nodeValue3813, nodeValue3876, nodeValue3887, nodeValue3888, nodeValue3907, nodeValue3915, nodeValue3998, nodeValue4001, nodeValue4017, nodeValue4018]
  ring

noncomputable def reducedSource867 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))

def numericRow867 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, 30), (Sum.inl 12, -80), (Sum.inl 4, 80), (Sum.inl 1, 15), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3054, -2160), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3626, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3886, -4320), (Sum.inr 3903, -4320), (Sum.inr 3907, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3963, -4320), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640), (Sum.inr 5430, 17280), (Sum.inr 5446, 17280)]

theorem reindexCheck867 : Integer.Sparse.reindex keyMap MixedData.row867 = numericRow867 := by decide +kernel

theorem numericCheck867 (x : Master → ℝ) : Integer.Sparse.eval numericRow867 x =
    (8640 : ℝ) * reducedSource867 x := by
  norm_num [numericRow867, reducedSource867, Integer.Sparse.eval, Sparse.eval, nodeValue5289, nodeValue5291, nodeValue5295, nodeValue5299, nodeValue5300, nodeValue5302, nodeValue5304, nodeValue5411, nodeValue5413, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5438, nodeValue5441, nodeValue5442, nodeValue5443, nodeValue5446, nodeValue5449, nodeValue5473, nodeValue5475, nodeValue5487]
  ring

noncomputable def reducedSource868 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

def numericRow868 : Integer.Sparse Master := [(Sum.inl 0, -113), (Sum.inl 2, 20), (Sum.inl 3, -480), (Sum.inl 12, -160), (Sum.inl 26, -80), (Sum.inl 4, -240), (Sum.inl 1, -75), (Sum.inl 31, 240), (Sum.inr 2390, 4320), (Sum.inr 2391, 4320), (Sum.inr 2395, 4320), (Sum.inr 2401, 4320), (Sum.inr 2537, 4320), (Sum.inr 2538, 4320), (Sum.inr 2591, 4320), (Sum.inr 2673, 4320), (Sum.inr 2731, 4320), (Sum.inr 3346, 4320), (Sum.inr 3349, 4320), (Sum.inr 3355, 4320), (Sum.inr 3540, 4320), (Sum.inr 3568, 4320), (Sum.inr 3578, 4320), (Sum.inr 3580, 4320), (Sum.inr 3848, 4320), (Sum.inr 3857, 4320), (Sum.inr 3873, 4320), (Sum.inr 3874, 4320), (Sum.inr 3879, 4320), (Sum.inr 3880, 4320), (Sum.inr 3884, 4320), (Sum.inr 3885, 4320), (Sum.inr 3929, 4320), (Sum.inr 3947, 4320)]

theorem reindexCheck868 : Integer.Sparse.reindex keyMap MixedData.row868 = numericRow868 := by decide +kernel

theorem numericCheck868 (x : Master → ℝ) : Integer.Sparse.eval numericRow868 x =
    (4320 : ℝ) * reducedSource868 x := by
  norm_num [numericRow868, reducedSource868, Integer.Sparse.eval, Sparse.eval, nodeValue2390, nodeValue2391, nodeValue2395, nodeValue2401, nodeValue2537, nodeValue2538, nodeValue2591, nodeValue2673, nodeValue2731, nodeValue3346, nodeValue3349, nodeValue3355, nodeValue3540, nodeValue3568, nodeValue3578, nodeValue3580, nodeValue3848, nodeValue3857, nodeValue3858, nodeValue3873, nodeValue3874, nodeValue3879, nodeValue3880, nodeValue3884, nodeValue3885, nodeValue3887, nodeValue3929, nodeValue3947, nodeValue3995, nodeValue3997]
  ring

noncomputable def reducedSource869 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((1 : ℝ) * Sparse.eval nodeValue3947 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow869 : Integer.Sparse Master := [(Sum.inr 2955, 1), (Sum.inr 3881, 1), (Sum.inr 3929, 1), (Sum.inr 3947, 1), (Sum.inr 3958, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem reindexCheck869 : Integer.Sparse.reindex keyMap MixedData.row869 = numericRow869 := by decide +kernel

theorem numericCheck869 (x : Master → ℝ) : Integer.Sparse.eval numericRow869 x =
    (1 : ℝ) * reducedSource869 x := by
  norm_num [numericRow869, reducedSource869, Integer.Sparse.eval, Sparse.eval, nodeValue2955, nodeValue3881, nodeValue3929, nodeValue3947, nodeValue3958, nodeValue3983, nodeValue4091]

noncomputable def reducedSource870 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow870 : Integer.Sparse Master := [(Sum.inr 2633, 1), (Sum.inr 3092, 1), (Sum.inr 3827, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem reindexCheck870 : Integer.Sparse.reindex keyMap MixedData.row870 = numericRow870 := by decide +kernel

theorem numericCheck870 (x : Master → ℝ) : Integer.Sparse.eval numericRow870 x =
    (1 : ℝ) * reducedSource870 x := by
  norm_num [numericRow870, reducedSource870, Integer.Sparse.eval, Sparse.eval, nodeValue2633, nodeValue3092, nodeValue3827, nodeValue3876, nodeValue3881, nodeValue3885, nodeValue4091]

noncomputable def reducedSource871 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4849 x + ((1 : ℝ) * Sparse.eval nodeValue4850 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4861 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue5183 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5399 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))

def numericRow871 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3693, -720), (Sum.inr 3706, -720), (Sum.inr 3732, -720), (Sum.inr 3770, -720), (Sum.inr 3771, -720), (Sum.inr 3809, -1440), (Sum.inr 3811, -720), (Sum.inr 3813, -1440), (Sum.inr 3845, -1440), (Sum.inr 3857, -720), (Sum.inr 3876, -720), (Sum.inr 3958, -720), (Sum.inr 3961, -720), (Sum.inr 4047, -720), (Sum.inr 4849, 2880), (Sum.inr 4850, 2880), (Sum.inr 4856, 2880), (Sum.inr 4861, 2880), (Sum.inr 4867, 2880), (Sum.inr 5183, 2880), (Sum.inr 5188, 2880), (Sum.inr 5198, 2880), (Sum.inr 5264, 2880), (Sum.inr 5353, 2880), (Sum.inr 5379, 2880), (Sum.inr 5382, 2880), (Sum.inr 5385, 5760), (Sum.inr 5399, 2880), (Sum.inr 5402, 2880), (Sum.inr 5421, 2880), (Sum.inr 5436, 2880), (Sum.inr 5445, 2880), (Sum.inr 5446, 2880)]

theorem reindexCheck871 : Integer.Sparse.reindex keyMap MixedData.row871 = numericRow871 := by decide +kernel

theorem numericCheck871 (x : Master → ℝ) : Integer.Sparse.eval numericRow871 x =
    (2880 : ℝ) * reducedSource871 x := by
  norm_num [numericRow871, reducedSource871, Integer.Sparse.eval, Sparse.eval, nodeValue4849, nodeValue4850, nodeValue4856, nodeValue4861, nodeValue4867, nodeValue5183, nodeValue5188, nodeValue5198, nodeValue5264, nodeValue5353, nodeValue5355, nodeValue5370, nodeValue5379, nodeValue5382, nodeValue5384, nodeValue5385, nodeValue5399, nodeValue5402, nodeValue5411, nodeValue5421, nodeValue5428, nodeValue5436, nodeValue5438, nodeValue5445, nodeValue5446, nodeValue5471, nodeValue5473, nodeValue5483]
  ring

noncomputable def reducedSource872 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2613 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3728 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

def numericRow872 : Integer.Sparse Master := [(Sum.inl 0, -2472), (Sum.inl 5, -240), (Sum.inl 2, -1560), (Sum.inl 51, 2880), (Sum.inl 3, -7680), (Sum.inl 13, -960), (Sum.inl 23, 2880), (Sum.inl 24, 2880), (Sum.inl 55, 5760), (Sum.inl 12, -3840), (Sum.inl 4, -2880), (Sum.inl 27, -1440), (Sum.inl 1, 4800), (Sum.inl 31, 2880), (Sum.inr 2086, 51840), (Sum.inr 2087, 51840), (Sum.inr 2094, 51840), (Sum.inr 2102, 51840), (Sum.inr 2251, 51840), (Sum.inr 2613, 51840), (Sum.inr 2620, 51840), (Sum.inr 2632, 51840), (Sum.inr 2729, 51840), (Sum.inr 3724, 51840), (Sum.inr 3733, 51840), (Sum.inr 3783, 51840), (Sum.inr 3785, 51840), (Sum.inr 3802, 51840), (Sum.inr 3811, 51840), (Sum.inr 3813, 51840), (Sum.inr 3827, 51840), (Sum.inr 3854, 51840), (Sum.inr 3866, 51840), (Sum.inr 3868, 51840), (Sum.inr 3876, 51840), (Sum.inr 3880, 51840), (Sum.inr 3884, 51840)]

theorem reindexCheck872 : Integer.Sparse.reindex keyMap MixedData.row872 = numericRow872 := by decide +kernel

theorem numericCheck872 (x : Master → ℝ) : Integer.Sparse.eval numericRow872 x =
    (51840 : ℝ) * reducedSource872 x := by
  norm_num [numericRow872, reducedSource872, Integer.Sparse.eval, Sparse.eval, nodeValue2086, nodeValue2087, nodeValue2094, nodeValue2102, nodeValue2251, nodeValue2613, nodeValue2620, nodeValue2632, nodeValue2729, nodeValue3724, nodeValue3728, nodeValue3733, nodeValue3783, nodeValue3785, nodeValue3802, nodeValue3811, nodeValue3813, nodeValue3827, nodeValue3831, nodeValue3854, nodeValue3866, nodeValue3868, nodeValue3876, nodeValue3880, nodeValue3883, nodeValue3884, nodeValue3976, nodeValue3981, nodeValue3995, nodeValue4003]
  ring

noncomputable def reducedSource873 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3501 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3785 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

def numericRow873 : Integer.Sparse Master := [(Sum.inl 0, -393), (Sum.inl 5, -60), (Sum.inl 2, -165), (Sum.inl 3, -1680), (Sum.inl 13, -240), (Sum.inl 23, 720), (Sum.inl 54, 720), (Sum.inl 12, -960), (Sum.inl 25, 720), (Sum.inl 26, -240), (Sum.inl 4, -720), (Sum.inl 27, 180), (Sum.inl 1, 480), (Sum.inr 2098, 12960), (Sum.inr 2099, 12960), (Sum.inr 2102, 12960), (Sum.inr 2108, 12960), (Sum.inr 2274, 12960), (Sum.inr 3501, 12960), (Sum.inr 3506, 12960), (Sum.inr 3538, 12960), (Sum.inr 3570, 12960), (Sum.inr 3730, 12960), (Sum.inr 3733, 12960), (Sum.inr 3761, 12960), (Sum.inr 3770, 12960), (Sum.inr 3771, 12960), (Sum.inr 3785, 12960), (Sum.inr 3788, 12960), (Sum.inr 3813, 12960), (Sum.inr 3832, 12960), (Sum.inr 3845, 12960), (Sum.inr 3868, 12960), (Sum.inr 3873, 12960), (Sum.inr 3877, 12960), (Sum.inr 3880, 12960), (Sum.inr 3881, 12960), (Sum.inr 3958, 12960)]

theorem reindexCheck873 : Integer.Sparse.reindex keyMap MixedData.row873 = numericRow873 := by decide +kernel

theorem numericCheck873 (x : Master → ℝ) : Integer.Sparse.eval numericRow873 x =
    (12960 : ℝ) * reducedSource873 x := by
  norm_num [numericRow873, reducedSource873, Integer.Sparse.eval, Sparse.eval, nodeValue2098, nodeValue2099, nodeValue2102, nodeValue2108, nodeValue2274, nodeValue3501, nodeValue3506, nodeValue3538, nodeValue3570, nodeValue3730, nodeValue3733, nodeValue3738, nodeValue3761, nodeValue3770, nodeValue3771, nodeValue3785, nodeValue3788, nodeValue3813, nodeValue3832, nodeValue3845, nodeValue3868, nodeValue3873, nodeValue3877, nodeValue3880, nodeValue3881, nodeValue3883, nodeValue3953, nodeValue3958, nodeValue3981, nodeValue3993]
  ring

noncomputable def reducedSource874 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow874 : Integer.Sparse Master := [(Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 3720, 1), (Sum.inr 3733, 1), (Sum.inr 3845, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem reindexCheck874 : Integer.Sparse.reindex keyMap MixedData.row874 = numericRow874 := by decide +kernel

theorem numericCheck874 (x : Master → ℝ) : Integer.Sparse.eval numericRow874 x =
    (1 : ℝ) * reducedSource874 x := by
  norm_num [numericRow874, reducedSource874, Integer.Sparse.eval, Sparse.eval, nodeValue2867, nodeValue3693, nodeValue3720, nodeValue3733, nodeValue3845, nodeValue3959, nodeValue4092]

noncomputable def reducedSource875 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow875 : Integer.Sparse Master := [(Sum.inr 3174, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3809, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem reindexCheck875 : Integer.Sparse.reindex keyMap MixedData.row875 = numericRow875 := by decide +kernel

theorem numericCheck875 (x : Master → ℝ) : Integer.Sparse.eval numericRow875 x =
    (1 : ℝ) * reducedSource875 x := by
  norm_num [numericRow875, reducedSource875, Integer.Sparse.eval, Sparse.eval, nodeValue3174, nodeValue3691, nodeValue3693, nodeValue3706, nodeValue3809, nodeValue3959, nodeValue4092]

noncomputable def reducedSource876 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow876 : Integer.Sparse Master := [(Sum.inr 3040, 1), (Sum.inr 3730, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 3857, 1), (Sum.inr 3959, 1), (Sum.inr 4092, -1)]

theorem reindexCheck876 : Integer.Sparse.reindex keyMap MixedData.row876 = numericRow876 := by decide +kernel

theorem numericCheck876 (x : Master → ℝ) : Integer.Sparse.eval numericRow876 x =
    (1 : ℝ) * reducedSource876 x := by
  norm_num [numericRow876, reducedSource876, Integer.Sparse.eval, Sparse.eval, nodeValue3040, nodeValue3730, nodeValue3732, nodeValue3733, nodeValue3857, nodeValue3959, nodeValue4092]

noncomputable def reducedSource877 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2491 x + ((1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2506 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3939 x + ((1 : ℝ) * Sparse.eval nodeValue3968 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0)))))))))))))))))))))))))))))

def numericRow877 : Integer.Sparse Master := [(Sum.inl 0, -824), (Sum.inl 5, -80), (Sum.inl 2, -420), (Sum.inl 51, 960), (Sum.inl 3, -960), (Sum.inl 13, -320), (Sum.inl 12, -640), (Sum.inl 4, -320), (Sum.inl 1, 1140), (Sum.inr 2491, 17280), (Sum.inr 2492, 17280), (Sum.inr 2499, 17280), (Sum.inr 2506, 17280), (Sum.inr 2607, 17280), (Sum.inr 2608, 17280), (Sum.inr 2633, 17280), (Sum.inr 2678, 17280), (Sum.inr 2774, 17280), (Sum.inr 3566, 17280), (Sum.inr 3570, 17280), (Sum.inr 3572, 17280), (Sum.inr 3575, 17280), (Sum.inr 3696, 17280), (Sum.inr 3699, 17280), (Sum.inr 3846, 17280), (Sum.inr 3850, 17280), (Sum.inr 3854, 17280), (Sum.inr 3870, 17280), (Sum.inr 3871, 17280), (Sum.inr 3878, 17280), (Sum.inr 3881, 17280), (Sum.inr 3886, 17280)]

theorem reindexCheck877 : Integer.Sparse.reindex keyMap MixedData.row877 = numericRow877 := by decide +kernel

theorem numericCheck877 (x : Master → ℝ) : Integer.Sparse.eval numericRow877 x =
    (17280 : ℝ) * reducedSource877 x := by
  norm_num [numericRow877, reducedSource877, Integer.Sparse.eval, Sparse.eval, nodeValue2491, nodeValue2492, nodeValue2499, nodeValue2506, nodeValue2607, nodeValue2608, nodeValue2633, nodeValue2678, nodeValue2774, nodeValue3566, nodeValue3570, nodeValue3572, nodeValue3575, nodeValue3696, nodeValue3699, nodeValue3846, nodeValue3850, nodeValue3852, nodeValue3854, nodeValue3870, nodeValue3871, nodeValue3878, nodeValue3881, nodeValue3883, nodeValue3886, nodeValue3888, nodeValue3939, nodeValue3968, nodeValue3995, nodeValue4004]
  ring

noncomputable def reducedSource878 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3384 x + ((1 : ℝ) * Sparse.eval nodeValue3385 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3447 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3752 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4022 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0)))))))))))))))))))))))))))))

def numericRow878 : Integer.Sparse Master := [(Sum.inl 0, -256), (Sum.inl 2, -170), (Sum.inl 3, -160), (Sum.inl 25, -480), (Sum.inl 26, -160), (Sum.inl 1, 110), (Sum.inr 2874, 8640), (Sum.inr 2875, 8640), (Sum.inr 2876, 8640), (Sum.inr 2885, 8640), (Sum.inr 3097, 8640), (Sum.inr 3384, 8640), (Sum.inr 3385, 8640), (Sum.inr 3386, 8640), (Sum.inr 3395, 8640), (Sum.inr 3447, 8640), (Sum.inr 3480, 8640), (Sum.inr 3578, 8640), (Sum.inr 3584, 8640), (Sum.inr 3752, 8640), (Sum.inr 3759, 8640), (Sum.inr 3767, 8640), (Sum.inr 3772, 8640), (Sum.inr 3809, 8640), (Sum.inr 3877, 8640), (Sum.inr 3954, 8640), (Sum.inr 3958, 8640), (Sum.inr 3959, 8640), (Sum.inr 3963, 8640), (Sum.inr 3972, 8640), (Sum.inr 4022, 8640)]

theorem reindexCheck878 : Integer.Sparse.reindex keyMap MixedData.row878 = numericRow878 := by decide +kernel

theorem numericCheck878 (x : Master → ℝ) : Integer.Sparse.eval numericRow878 x =
    (8640 : ℝ) * reducedSource878 x := by
  norm_num [numericRow878, reducedSource878, Integer.Sparse.eval, Sparse.eval, nodeValue2874, nodeValue2875, nodeValue2876, nodeValue2885, nodeValue3097, nodeValue3384, nodeValue3385, nodeValue3386, nodeValue3395, nodeValue3447, nodeValue3480, nodeValue3578, nodeValue3584, nodeValue3752, nodeValue3759, nodeValue3767, nodeValue3772, nodeValue3809, nodeValue3877, nodeValue3950, nodeValue3954, nodeValue3958, nodeValue3959, nodeValue3963, nodeValue3972, nodeValue3982, nodeValue3987, nodeValue4022, nodeValue4027, nodeValue4030]
  ring

noncomputable def reducedSource879 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3944 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow879 : Integer.Sparse Master := [(Sum.inr 2882, 1), (Sum.inr 3705, 1), (Sum.inr 3884, 1), (Sum.inr 3961, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem reindexCheck879 : Integer.Sparse.reindex keyMap MixedData.row879 = numericRow879 := by decide +kernel

theorem numericCheck879 (x : Master → ℝ) : Integer.Sparse.eval numericRow879 x =
    (1 : ℝ) * reducedSource879 x := by
  norm_num [numericRow879, reducedSource879, Integer.Sparse.eval, Sparse.eval, nodeValue2882, nodeValue3705, nodeValue3884, nodeValue3944, nodeValue3961, nodeValue3963, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
