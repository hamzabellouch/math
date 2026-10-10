import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
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

noncomputable def reducedSource928 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))))))))))

def numericRow928 : Integer.Sparse Master := [(Sum.inl 0, 30), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 4, -16), (Sum.inl 1, -29), (Sum.inr 2881, -864), (Sum.inr 3624, -864), (Sum.inr 3703, -864), (Sum.inr 3705, -864), (Sum.inr 3706, -864), (Sum.inr 3758, -864), (Sum.inr 3767, -864), (Sum.inr 3771, -864), (Sum.inr 3781, -864), (Sum.inr 3794, -864), (Sum.inr 3845, -1728), (Sum.inr 3850, -1728), (Sum.inr 3857, -864), (Sum.inr 3876, -864), (Sum.inr 3903, -864), (Sum.inr 3913, -864), (Sum.inr 3958, -864), (Sum.inr 3961, -864), (Sum.inr 3963, -1728), (Sum.inr 4047, -864), (Sum.inr 5197, 3456), (Sum.inr 5198, 3456), (Sum.inr 5199, 3456), (Sum.inr 5299, 3456), (Sum.inr 5421, 3456), (Sum.inr 5429, 3456), (Sum.inr 5430, 3456), (Sum.inr 5436, 3456), (Sum.inr 5446, 6912)]

theorem reindexCheck928 : Integer.Sparse.reindex keyMap MixedData.row928 = numericRow928 := by decide +kernel

theorem numericCheck928 (x : Master → ℝ) : Integer.Sparse.eval numericRow928 x =
    (3456 : ℝ) * reducedSource928 x := by
  norm_num [numericRow928, reducedSource928, Integer.Sparse.eval, Sparse.eval, nodeValue5197, nodeValue5198, nodeValue5199, nodeValue5204, nodeValue5299, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5370, nodeValue5395, nodeValue5410, nodeValue5413, nodeValue5421, nodeValue5428, nodeValue5429, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5436, nodeValue5438, nodeValue5446, nodeValue5451, nodeValue5468, nodeValue5471, nodeValue5473, nodeValue5475, nodeValue5477, nodeValue5483, nodeValue5487]
  ring

noncomputable def reducedSource929 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3972 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + 0)))))))))))))))))))))))))))))

def numericRow929 : Integer.Sparse Master := [(Sum.inl 0, -194), (Sum.inl 2, -100), (Sum.inl 3, -320), (Sum.inl 12, -80), (Sum.inl 25, 240), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, 270), (Sum.inr 3569, 4320), (Sum.inr 3570, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3624, 4320), (Sum.inr 3758, 4320), (Sum.inr 3767, 4320), (Sum.inr 3771, 4320), (Sum.inr 3794, 4320), (Sum.inr 3845, 4320), (Sum.inr 3873, 4320), (Sum.inr 3877, 4320), (Sum.inr 3884, 4320), (Sum.inr 3954, 4320), (Sum.inr 3958, 4320), (Sum.inr 3959, 4320), (Sum.inr 3963, 4320), (Sum.inr 3972, 4320)]

theorem reindexCheck929 : Integer.Sparse.reindex keyMap MixedData.row929 = numericRow929 := by decide +kernel

theorem numericCheck929 (x : Master → ℝ) : Integer.Sparse.eval numericRow929 x =
    (4320 : ℝ) * reducedSource929 x := by
  norm_num [numericRow929, reducedSource929, Integer.Sparse.eval, Sparse.eval, nodeValue3569, nodeValue3570, nodeValue3573, nodeValue3578, nodeValue3624, nodeValue3758, nodeValue3766, nodeValue3767, nodeValue3771, nodeValue3794, nodeValue3808, nodeValue3817, nodeValue3845, nodeValue3873, nodeValue3877, nodeValue3884, nodeValue3950, nodeValue3953, nodeValue3954, nodeValue3958, nodeValue3959, nodeValue3963, nodeValue3971, nodeValue3972, nodeValue3981, nodeValue3982, nodeValue3986, nodeValue3987, nodeValue3993, nodeValue4027]
  ring

noncomputable def reducedSource930 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))))))))))

def numericRow930 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2480, -2160), (Sum.inr 2485, -2160), (Sum.inr 2489, -2160), (Sum.inr 2723, -2160), (Sum.inr 2924, -2160), (Sum.inr 2931, -2160), (Sum.inr 2954, -2160), (Sum.inr 3077, -2160), (Sum.inr 3467, -2160), (Sum.inr 3481, -2160), (Sum.inr 3482, -2160), (Sum.inr 3544, -2160), (Sum.inr 3605, -2160), (Sum.inr 3606, -2160), (Sum.inr 3612, -2160), (Sum.inr 3625, -2160), (Sum.inr 3690, -2160), (Sum.inr 3694, -2160), (Sum.inr 3764, -2160), (Sum.inr 3773, -2160), (Sum.inr 3779, -2160), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3797, -2160), (Sum.inr 3800, -2160), (Sum.inr 3804, -2160), (Sum.inr 3805, -2160), (Sum.inr 3815, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3902, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 3974, -4320), (Sum.inr 3983, -4320), (Sum.inr 4010, -2160), (Sum.inr 4091, 8640)]

theorem reindexCheck930 : Integer.Sparse.reindex keyMap MixedData.row930 = numericRow930 := by decide +kernel

theorem numericCheck930 (x : Master → ℝ) : Integer.Sparse.eval numericRow930 x =
    (8640 : ℝ) * reducedSource930 x := by
  norm_num [numericRow930, reducedSource930, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue5073, nodeValue5078, nodeValue5081, nodeValue5104, nodeValue5149, nodeValue5152, nodeValue5170, nodeValue5259, nodeValue5284, nodeValue5352, nodeValue5356, nodeValue5369, nodeValue5393, nodeValue5396, nodeValue5401, nodeValue5404, nodeValue5405, nodeValue5408, nodeValue5410, nodeValue5424, nodeValue5438, nodeValue5439, nodeValue5440, nodeValue5473, nodeValue5478, nodeValue5484, nodeValue5485, nodeValue5486]
  ring

noncomputable def reducedSource931 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))))))))))

def numericRow931 : Integer.Sparse Master := [(Sum.inl 0, 99), (Sum.inl 2, 50), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -145), (Sum.inr 2508, -2160), (Sum.inr 2512, -2160), (Sum.inr 2515, -2160), (Sum.inr 2739, -2160), (Sum.inr 3460, -2160), (Sum.inr 3471, -2160), (Sum.inr 3479, -2160), (Sum.inr 3534, -2160), (Sum.inr 3703, -2160), (Sum.inr 3705, -2160), (Sum.inr 3706, -2160), (Sum.inr 3758, -2160), (Sum.inr 3767, -2160), (Sum.inr 3771, -2160), (Sum.inr 3781, -2160), (Sum.inr 3782, -2160), (Sum.inr 3794, -2160), (Sum.inr 3796, -2160), (Sum.inr 3800, -2160), (Sum.inr 3801, -2160), (Sum.inr 3805, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320), (Sum.inr 3814, -4320), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3903, -4320), (Sum.inr 3906, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4047, -2160), (Sum.inr 4092, 8640)]

theorem reindexCheck931 : Integer.Sparse.reindex keyMap MixedData.row931 = numericRow931 := by decide +kernel

theorem numericCheck931 (x : Master → ℝ) : Integer.Sparse.eval numericRow931 x =
    (8640 : ℝ) * reducedSource931 x := by
  norm_num [numericRow931, reducedSource931, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue5098, nodeValue5101, nodeValue5102, nodeValue5105, nodeValue5271, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5370, nodeValue5394, nodeValue5395, nodeValue5397, nodeValue5405, nodeValue5406, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5413, nodeValue5424, nodeValue5434, nodeValue5435, nodeValue5442, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5487]
  ring

noncomputable def reducedSource932 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))))

def numericRow932 : Integer.Sparse Master := [(Sum.inl 0, 24), (Sum.inl 2, 10), (Sum.inl 3, -40), (Sum.inl 12, -40), (Sum.inl 1, 10), (Sum.inr 2561, -1080), (Sum.inr 2743, -1080), (Sum.inr 2881, -1080), (Sum.inr 3522, -1080), (Sum.inr 3548, -1080), (Sum.inr 3624, -1080), (Sum.inr 3689, -1080), (Sum.inr 3693, -1080), (Sum.inr 3757, -1080), (Sum.inr 3770, -1080), (Sum.inr 3781, -1080), (Sum.inr 3794, -1080), (Sum.inr 3838, -1080), (Sum.inr 3843, -1080), (Sum.inr 3845, -2160), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3907, -1080), (Sum.inr 3958, -1080), (Sum.inr 3961, -1080), (Sum.inr 4047, -1080), (Sum.inr 5139, 4320), (Sum.inr 5164, 4320), (Sum.inr 5187, 4320), (Sum.inr 5188, 4320), (Sum.inr 5267, 4320), (Sum.inr 5379, 4320), (Sum.inr 5385, 4320), (Sum.inr 5414, 4320), (Sum.inr 5425, 4320), (Sum.inr 5436, 4320), (Sum.inr 5446, 4320)]

theorem reindexCheck932 : Integer.Sparse.reindex keyMap MixedData.row932 = numericRow932 := by decide +kernel

theorem numericCheck932 (x : Master → ℝ) : Integer.Sparse.eval numericRow932 x =
    (4320 : ℝ) * reducedSource932 x := by
  norm_num [numericRow932, reducedSource932, Integer.Sparse.eval, Sparse.eval, nodeValue5135, nodeValue5139, nodeValue5141, nodeValue5164, nodeValue5187, nodeValue5188, nodeValue5204, nodeValue5267, nodeValue5275, nodeValue5351, nodeValue5355, nodeValue5367, nodeValue5379, nodeValue5385, nodeValue5395, nodeValue5409, nodeValue5413, nodeValue5414, nodeValue5424, nodeValue5425, nodeValue5428, nodeValue5436, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5446, nodeValue5471, nodeValue5473, nodeValue5483]
  ring

noncomputable def reducedSource933 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

def numericRow933 : Integer.Sparse Master := [(Sum.inl 0, -232), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, 70), (Sum.inr 3522, 8640), (Sum.inr 3523, 8640), (Sum.inr 3537, 8640), (Sum.inr 3538, 8640), (Sum.inr 3541, 8640), (Sum.inr 3548, 8640), (Sum.inr 3565, 8640), (Sum.inr 3624, 8640), (Sum.inr 3757, 8640), (Sum.inr 3770, 8640), (Sum.inr 3794, 8640), (Sum.inr 3832, 8640), (Sum.inr 3838, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3884, 8640), (Sum.inr 3958, 8640)]

theorem reindexCheck933 : Integer.Sparse.reindex keyMap MixedData.row933 = numericRow933 := by decide +kernel

theorem numericCheck933 (x : Master → ℝ) : Integer.Sparse.eval numericRow933 x =
    (8640 : ℝ) * reducedSource933 x := by
  norm_num [numericRow933, reducedSource933, Integer.Sparse.eval, Sparse.eval, nodeValue3515, nodeValue3522, nodeValue3523, nodeValue3537, nodeValue3538, nodeValue3541, nodeValue3548, nodeValue3565, nodeValue3624, nodeValue3757, nodeValue3766, nodeValue3770, nodeValue3794, nodeValue3807, nodeValue3817, nodeValue3832, nodeValue3838, nodeValue3839, nodeValue3845, nodeValue3861, nodeValue3862, nodeValue3868, nodeValue3869, nodeValue3876, nodeValue3877, nodeValue3884, nodeValue3953, nodeValue3958, nodeValue3981, nodeValue3993]
  ring

noncomputable def reducedSource934 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4996 x + ((2 : ℝ) * Sparse.eval nodeValue5003 x + ((2 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0)))))))))))))))

def numericRow934 : Integer.Sparse Master := [(Sum.inl 0, 215), (Sum.inl 2, 20), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 240), (Sum.inl 1, 5), (Sum.inr 2000, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2054, -4320), (Sum.inr 2206, -4320), (Sum.inr 2382, -4320), (Sum.inr 2388, -4320), (Sum.inr 2400, -4320), (Sum.inr 2722, -4320), (Sum.inr 3340, -4320), (Sum.inr 3344, -4320), (Sum.inr 3354, -4320), (Sum.inr 3533, -4320), (Sum.inr 3683, -4320), (Sum.inr 3705, -4320), (Sum.inr 3746, -4320), (Sum.inr 3767, -4320), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 3957, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320)]

theorem reindexCheck934 : Integer.Sparse.reindex keyMap MixedData.row934 = numericRow934 := by decide +kernel

theorem numericCheck934 (x : Master → ℝ) : Integer.Sparse.eval numericRow934 x =
    (8640 : ℝ) * reducedSource934 x := by
  norm_num [numericRow934, reducedSource934, Integer.Sparse.eval, Sparse.eval, nodeValue4787, nodeValue4788, nodeValue4835, nodeValue4996, nodeValue5003, nodeValue5015, nodeValue5258, nodeValue5346, nodeValue5368, nodeValue5395, nodeValue5424, nodeValue5434, nodeValue5439, nodeValue5472, nodeValue5473, nodeValue5490]
  ring

noncomputable def reducedSource935 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((4 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5413 x + ((4 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5468 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))

def numericRow935 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2889, -2160), (Sum.inr 3631, -2160), (Sum.inr 3705, -4320), (Sum.inr 3767, -4320), (Sum.inr 3886, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5199, 17280), (Sum.inr 5201, 4320), (Sum.inr 5300, 8640), (Sum.inr 5446, 17280)]

theorem reindexCheck935 : Integer.Sparse.reindex keyMap MixedData.row935 = numericRow935 := by decide +kernel

theorem numericCheck935 (x : Master → ℝ) : Integer.Sparse.eval numericRow935 x =
    (4320 : ℝ) * reducedSource935 x := by
  norm_num [numericRow935, reducedSource935, Integer.Sparse.eval, Sparse.eval, nodeValue5199, nodeValue5201, nodeValue5207, nodeValue5300, nodeValue5368, nodeValue5371, nodeValue5413, nodeValue5446, nodeValue5449, nodeValue5451, nodeValue5468, nodeValue5473, nodeValue5487]
  ring

noncomputable def reducedSource936 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3631 x + ((4 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((2 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3950 x + ((4 : ℝ) * Sparse.eval nodeValue3958 x + ((4 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3986 x + ((2 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0))))))))))))

def numericRow936 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, -10), (Sum.inl 3, 80), (Sum.inl 25, -120), (Sum.inl 4, 80), (Sum.inl 1, 5), (Sum.inr 3578, 4320), (Sum.inr 3579, 1080), (Sum.inr 3584, 2160), (Sum.inr 3631, 2160), (Sum.inr 3767, 4320), (Sum.inr 3958, 4320), (Sum.inr 3959, 4320)]

theorem reindexCheck936 : Integer.Sparse.reindex keyMap MixedData.row936 = numericRow936 := by decide +kernel

theorem numericCheck936 (x : Master → ℝ) : Integer.Sparse.eval numericRow936 x =
    (1080 : ℝ) * reducedSource936 x := by
  norm_num [numericRow936, reducedSource936, Integer.Sparse.eval, Sparse.eval, nodeValue3578, nodeValue3579, nodeValue3584, nodeValue3631, nodeValue3767, nodeValue3775, nodeValue3817, nodeValue3950, nodeValue3958, nodeValue3959, nodeValue3986, nodeValue3987, nodeValue4030]
  ring

noncomputable def reducedSource937 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5018 x + ((2 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5023 x + ((4 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5467 x + ((8 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))

def numericRow937 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 4, -80), (Sum.inl 1, 105), (Sum.inr 2404, -4320), (Sum.inr 2407, -1080), (Sum.inr 2410, -2160), (Sum.inr 2743, -2160), (Sum.inr 3357, -4320), (Sum.inr 3360, -1080), (Sum.inr 3548, -2160), (Sum.inr 3942, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320)]

theorem reindexCheck937 : Integer.Sparse.reindex keyMap MixedData.row937 = numericRow937 := by decide +kernel

theorem numericCheck937 (x : Master → ℝ) : Integer.Sparse.eval numericRow937 x =
    (2160 : ℝ) * reducedSource937 x := by
  norm_num [numericRow937, reducedSource937, Integer.Sparse.eval, Sparse.eval, nodeValue5018, nodeValue5021, nodeValue5023, nodeValue5275, nodeValue5467, nodeValue5473, nodeValue5491, nodeValue5492]
  ring

noncomputable def reducedSource938 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5206 x + ((4 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5420 x + ((4 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((4 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))

def numericRow938 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2765, -2160), (Sum.inr 3582, -2160), (Sum.inr 3850, -8640), (Sum.inr 3913, -2160), (Sum.inr 3963, -2160), (Sum.inr 5198, 17280), (Sum.inr 5201, 4320), (Sum.inr 5206, 8640), (Sum.inr 5233, 17280), (Sum.inr 5235, 4320), (Sum.inr 5300, 8640), (Sum.inr 5420, 8640), (Sum.inr 5446, 17280)]

theorem reindexCheck938 : Integer.Sparse.reindex keyMap MixedData.row938 = numericRow938 := by decide +kernel

theorem numericCheck938 (x : Master → ℝ) : Integer.Sparse.eval numericRow938 x =
    (4320 : ℝ) * reducedSource938 x := by
  norm_num [numericRow938, reducedSource938, Integer.Sparse.eval, Sparse.eval, nodeValue5198, nodeValue5201, nodeValue5206, nodeValue5233, nodeValue5235, nodeValue5291, nodeValue5300, nodeValue5420, nodeValue5432, nodeValue5441, nodeValue5446, nodeValue5451, nodeValue5475]
  ring

noncomputable def reducedSource939 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((2 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2774 x + ((4 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((4 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((2 : ℝ) * Sparse.eval nodeValue3870 x + ((4 : ℝ) * Sparse.eval nodeValue3881 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0))))))))))))

def numericRow939 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 4, 320), (Sum.inl 1, 130), (Sum.inl 31, -480), (Sum.inr 2678, 17280), (Sum.inr 2680, 4320), (Sum.inr 2687, 8640), (Sum.inr 2774, 8640), (Sum.inr 3570, 17280), (Sum.inr 3579, 4320), (Sum.inr 3582, 8640), (Sum.inr 3850, 17280), (Sum.inr 3870, 8640), (Sum.inr 3881, 17280)]

theorem reindexCheck939 : Integer.Sparse.reindex keyMap MixedData.row939 = numericRow939 := by decide +kernel

theorem numericCheck939 (x : Master → ℝ) : Integer.Sparse.eval numericRow939 x =
    (4320 : ℝ) * reducedSource939 x := by
  norm_num [numericRow939, reducedSource939, Integer.Sparse.eval, Sparse.eval, nodeValue2678, nodeValue2680, nodeValue2687, nodeValue2774, nodeValue3570, nodeValue3579, nodeValue3582, nodeValue3850, nodeValue3860, nodeValue3870, nodeValue3881, nodeValue3888, nodeValue4004]
  ring

noncomputable def reducedSource940 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4860 x + ((1 : ℝ) * Sparse.eval nodeValue4862 x + ((4 : ℝ) * Sparse.eval nodeValue4874 x + ((8 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((2 : ℝ) * Sparse.eval nodeValue5398 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))

def numericRow940 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 2, 30), (Sum.inl 3, -480), (Sum.inl 23, 720), (Sum.inl 12, -480), (Sum.inl 27, 180), (Sum.inl 1, 1020), (Sum.inr 2101, -25920), (Sum.inr 2103, -6480), (Sum.inr 2115, -12960), (Sum.inr 2276, -12960), (Sum.inr 3732, -25920), (Sum.inr 3784, -12960), (Sum.inr 3811, -25920), (Sum.inr 3885, -25920), (Sum.inr 3893, -6480), (Sum.inr 3907, -12960)]

theorem reindexCheck940 : Integer.Sparse.reindex keyMap MixedData.row940 = numericRow940 := by decide +kernel

theorem numericCheck940 (x : Master → ℝ) : Integer.Sparse.eval numericRow940 x =
    (12960 : ℝ) * reducedSource940 x := by
  norm_num [numericRow940, reducedSource940, Integer.Sparse.eval, Sparse.eval, nodeValue4860, nodeValue4862, nodeValue4874, nodeValue5384, nodeValue5389, nodeValue5398, nodeValue5443, nodeValue5448, nodeValue5491]
  ring

noncomputable def reducedSource941 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5420 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow941 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -85), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 2765, -4320), (Sum.inr 3533, -4320), (Sum.inr 3564, -4320), (Sum.inr 3582, -4320), (Sum.inr 3732, -4320), (Sum.inr 3786, -4320), (Sum.inr 3799, -4320), (Sum.inr 3811, -4320), (Sum.inr 3837, -8640), (Sum.inr 3850, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3886, -8640), (Sum.inr 3903, -4320), (Sum.inr 3913, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5151, 17280), (Sum.inr 5184, 17280), (Sum.inr 5188, 17280), (Sum.inr 5198, 17280), (Sum.inr 5231, 17280), (Sum.inr 5232, 17280), (Sum.inr 5233, 17280), (Sum.inr 5299, 17280), (Sum.inr 5381, 17280), (Sum.inr 5420, 17280), (Sum.inr 5429, 17280), (Sum.inr 5430, 17280), (Sum.inr 5436, 17280), (Sum.inr 5446, 17280)]

theorem reindexCheck941 : Integer.Sparse.reindex keyMap MixedData.row941 = numericRow941 := by decide +kernel

theorem numericCheck941 (x : Master → ℝ) : Integer.Sparse.eval numericRow941 x =
    (17280 : ℝ) * reducedSource941 x := by
  norm_num [numericRow941, reducedSource941, Integer.Sparse.eval, Sparse.eval, nodeValue5144, nodeValue5147, nodeValue5151, nodeValue5163, nodeValue5184, nodeValue5188, nodeValue5198, nodeValue5231, nodeValue5232, nodeValue5233, nodeValue5258, nodeValue5291, nodeValue5299, nodeValue5381, nodeValue5384, nodeValue5400, nodeValue5409, nodeValue5420, nodeValue5423, nodeValue5429, nodeValue5430, nodeValue5432, nodeValue5434, nodeValue5436, nodeValue5438, nodeValue5441, nodeValue5446, nodeValue5449, nodeValue5451, nodeValue5473]
  ring

noncomputable def reducedSource942 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0)))))))))))))))))))))))))))))

def numericRow942 : Integer.Sparse Master := [(Sum.inl 0, -230), (Sum.inl 2, -100), (Sum.inl 1, 210), (Sum.inl 31, 480), (Sum.inr 2676, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2681, 8640), (Sum.inr 2773, 8640), (Sum.inr 3524, 8640), (Sum.inr 3530, 8640), (Sum.inr 3533, 8640), (Sum.inr 3538, 8640), (Sum.inr 3557, 8640), (Sum.inr 3564, 8640), (Sum.inr 3570, 8640), (Sum.inr 3582, 8640), (Sum.inr 3799, 8640), (Sum.inr 3811, 8640), (Sum.inr 3834, 8640), (Sum.inr 3837, 8640), (Sum.inr 3846, 8640), (Sum.inr 3850, 8640), (Sum.inr 3854, 8640), (Sum.inr 3870, 8640), (Sum.inr 3871, 8640), (Sum.inr 3876, 8640), (Sum.inr 3881, 8640), (Sum.inr 3886, 8640)]

theorem reindexCheck942 : Integer.Sparse.reindex keyMap MixedData.row942 = numericRow942 := by decide +kernel

theorem numericCheck942 (x : Master → ℝ) : Integer.Sparse.eval numericRow942 x =
    (8640 : ℝ) * reducedSource942 x := by
  norm_num [numericRow942, reducedSource942, Integer.Sparse.eval, Sparse.eval, nodeValue2676, nodeValue2677, nodeValue2678, nodeValue2681, nodeValue2773, nodeValue3524, nodeValue3530, nodeValue3533, nodeValue3538, nodeValue3557, nodeValue3564, nodeValue3570, nodeValue3582, nodeValue3799, nodeValue3807, nodeValue3811, nodeValue3834, nodeValue3837, nodeValue3846, nodeValue3850, nodeValue3852, nodeValue3854, nodeValue3860, nodeValue3870, nodeValue3871, nodeValue3876, nodeValue3881, nodeValue3886, nodeValue3888, nodeValue3995]
  ring

noncomputable def reducedSource943 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4800 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4828 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))

def numericRow943 : Integer.Sparse Master := [(Sum.inl 0, 501), (Sum.inl 5, 60), (Sum.inl 7, 240), (Sum.inl 3, 1440), (Sum.inl 23, -720), (Sum.inl 12, 960), (Sum.inl 4, 720), (Sum.inl 27, -180), (Sum.inl 1, -645), (Sum.inr 2016, -12960), (Sum.inr 2018, -12960), (Sum.inr 2028, -12960), (Sum.inr 2048, -12960), (Sum.inr 2075, -12960), (Sum.inr 2082, -12960), (Sum.inr 2106, -12960), (Sum.inr 2215, -12960), (Sum.inr 2242, -12960), (Sum.inr 3687, -12960), (Sum.inr 3693, -12960), (Sum.inr 3702, -12960), (Sum.inr 3719, -12960), (Sum.inr 3749, -12960), (Sum.inr 3770, -12960), (Sum.inr 3786, -12960), (Sum.inr 3795, -12960), (Sum.inr 3799, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -12960), (Sum.inr 3857, -12960), (Sum.inr 3875, -12960), (Sum.inr 3876, -12960), (Sum.inr 3891, -12960), (Sum.inr 3906, -12960), (Sum.inr 3910, -12960)]

theorem reindexCheck943 : Integer.Sparse.reindex keyMap MixedData.row943 = numericRow943 := by decide +kernel

theorem numericCheck943 (x : Master → ℝ) : Integer.Sparse.eval numericRow943 x =
    (25920 : ℝ) * reducedSource943 x := by
  norm_num [numericRow943, reducedSource943, Integer.Sparse.eval, Sparse.eval, nodeValue4798, nodeValue4800, nodeValue4810, nodeValue4828, nodeValue4865, nodeValue5349, nodeValue5355, nodeValue5364, nodeValue5378, nodeValue5387, nodeValue5400, nodeValue5431, nodeValue5432, nodeValue5435, nodeValue5438, nodeValue5450, nodeValue5490]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
