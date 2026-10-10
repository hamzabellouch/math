import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
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

noncomputable def reducedSource976 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5094 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))

def numericRow976 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 2, 7), (Sum.inl 3, -16), (Sum.inl 4, 32), (Sum.inl 1, -62), (Sum.inr 2503, -864), (Sum.inr 2504, -864), (Sum.inr 2505, -864), (Sum.inr 2515, -864), (Sum.inr 2782, -864), (Sum.inr 3446, -864), (Sum.inr 3448, -864), (Sum.inr 3479, -864), (Sum.inr 3583, -864), (Sum.inr 3701, -864), (Sum.inr 3702, -864), (Sum.inr 3706, -864), (Sum.inr 3751, -864), (Sum.inr 3771, -864), (Sum.inr 3857, -864), (Sum.inr 3876, -864), (Sum.inr 3900, -864), (Sum.inr 3903, -864), (Sum.inr 3913, -864), (Sum.inr 3964, -864), (Sum.inr 3983, -1728)]

theorem reindexCheck976 : Integer.Sparse.reindex keyMap MixedData.row976 = numericRow976 := by decide +kernel

theorem numericCheck976 (x : Master → ℝ) : Integer.Sparse.eval numericRow976 x =
    (1728 : ℝ) * reducedSource976 x := by
  norm_num [numericRow976, reducedSource976, Integer.Sparse.eval, Sparse.eval, nodeValue5093, nodeValue5094, nodeValue5095, nodeValue5105, nodeValue5304, nodeValue5363, nodeValue5364, nodeValue5370, nodeValue5422, nodeValue5434, nodeValue5438, nodeValue5451, nodeValue5481, nodeValue5484, nodeValue5490, nodeValue5492, nodeValue5494]
  ring

noncomputable def reducedSource977 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + 0))))))))))))))))))

def numericRow977 : Integer.Sparse Master := [(Sum.inl 0, 329), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -220), (Sum.inl 7, -80), (Sum.inl 8, -400), (Sum.inl 3, -320), (Sum.inl 24, 240), (Sum.inl 4, -160), (Sum.inl 27, 180), (Sum.inl 1, 260), (Sum.inl 30, 480), (Sum.inr 3602, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -8640), (Sum.inr 3622, -4320), (Sum.inr 3896, -4320), (Sum.inr 3898, -4320), (Sum.inr 3903, -8640), (Sum.inr 4041, -4320), (Sum.inr 4042, -8640), (Sum.inr 4045, -8640), (Sum.inr 4046, -12960), (Sum.inr 4047, -8640)]

theorem reindexCheck977 : Integer.Sparse.reindex keyMap MixedData.row977 = numericRow977 := by decide +kernel

theorem numericCheck977 (x : Master → ℝ) : Integer.Sparse.eval numericRow977 x =
    (17280 : ℝ) * reducedSource977 x := by
  norm_num [numericRow977, reducedSource977, Integer.Sparse.eval, Sparse.eval, nodeValue4096, nodeValue5167, nodeValue5168, nodeValue5169, nodeValue5292, nodeValue5416, nodeValue5418, nodeValue5434, nodeValue5464, nodeValue5465, nodeValue5476, nodeValue5482, nodeValue5483, nodeValue5486, nodeValue5487, nodeValue5490, nodeValue5493, nodeValue5497, nodeValue5499]
  ring

noncomputable def reducedSource978 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5055 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5344 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5467 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + 0)))))))))))))))))

def numericRow978 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 2, -6), (Sum.inl 4, -16), (Sum.inl 1, 21), (Sum.inr 2458, -432), (Sum.inr 2459, -432), (Sum.inr 2462, -432), (Sum.inr 2508, -432), (Sum.inr 2739, -432), (Sum.inr 3429, -432), (Sum.inr 3436, -432), (Sum.inr 3460, -432), (Sum.inr 3534, -432), (Sum.inr 3681, -432), (Sum.inr 3683, -432), (Sum.inr 3703, -432), (Sum.inr 3746, -432), (Sum.inr 3758, -432), (Sum.inr 3838, -432), (Sum.inr 3843, -432), (Sum.inr 3942, -432), (Sum.inr 3958, -432), (Sum.inr 3961, -432), (Sum.inr 3974, -432), (Sum.inr 4010, -432), (Sum.inr 4046, -432)]

theorem reindexCheck978 : Integer.Sparse.reindex keyMap MixedData.row978 = numericRow978 := by decide +kernel

theorem numericCheck978 (x : Master → ℝ) : Integer.Sparse.eval numericRow978 x =
    (864 : ℝ) * reducedSource978 x := by
  norm_num [numericRow978, reducedSource978, Integer.Sparse.eval, Sparse.eval, nodeValue5055, nodeValue5056, nodeValue5059, nodeValue5098, nodeValue5271, nodeValue5344, nodeValue5346, nodeValue5365, nodeValue5424, nodeValue5467, nodeValue5473, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5485, nodeValue5490, nodeValue5492, nodeValue5500]
  ring

noncomputable def reducedSource979 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue5396 x + ((3 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((6 : ℝ) * Sparse.eval nodeValue5478 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((3 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))

def numericRow979 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 80), (Sum.inr 3899, -720), (Sum.inr 3900, -1080), (Sum.inr 3901, -1080), (Sum.inr 3909, -720), (Sum.inr 3945, -1080), (Sum.inr 3952, -1080), (Sum.inr 3964, -1080), (Sum.inr 3974, -4320), (Sum.inr 4025, -720), (Sum.inr 4046, -1080), (Sum.inr 4091, 1440)]

theorem reindexCheck979 : Integer.Sparse.reindex keyMap MixedData.row979 = numericRow979 := by decide +kernel

theorem numericCheck979 (x : Master → ℝ) : Integer.Sparse.eval numericRow979 x =
    (1440 : ℝ) * reducedSource979 x := by
  norm_num [numericRow979, reducedSource979, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue5396, nodeValue5422, nodeValue5427, nodeValue5433, nodeValue5437, nodeValue5447, nodeValue5469, nodeValue5474, nodeValue5478, nodeValue5482, nodeValue5486]
  ring

noncomputable def reducedSource980 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5470 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))))))))

def numericRow980 : Integer.Sparse Master := [(Sum.inl 0, 64), (Sum.inl 2, -60), (Sum.inl 12, 40), (Sum.inl 4, -80), (Sum.inl 1, 180), (Sum.inr 2880, -2160), (Sum.inr 3617, -2160), (Sum.inr 3690, -4320), (Sum.inr 3692, -2160), (Sum.inr 3764, -4320), (Sum.inr 3769, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3910, -2160), (Sum.inr 3957, -8640), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4046, -4320), (Sum.inr 5184, 8640), (Sum.inr 5185, 17280), (Sum.inr 5265, 8640), (Sum.inr 5414, 8640), (Sum.inr 5429, 25920), (Sum.inr 5470, 17280)]

theorem reindexCheck980 : Integer.Sparse.reindex keyMap MixedData.row980 = numericRow980 := by decide +kernel

theorem numericCheck980 (x : Master → ℝ) : Integer.Sparse.eval numericRow980 x =
    (8640 : ℝ) * reducedSource980 x := by
  norm_num [numericRow980, reducedSource980, Integer.Sparse.eval, Sparse.eval, nodeValue5184, nodeValue5185, nodeValue5202, nodeValue5265, nodeValue5352, nodeValue5354, nodeValue5366, nodeValue5408, nodeValue5414, nodeValue5429, nodeValue5431, nodeValue5450, nodeValue5470, nodeValue5471, nodeValue5472, nodeValue5473, nodeValue5474, nodeValue5481, nodeValue5482, nodeValue5486]
  ring

noncomputable def reducedSource981 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((2 : ℝ) * Sparse.eval nodeValue3955 x + ((2 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3957 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3985 x + ((2 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4029 x + 0))))))))))))))))))))

def numericRow981 : Integer.Sparse Master := [(Sum.inl 0, -63), (Sum.inl 2, 105), (Sum.inl 3, 720), (Sum.inl 12, 280), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 560), (Sum.inl 1, -460), (Sum.inr 3524, 2160), (Sum.inr 3526, 2160), (Sum.inr 3529, 4320), (Sum.inr 3617, 2160), (Sum.inr 3764, 4320), (Sum.inr 3769, 2160), (Sum.inr 3869, 2160), (Sum.inr 3874, 4320), (Sum.inr 3954, 2160), (Sum.inr 3955, 4320), (Sum.inr 3957, 4320), (Sum.inr 3961, 4320)]

theorem reindexCheck981 : Integer.Sparse.reindex keyMap MixedData.row981 = numericRow981 := by decide +kernel

theorem numericCheck981 (x : Master → ℝ) : Integer.Sparse.eval numericRow981 x =
    (2160 : ℝ) * reducedSource981 x := by
  norm_num [numericRow981, reducedSource981, Integer.Sparse.eval, Sparse.eval, nodeValue3524, nodeValue3526, nodeValue3529, nodeValue3617, nodeValue3764, nodeValue3765, nodeValue3769, nodeValue3806, nodeValue3869, nodeValue3874, nodeValue3954, nodeValue3955, nodeValue3956, nodeValue3957, nodeValue3961, nodeValue3962, nodeValue3979, nodeValue3980, nodeValue3985, nodeValue4026, nodeValue4029]
  ring

noncomputable def reducedSource982 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4996 x + ((2 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5013 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((4 : ℝ) * Sparse.eval nodeValue5395 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5469 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))

def numericRow982 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 2, -11), (Sum.inl 3, -16), (Sum.inl 4, 32), (Sum.inl 1, -14), (Sum.inr 2382, -1728), (Sum.inr 2383, -864), (Sum.inr 2398, -864), (Sum.inr 2721, -864), (Sum.inr 3340, -1728), (Sum.inr 3341, -864), (Sum.inr 3352, -864), (Sum.inr 3532, -864), (Sum.inr 3781, -1728), (Sum.inr 3794, -1728), (Sum.inr 3845, -1728), (Sum.inr 3945, -864), (Sum.inr 3952, -864), (Sum.inr 3958, -1728), (Sum.inr 3961, -1728), (Sum.inr 4046, -864)]

theorem reindexCheck982 : Integer.Sparse.reindex keyMap MixedData.row982 = numericRow982 := by decide +kernel

theorem numericCheck982 (x : Master → ℝ) : Integer.Sparse.eval numericRow982 x =
    (1728 : ℝ) * reducedSource982 x := by
  norm_num [numericRow982, reducedSource982, Integer.Sparse.eval, Sparse.eval, nodeValue4996, nodeValue4998, nodeValue5013, nodeValue5257, nodeValue5395, nodeValue5428, nodeValue5469, nodeValue5473, nodeValue5482, nodeValue5489, nodeValue5490]
  ring

noncomputable def reducedSource983 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4859 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue5383 x + ((4 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5398 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))

def numericRow983 : Integer.Sparse Master := [(Sum.inl 0, 657), (Sum.inl 5, 60), (Sum.inl 2, 15), (Sum.inl 7, 240), (Sum.inl 3, -240), (Sum.inl 23, -720), (Sum.inl 12, -480), (Sum.inl 27, -180), (Sum.inl 1, 2970), (Sum.inr 2100, -12960), (Sum.inr 2101, -25920), (Sum.inr 2110, -12960), (Sum.inr 2275, -12960), (Sum.inr 3731, -12960), (Sum.inr 3732, -25920), (Sum.inr 3784, -25920), (Sum.inr 3789, -12960), (Sum.inr 3810, -12960), (Sum.inr 3811, -25920), (Sum.inr 3867, -12960), (Sum.inr 3885, -25920), (Sum.inr 3886, -25920), (Sum.inr 3891, -12960), (Sum.inr 3902, -12960), (Sum.inr 3907, -25920)]

theorem reindexCheck983 : Integer.Sparse.reindex keyMap MixedData.row983 = numericRow983 := by decide +kernel

theorem numericCheck983 (x : Master → ℝ) : Integer.Sparse.eval numericRow983 x =
    (25920 : ℝ) * reducedSource983 x := by
  norm_num [numericRow983, reducedSource983, Integer.Sparse.eval, Sparse.eval, nodeValue4859, nodeValue4860, nodeValue4869, nodeValue5383, nodeValue5384, nodeValue5387, nodeValue5398, nodeValue5403, nodeValue5439, nodeValue5443, nodeValue5448, nodeValue5449, nodeValue5488, nodeValue5491]
  ring

noncomputable def reducedSource984 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5445 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow984 : Integer.Sparse Master := [(Sum.inl 0, 107), (Sum.inl 2, -95), (Sum.inl 3, -400), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, 130), (Sum.inr 2721, -4320), (Sum.inr 3532, -4320), (Sum.inr 3787, -8640), (Sum.inr 3789, -4320), (Sum.inr 3804, -8640), (Sum.inr 3810, -4320), (Sum.inr 3857, -8640), (Sum.inr 3876, -8640), (Sum.inr 3885, -8640), (Sum.inr 3901, -8640), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 5185, 34560), (Sum.inr 5187, 17280), (Sum.inr 5197, 17280), (Sum.inr 5219, 17280), (Sum.inr 5220, 17280), (Sum.inr 5226, 34560), (Sum.inr 5281, 17280), (Sum.inr 5425, 34560), (Sum.inr 5430, 34560), (Sum.inr 5445, 34560)]

theorem reindexCheck984 : Integer.Sparse.reindex keyMap MixedData.row984 = numericRow984 := by decide +kernel

theorem numericCheck984 (x : Master → ℝ) : Integer.Sparse.eval numericRow984 x =
    (17280 : ℝ) * reducedSource984 x := by
  norm_num [numericRow984, reducedSource984, Integer.Sparse.eval, Sparse.eval, nodeValue5185, nodeValue5187, nodeValue5197, nodeValue5219, nodeValue5220, nodeValue5226, nodeValue5257, nodeValue5281, nodeValue5401, nodeValue5403, nodeValue5408, nodeValue5425, nodeValue5430, nodeValue5433, nodeValue5438, nodeValue5440, nodeValue5445, nodeValue5448, nodeValue5478, nodeValue5481, nodeValue5485]
  ring

noncomputable def reducedSource985 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((2 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

def numericRow985 : Integer.Sparse Master := [(Sum.inl 0, -109), (Sum.inl 2, 195), (Sum.inl 3, 1040), (Sum.inl 12, 320), (Sum.inl 26, 160), (Sum.inl 4, 640), (Sum.inl 1, -620), (Sum.inl 31, -480), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2669, 8640), (Sum.inr 2750, 4320), (Sum.inr 3529, 8640), (Sum.inr 3532, 4320), (Sum.inr 3537, 4320), (Sum.inr 3569, 4320), (Sum.inr 3804, 8640), (Sum.inr 3810, 4320), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3857, 8640), (Sum.inr 3880, 8640), (Sum.inr 3885, 4320)]

theorem reindexCheck985 : Integer.Sparse.reindex keyMap MixedData.row985 = numericRow985 := by decide +kernel

theorem numericCheck985 (x : Master → ℝ) : Integer.Sparse.eval numericRow985 x =
    (4320 : ℝ) * reducedSource985 x := by
  norm_num [numericRow985, reducedSource985, Integer.Sparse.eval, Sparse.eval, nodeValue2661, nodeValue2662, nodeValue2669, nodeValue2750, nodeValue3529, nodeValue3532, nodeValue3537, nodeValue3569, nodeValue3804, nodeValue3806, nodeValue3810, nodeValue3840, nodeValue3848, nodeValue3851, nodeValue3857, nodeValue3859, nodeValue3880, nodeValue3885, nodeValue3979, nodeValue3994, nodeValue3998]
  ring

noncomputable def reducedSource986 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

def numericRow986 : Integer.Sparse Master := [(Sum.inl 0, 1548), (Sum.inl 5, -240), (Sum.inl 6, 15), (Sum.inl 2, -195), (Sum.inl 7, -1200), (Sum.inl 3, -2640), (Sum.inl 23, 1440), (Sum.inl 24, 1440), (Sum.inl 12, -720), (Sum.inl 4, 480), (Sum.inl 27, 720), (Sum.inl 1, -1890), (Sum.inr 2016, -25920), (Sum.inr 2023, -12960), (Sum.inr 2046, -12960), (Sum.inr 2075, -25920), (Sum.inr 2077, -12960), (Sum.inr 2105, -12960), (Sum.inr 2214, -12960), (Sum.inr 2241, -12960), (Sum.inr 3687, -25920), (Sum.inr 3692, -12960), (Sum.inr 3701, -12960), (Sum.inr 3719, -25920), (Sum.inr 3721, -12960), (Sum.inr 3749, -25920), (Sum.inr 3751, -12960), (Sum.inr 3769, -12960), (Sum.inr 3786, -25920), (Sum.inr 3795, -25920), (Sum.inr 3799, -25920), (Sum.inr 3836, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -51840), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3890, -12960), (Sum.inr 3897, -12960), (Sum.inr 3901, -12960), (Sum.inr 3906, -25920), (Sum.inr 3910, -25920)]

theorem reindexCheck986 : Integer.Sparse.reindex keyMap MixedData.row986 = numericRow986 := by decide +kernel

theorem numericCheck986 (x : Master → ℝ) : Integer.Sparse.eval numericRow986 x =
    (51840 : ℝ) * reducedSource986 x := by
  norm_num [numericRow986, reducedSource986, Integer.Sparse.eval, Sparse.eval, nodeValue4798, nodeValue4805, nodeValue4826, nodeValue4864, nodeValue5349, nodeValue5354, nodeValue5363, nodeValue5378, nodeValue5380, nodeValue5386, nodeValue5400, nodeValue5417, nodeValue5431, nodeValue5432, nodeValue5433, nodeValue5435, nodeValue5438, nodeValue5450, nodeValue5481, nodeValue5489, nodeValue5490]
  ring

noncomputable def reducedSource987 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3735 x + ((2 : ℝ) * Sparse.eval nodeValue3749 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((2 : ℝ) * Sparse.eval nodeValue3799 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3897 x + ((2 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + 0))))))))))))))))))))

def numericRow987 : Integer.Sparse Master := [(Sum.inl 0, -269), (Sum.inl 5, 60), (Sum.inl 2, 25), (Sum.inl 7, 240), (Sum.inl 3, 560), (Sum.inl 23, -240), (Sum.inl 24, -480), (Sum.inl 12, 160), (Sum.inl 27, -180), (Sum.inl 1, 250), (Sum.inr 2075, 8640), (Sum.inr 2077, 4320), (Sum.inr 2105, 4320), (Sum.inr 2214, 4320), (Sum.inr 3719, 8640), (Sum.inr 3721, 4320), (Sum.inr 3749, 8640), (Sum.inr 3751, 4320), (Sum.inr 3769, 4320), (Sum.inr 3799, 8640), (Sum.inr 3850, 8640), (Sum.inr 3875, 4320), (Sum.inr 3876, 8640), (Sum.inr 3897, 4320), (Sum.inr 3906, 8640)]

theorem reindexCheck987 : Integer.Sparse.reindex keyMap MixedData.row987 = numericRow987 := by decide +kernel

theorem numericCheck987 (x : Master → ℝ) : Integer.Sparse.eval numericRow987 x =
    (4320 : ℝ) * reducedSource987 x := by
  norm_num [numericRow987, reducedSource987, Integer.Sparse.eval, Sparse.eval, nodeValue2075, nodeValue2077, nodeValue2105, nodeValue2214, nodeValue3719, nodeValue3721, nodeValue3735, nodeValue3749, nodeValue3751, nodeValue3769, nodeValue3799, nodeValue3850, nodeValue3875, nodeValue3876, nodeValue3887, nodeValue3897, nodeValue3906, nodeValue4008, nodeValue4009, nodeValue4013, nodeValue4033]
  ring

noncomputable def reducedSource988 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0)))))))))))))))))))

def numericRow988 : Integer.Sparse Master := [(Sum.inl 0, 115), (Sum.inl 2, -75), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 30), (Sum.inr 2589, -4320), (Sum.inr 2764, -4320), (Sum.inr 3563, -4320), (Sum.inr 3581, -4320), (Sum.inr 3731, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -8640), (Sum.inr 3867, -4320), (Sum.inr 3875, -8640), (Sum.inr 3885, -8640), (Sum.inr 3910, -8640), (Sum.inr 3957, -17280), (Sum.inr 4046, -4320), (Sum.inr 5145, 34560), (Sum.inr 5150, 17280), (Sum.inr 5243, 17280), (Sum.inr 5244, 17280), (Sum.inr 5265, 34560), (Sum.inr 5379, 34560), (Sum.inr 5421, 34560), (Sum.inr 5429, 51840)]

theorem reindexCheck988 : Integer.Sparse.reindex keyMap MixedData.row988 = numericRow988 := by decide +kernel

theorem numericCheck988 (x : Master → ℝ) : Integer.Sparse.eval numericRow988 x =
    (17280 : ℝ) * reducedSource988 x := by
  norm_num [numericRow988, reducedSource988, Integer.Sparse.eval, Sparse.eval, nodeValue5145, nodeValue5150, nodeValue5162, nodeValue5243, nodeValue5244, nodeValue5265, nodeValue5290, nodeValue5379, nodeValue5383, nodeValue5421, nodeValue5424, nodeValue5427, nodeValue5429, nodeValue5431, nodeValue5440, nodeValue5448, nodeValue5450, nodeValue5471, nodeValue5472, nodeValue5482]
  ring

noncomputable def reducedSource989 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))))))))

def numericRow989 : Integer.Sparse Master := [(Sum.inl 0, 267), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -170), (Sum.inl 7, -320), (Sum.inl 8, -160), (Sum.inl 3, -1120), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -400), (Sum.inl 4, -160), (Sum.inl 27, 180), (Sum.inl 1, -100), (Sum.inr 3602, -4320), (Sum.inr 3607, -8640), (Sum.inr 3613, -4320), (Sum.inr 3890, -4320), (Sum.inr 3891, -4320), (Sum.inr 3892, -8640), (Sum.inr 3896, -8640), (Sum.inr 3897, -4320), (Sum.inr 3901, -8640), (Sum.inr 3903, -8640), (Sum.inr 3906, -8640), (Sum.inr 3910, -4320)]

theorem reindexCheck989 : Integer.Sparse.reindex keyMap MixedData.row989 = numericRow989 := by decide +kernel

theorem numericCheck989 (x : Master → ℝ) : Integer.Sparse.eval numericRow989 x =
    (17280 : ℝ) * reducedSource989 x := by
  norm_num [numericRow989, reducedSource989, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5167, nodeValue5169, nodeValue5172, nodeValue5307, nodeValue5386, nodeValue5387, nodeValue5388, nodeValue5416, nodeValue5417, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5440, nodeValue5442, nodeValue5450, nodeValue5454, nodeValue5489, nodeValue5490, nodeValue5493]
  ring

noncomputable def reducedSource990 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((3 : ℝ) * Sparse.eval nodeValue5396 x + ((6 : ℝ) * Sparse.eval nodeValue5424 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + ((3 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5479 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))

def numericRow990 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 230), (Sum.inr 2556, -4320), (Sum.inr 2589, -1440), (Sum.inr 3521, -4320), (Sum.inr 3563, -1440), (Sum.inr 3721, -4320), (Sum.inr 3731, -1440), (Sum.inr 3836, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3849, -4320), (Sum.inr 3867, -1440), (Sum.inr 3875, -4320), (Sum.inr 3909, -1440), (Sum.inr 4025, -1440), (Sum.inr 4046, -4320), (Sum.inr 4091, 5760)]

theorem reindexCheck990 : Integer.Sparse.reindex keyMap MixedData.row990 = numericRow990 := by decide +kernel

theorem numericCheck990 (x : Master → ℝ) : Integer.Sparse.eval numericRow990 x =
    (5760 : ℝ) * reducedSource990 x := by
  norm_num [numericRow990, reducedSource990, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue5137, nodeValue5162, nodeValue5273, nodeValue5380, nodeValue5383, nodeValue5396, nodeValue5424, nodeValue5431, nodeValue5440, nodeValue5447, nodeValue5479, nodeValue5482]
  ring

noncomputable def reducedSource991 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4079 x + ((3 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((3 : ℝ) * Sparse.eval nodeValue4088 x + ((3 : ℝ) * Sparse.eval nodeValue4090 x + ((5 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((3 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4095 x + ((3 : ℝ) * Sparse.eval nodeValue4096 x + 0))))))))))

def numericRow991 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 1, 5), (Sum.inr 4079, 60), (Sum.inr 4080, 180), (Sum.inr 4083, 60), (Sum.inr 4087, 60), (Sum.inr 4088, 180), (Sum.inr 4090, 180), (Sum.inr 4091, 300), (Sum.inr 4092, 360)]

theorem reindexCheck991 : Integer.Sparse.reindex keyMap MixedData.row991 = numericRow991 := by decide +kernel

theorem numericCheck991 (x : Master → ℝ) : Integer.Sparse.eval numericRow991 x =
    (60 : ℝ) * reducedSource991 x := by
  norm_num [numericRow991, reducedSource991, Integer.Sparse.eval, Sparse.eval, nodeValue4079, nodeValue4080, nodeValue4083, nodeValue4087, nodeValue4088, nodeValue4090, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4095, nodeValue4096]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
