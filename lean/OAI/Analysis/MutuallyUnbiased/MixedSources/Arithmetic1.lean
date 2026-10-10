import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource16 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3914 x + ((2 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((2 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + ((1 : ℝ) * Sparse.eval nodeValue4021 x + 0))))))))))))))))))))

def numericRow16 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 4, -80), (Sum.inl 1, 75), (Sum.inr 2764, 1080), (Sum.inr 2765, 540), (Sum.inr 2782, 540), (Sum.inr 3876, 1080), (Sum.inr 3907, 540), (Sum.inr 3910, 1080), (Sum.inr 3913, 540), (Sum.inr 3983, 1080)]

theorem reindexCheck16 : Integer.Sparse.reindex keyMap MixedData.row16 = numericRow16 := by decide +kernel

theorem numericCheck16 (x : Master → ℝ) : Integer.Sparse.eval numericRow16 x =
    (540 : ℝ) * reducedSource16 x := by
  norm_num [numericRow16, reducedSource16, Integer.Sparse.eval, Sparse.eval, nodeValue2764, nodeValue2765, nodeValue2768, nodeValue2782, nodeValue3876, nodeValue3888, nodeValue3907, nodeValue3910, nodeValue3913, nodeValue3914, nodeValue3979, nodeValue3982, nodeValue3983, nodeValue3998, nodeValue4001, nodeValue4013, nodeValue4017, nodeValue4018, nodeValue4019, nodeValue4020, nodeValue4021]
  ring

noncomputable def reducedSource17 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((4 : ℝ) * Sparse.eval nodeValue5485 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))

def numericRow17 : Integer.Sparse Master := [(Sum.inl 0, 91), (Sum.inl 4, 80), (Sum.inl 1, 45), (Sum.inr 2739, -1440), (Sum.inr 2740, -720), (Sum.inr 2743, -720), (Sum.inr 3534, -1440), (Sum.inr 3548, -720), (Sum.inr 3623, -720), (Sum.inr 3958, -1440), (Sum.inr 3961, -1440), (Sum.inr 3963, -720), (Sum.inr 3974, -1440), (Sum.inr 4010, -1440)]

theorem reindexCheck17 : Integer.Sparse.reindex keyMap MixedData.row17 = numericRow17 := by decide +kernel

theorem numericCheck17 (x : Master → ℝ) : Integer.Sparse.eval numericRow17 x =
    (1440 : ℝ) * reducedSource17 x := by
  norm_num [numericRow17, reducedSource17, Integer.Sparse.eval, Sparse.eval, nodeValue5271, nodeValue5272, nodeValue5275, nodeValue5306, nodeValue5473, nodeValue5475, nodeValue5478, nodeValue5485, nodeValue5490, nodeValue5491, nodeValue5492, nodeValue5493, nodeValue5501]
  ring

noncomputable def reducedSource18 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((3 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + ((1 : ℝ) * Sparse.eval nodeValue5500 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))))))))))))))

def numericRow18 : Integer.Sparse Master := [(Sum.inl 0, 1115), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, -240), (Sum.inl 1, 875), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3622, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320), (Sum.inr 3957, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 3974, -8640), (Sum.inr 4010, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -4320)]

theorem reindexCheck18 : Integer.Sparse.reindex keyMap MixedData.row18 = numericRow18 := by decide +kernel

theorem numericCheck18 (x : Master → ℝ) : Integer.Sparse.eval numericRow18 x =
    (17280 : ℝ) * reducedSource18 x := by
  norm_num [numericRow18, reducedSource18, Integer.Sparse.eval, Sparse.eval, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5424, nodeValue5428, nodeValue5434, nodeValue5439, nodeValue5472, nodeValue5473, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5489, nodeValue5490, nodeValue5491, nodeValue5492, nodeValue5493, nodeValue5499, nodeValue5500, nodeValue5501]
  ring

noncomputable def reducedSource19 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4050 x + ((1 : ℝ) * Sparse.eval nodeValue4052 x + ((1 : ℝ) * Sparse.eval nodeValue4053 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + ((1 : ℝ) * Sparse.eval nodeValue4055 x + 0))))))))))))))))))))))))))))

def numericRow19 : Integer.Sparse Master := [(Sum.inl 0, -161), (Sum.inl 4, 80), (Sum.inl 1, -135), (Sum.inr 2721, 1080), (Sum.inr 2722, 1080), (Sum.inr 2723, 1080), (Sum.inr 2739, 1080), (Sum.inr 3838, 1080), (Sum.inr 3845, 1080), (Sum.inr 3902, 1080), (Sum.inr 3957, 1080), (Sum.inr 3958, 1080), (Sum.inr 3961, 1080), (Sum.inr 3974, 1080), (Sum.inr 4010, 1080)]

theorem reindexCheck19 : Integer.Sparse.reindex keyMap MixedData.row19 = numericRow19 := by decide +kernel

theorem numericCheck19 (x : Master → ℝ) : Integer.Sparse.eval numericRow19 x =
    (1080 : ℝ) * reducedSource19 x := by
  norm_num [numericRow19, reducedSource19, Integer.Sparse.eval, Sparse.eval, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2739, nodeValue2766, nodeValue3838, nodeValue3845, nodeValue3852, nodeValue3902, nodeValue3957, nodeValue3958, nodeValue3961, nodeValue3971, nodeValue3974, nodeValue3980, nodeValue3981, nodeValue3992, nodeValue3999, nodeValue4009, nodeValue4010, nodeValue4013, nodeValue4014, nodeValue4015, nodeValue4018, nodeValue4050, nodeValue4052, nodeValue4053, nodeValue4054, nodeValue4055]
  ring

noncomputable def reducedSource20 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((3 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))

def numericRow20 : Integer.Sparse Master := [(Sum.inl 0, 220), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, -245), (Sum.inr 3849, -2160), (Sum.inr 3850, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3901, -2160), (Sum.inr 3903, -2160), (Sum.inr 3906, -2160), (Sum.inr 3910, -2160), (Sum.inr 3983, -2160)]

theorem reindexCheck20 : Integer.Sparse.reindex keyMap MixedData.row20 = numericRow20 := by decide +kernel

theorem numericCheck20 (x : Master → ℝ) : Integer.Sparse.eval numericRow20 x =
    (4320 : ℝ) * reducedSource20 x := by
  norm_num [numericRow20, reducedSource20, Integer.Sparse.eval, Sparse.eval, nodeValue5431, nodeValue5432, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5450, nodeValue5454, nodeValue5481, nodeValue5484, nodeValue5489, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5495]
  ring

noncomputable def reducedSource21 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((6 : ℝ) * Sparse.eval nodeValue5484 x + ((6 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))

def numericRow21 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 4, -80), (Sum.inl 1, -15), (Sum.inr 2782, -720), (Sum.inr 2783, -240), (Sum.inr 3583, -720), (Sum.inr 3633, -240), (Sum.inr 3913, -720), (Sum.inr 3983, -1440)]

theorem reindexCheck21 : Integer.Sparse.reindex keyMap MixedData.row21 = numericRow21 := by decide +kernel

theorem numericCheck21 (x : Master → ℝ) : Integer.Sparse.eval numericRow21 x =
    (480 : ℝ) * reducedSource21 x := by
  norm_num [numericRow21, reducedSource21, Integer.Sparse.eval, Sparse.eval, nodeValue5304, nodeValue5305, nodeValue5310, nodeValue5451, nodeValue5455, nodeValue5484, nodeValue5492, nodeValue5495]
  ring

noncomputable def reducedSource22 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5501 x + 0)))))))))))))

def numericRow22 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 1, 5), (Sum.inr 3622, -240), (Sum.inr 3623, -120), (Sum.inr 3627, -240), (Sum.inr 4010, -240), (Sum.inr 4046, -240), (Sum.inr 4047, -480)]

theorem reindexCheck22 : Integer.Sparse.reindex keyMap MixedData.row22 = numericRow22 := by decide +kernel

theorem numericCheck22 (x : Master → ℝ) : Integer.Sparse.eval numericRow22 x =
    (480 : ℝ) * reducedSource22 x := by
  norm_num [numericRow22, reducedSource22, Integer.Sparse.eval, Sparse.eval, nodeValue4096, nodeValue5292, nodeValue5293, nodeValue5306, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5487, nodeValue5490, nodeValue5491, nodeValue5492, nodeValue5499, nodeValue5501]
  ring

noncomputable def reducedSource23 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((4 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((2 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))

def numericRow23 : Integer.Sparse Master := [(Sum.inl 0, 174), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 160), (Sum.inl 1, -215), (Sum.inr 3910, -2160), (Sum.inr 3913, -2160), (Sum.inr 4010, -4320)]

theorem reindexCheck23 : Integer.Sparse.reindex keyMap MixedData.row23 = numericRow23 := by decide +kernel

theorem numericCheck23 (x : Master → ℝ) : Integer.Sparse.eval numericRow23 x =
    (4320 : ℝ) * reducedSource23 x := by
  norm_num [numericRow23, reducedSource23, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5440, nodeValue5442, nodeValue5450, nodeValue5451, nodeValue5452, nodeValue5453, nodeValue5454, nodeValue5485, nodeValue5489, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5495]
  ring

noncomputable def reducedSource24 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((3 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))))))

def numericRow24 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3622, -16), (Sum.inr 3627, -8), (Sum.inr 3632, -8), (Sum.inr 3901, -16), (Sum.inr 3903, -16), (Sum.inr 3906, -16), (Sum.inr 3907, -8), (Sum.inr 3910, -16), (Sum.inr 3913, -8)]

theorem reindexCheck24 : Integer.Sparse.reindex keyMap MixedData.row24 = numericRow24 := by decide +kernel

theorem numericCheck24 (x : Master → ℝ) : Integer.Sparse.eval numericRow24 x =
    (32 : ℝ) * reducedSource24 x := by
  norm_num [numericRow24, reducedSource24, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5292, nodeValue5293, nodeValue5294, nodeValue5307, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5440, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5452, nodeValue5453, nodeValue5454, nodeValue5455, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5495]
  ring

noncomputable def reducedSource25 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((6 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((6 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue4096 x + ((2 : ℝ) * Sparse.eval nodeValue4097 x + 0)))))))

def numericRow25 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 1, -5), (Sum.inr 4083, 120), (Sum.inr 4084, 80), (Sum.inr 4091, 240), (Sum.inr 4092, 240)]

theorem reindexCheck25 : Integer.Sparse.reindex keyMap MixedData.row25 = numericRow25 := by decide +kernel

theorem numericCheck25 (x : Master → ℝ) : Integer.Sparse.eval numericRow25 x =
    (40 : ℝ) * reducedSource25 x := by
  norm_num [numericRow25, reducedSource25, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4084, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4094, nodeValue4096, nodeValue4097]
  ring

noncomputable def reducedSource26 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((8 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5489 x + ((8 : ℝ) * Sparse.eval nodeValue5499 x + 0))))

def numericRow26 : Integer.Sparse Master := [(Sum.inl 0, 82), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, 40), (Sum.inl 4, -160), (Sum.inl 1, 155), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 4046, -4320)]

theorem reindexCheck26 : Integer.Sparse.reindex keyMap MixedData.row26 = numericRow26 := by decide +kernel

theorem numericCheck26 (x : Master → ℝ) : Integer.Sparse.eval numericRow26 x =
    (2160 : ℝ) * reducedSource26 x := by
  norm_num [numericRow26, reducedSource26, Integer.Sparse.eval, Sparse.eval, nodeValue5405, nodeValue5452, nodeValue5482, nodeValue5489, nodeValue5499]
  ring

noncomputable def reducedSource27 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((4 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5497 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))

def numericRow27 : Integer.Sparse Master := [(Sum.inl 0, 76), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 95), (Sum.inr 3837, -540), (Sum.inr 3838, -1080), (Sum.inr 3843, -1080), (Sum.inr 3901, -1080), (Sum.inr 3974, -1080), (Sum.inr 4046, -1080)]

theorem reindexCheck27 : Integer.Sparse.reindex keyMap MixedData.row27 = numericRow27 := by decide +kernel

theorem numericCheck27 (x : Master → ℝ) : Integer.Sparse.eval numericRow27 x =
    (1080 : ℝ) * reducedSource27 x := by
  norm_num [numericRow27, reducedSource27, Integer.Sparse.eval, Sparse.eval, nodeValue5423, nodeValue5424, nodeValue5433, nodeValue5477, nodeValue5478, nodeValue5482, nodeValue5490, nodeValue5497, nodeValue5499, nodeValue5500, nodeValue5501]
  ring

noncomputable def reducedSource28 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + ((2 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))))))

def numericRow28 : Integer.Sparse Master := [(Sum.inl 0, 468), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -160), (Sum.inl 1, 425), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 3903, -4320), (Sum.inr 4010, -2160), (Sum.inr 4046, -6480), (Sum.inr 4047, -4320)]

theorem reindexCheck28 : Integer.Sparse.reindex keyMap MixedData.row28 = numericRow28 := by decide +kernel

theorem numericCheck28 (x : Master → ℝ) : Integer.Sparse.eval numericRow28 x =
    (8640 : ℝ) * reducedSource28 x := by
  norm_num [numericRow28, reducedSource28, Integer.Sparse.eval, Sparse.eval, nodeValue4096, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5452, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5489, nodeValue5490, nodeValue5493, nodeValue5497, nodeValue5498, nodeValue5499, nodeValue5500, nodeValue5501]
  ring

noncomputable def reducedSource29 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + ((4 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4095 x + ((8 : ℝ) * Sparse.eval nodeValue4096 x + ((4 : ℝ) * Sparse.eval nodeValue4097 x + 0)))))

def numericRow29 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 1, 5), (Sum.inr 4091, 720), (Sum.inr 4092, 360)]

theorem reindexCheck29 : Integer.Sparse.reindex keyMap MixedData.row29 = numericRow29 := by decide +kernel

theorem numericCheck29 (x : Master → ℝ) : Integer.Sparse.eval numericRow29 x =
    (90 : ℝ) * reducedSource29 x := by
  norm_num [numericRow29, reducedSource29, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue4092, nodeValue4093, nodeValue4095, nodeValue4096, nodeValue4097]
  ring

noncomputable def reducedSource30 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1092 x + ((3 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow30 : Integer.Sparse Master := [(Sum.inr 1092, 1), (Sum.inr 2063, 3), (Sum.inr 2285, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem reindexCheck30 : Integer.Sparse.reindex keyMap MixedData.row30 = numericRow30 := by decide +kernel

theorem numericCheck30 (x : Master → ℝ) : Integer.Sparse.eval numericRow30 x =
    (1 : ℝ) * reducedSource30 x := by
  norm_num [numericRow30, reducedSource30, Integer.Sparse.eval, Sparse.eval, nodeValue1092, nodeValue2063, nodeValue2285, nodeValue2294, nodeValue4085]

noncomputable def reducedSource31 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1067 x + ((1 : ℝ) * Sparse.eval nodeValue1069 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow31 : Integer.Sparse Master := [(Sum.inr 1067, 3), (Sum.inr 1069, 1), (Sum.inr 1092, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem reindexCheck31 : Integer.Sparse.reindex keyMap MixedData.row31 = numericRow31 := by decide +kernel

theorem numericCheck31 (x : Master → ℝ) : Integer.Sparse.eval numericRow31 x =
    (1 : ℝ) * reducedSource31 x := by
  norm_num [numericRow31, reducedSource31, Integer.Sparse.eval, Sparse.eval, nodeValue1067, nodeValue1069, nodeValue1092, nodeValue2285, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
