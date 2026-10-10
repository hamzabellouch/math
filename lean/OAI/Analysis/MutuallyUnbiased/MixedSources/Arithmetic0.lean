import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource0 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5412 x + ((6 : ℝ) * Sparse.eval nodeValue5443 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + 0)))))))

def numericRow0 : Integer.Sparse Master := [(Sum.inl 0, 10), (Sum.inl 12, -40), (Sum.inl 1, 30), (Sum.inr 2279, -540), (Sum.inr 2281, -180), (Sum.inr 2294, -180), (Sum.inr 3054, -540), (Sum.inr 3626, -540), (Sum.inr 3633, -180), (Sum.inr 3814, -1080), (Sum.inr 3907, -540)]

theorem reindexCheck0 : Integer.Sparse.reindex keyMap MixedData.row0 = numericRow0 := by decide +kernel

theorem numericCheck0 (x : Master → ℝ) : Integer.Sparse.eval numericRow0 x =
    (360 : ℝ) * reducedSource0 x := by
  norm_num [numericRow0, reducedSource0, Integer.Sparse.eval, Sparse.eval, nodeValue4898, nodeValue4899, nodeValue5302, nodeValue5310, nodeValue5412, nodeValue5443, nodeValue5453, nodeValue5455]
  ring

noncomputable def reducedSource1 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((4 : ℝ) * Sparse.eval nodeValue5411 x + ((4 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

def numericRow1 : Integer.Sparse Master := [(Sum.inl 0, 35), (Sum.inl 12, 40), (Sum.inl 1, -75), (Sum.inr 2245, -432), (Sum.inr 2247, -216), (Sum.inr 2266, -432), (Sum.inr 2277, -432), (Sum.inr 2278, -432), (Sum.inr 2290, -216), (Sum.inr 3077, -432), (Sum.inr 3625, -432), (Sum.inr 3632, -432), (Sum.inr 3801, -432), (Sum.inr 3809, -864), (Sum.inr 3812, -432), (Sum.inr 3813, -864), (Sum.inr 3906, -864), (Sum.inr 3907, -432), (Sum.inr 3910, -432), (Sum.inr 3913, -432)]

theorem reindexCheck1 : Integer.Sparse.reindex keyMap MixedData.row1 = numericRow1 := by decide +kernel

theorem numericCheck1 (x : Master → ℝ) : Integer.Sparse.eval numericRow1 x =
    (864 : ℝ) * reducedSource1 x := by
  norm_num [numericRow1, reducedSource1, Integer.Sparse.eval, Sparse.eval, nodeValue4889, nodeValue4890, nodeValue4896, nodeValue5284, nodeValue5294, nodeValue5406, nodeValue5411, nodeValue5435, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5452, nodeValue5454, nodeValue5493]
  ring

noncomputable def reducedSource2 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3801 x + ((4 : ℝ) * Sparse.eval nodeValue3809 x + ((4 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((2 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue4016 x + ((2 : ℝ) * Sparse.eval nodeValue4039 x + ((2 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))

def numericRow2 : Integer.Sparse Master := [(Sum.inl 0, -35), (Sum.inl 12, -40), (Sum.inl 1, 75), (Sum.inr 2245, 720), (Sum.inr 2247, 360), (Sum.inr 2266, 720), (Sum.inr 3077, 720), (Sum.inr 3801, 720), (Sum.inr 3809, 1440), (Sum.inr 3910, 720), (Sum.inr 3913, 720)]

theorem reindexCheck2 : Integer.Sparse.reindex keyMap MixedData.row2 = numericRow2 := by decide +kernel

theorem numericCheck2 (x : Master → ℝ) : Integer.Sparse.eval numericRow2 x =
    (360 : ℝ) * reducedSource2 x := by
  norm_num [numericRow2, reducedSource2, Integer.Sparse.eval, Sparse.eval, nodeValue2245, nodeValue2247, nodeValue2266, nodeValue3077, nodeValue3101, nodeValue3801, nodeValue3809, nodeValue3853, nodeValue3862, nodeValue3910, nodeValue3913, nodeValue4016, nodeValue4039, nodeValue4040]
  ring

noncomputable def reducedSource3 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5301 x + ((4 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((4 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5437 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))

def numericRow3 : Integer.Sparse Master := [(Sum.inl 0, 26), (Sum.inl 12, 40), (Sum.inl 1, 150), (Sum.inr 3053, -720), (Sum.inr 3054, -720), (Sum.inr 3619, -720), (Sum.inr 3623, -360), (Sum.inr 3626, -720), (Sum.inr 3814, -1440), (Sum.inr 3899, -720), (Sum.inr 3902, -720)]

theorem reindexCheck3 : Integer.Sparse.reindex keyMap MixedData.row3 = numericRow3 := by decide +kernel

theorem numericCheck3 (x : Master → ℝ) : Integer.Sparse.eval numericRow3 x =
    (720 : ℝ) * reducedSource3 x := by
  norm_num [numericRow3, reducedSource3, Integer.Sparse.eval, Sparse.eval, nodeValue5301, nodeValue5302, nodeValue5306, nodeValue5412, nodeValue5437, nodeValue5439, nodeValue5453, nodeValue5455, nodeValue5456]
  ring

noncomputable def reducedSource4 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((4 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))

def numericRow4 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 2723, -16), (Sum.inr 2726, -4), (Sum.inr 2743, -8), (Sum.inr 3544, -16), (Sum.inr 3545, -4), (Sum.inr 3548, -8), (Sum.inr 3627, -8), (Sum.inr 3958, -16), (Sum.inr 3961, -16), (Sum.inr 3963, -8), (Sum.inr 4047, -16)]

theorem reindexCheck4 : Integer.Sparse.reindex keyMap MixedData.row4 = numericRow4 := by decide +kernel

theorem numericCheck4 (x : Master → ℝ) : Integer.Sparse.eval numericRow4 x =
    (16 : ℝ) * reducedSource4 x := by
  norm_num [numericRow4, reducedSource4, Integer.Sparse.eval, Sparse.eval, nodeValue5259, nodeValue5261, nodeValue5275, nodeValue5293, nodeValue5473, nodeValue5475, nodeValue5477, nodeValue5483, nodeValue5487, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5501]
  ring

noncomputable def reducedSource5 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((4 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((2 : ℝ) * Sparse.eval nodeValue3971 x + ((4 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((4 : ℝ) * Sparse.eval nodeValue4013 x + ((2 : ℝ) * Sparse.eval nodeValue4015 x + ((2 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4055 x + 0))))))))))))

def numericRow5 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 2723, 24), (Sum.inr 2726, 6), (Sum.inr 2743, 12), (Sum.inr 3958, 24), (Sum.inr 3963, 6)]

theorem reindexCheck5 : Integer.Sparse.reindex keyMap MixedData.row5 = numericRow5 := by decide +kernel

theorem numericCheck5 (x : Master → ℝ) : Integer.Sparse.eval numericRow5 x =
    (6 : ℝ) * reducedSource5 x := by
  norm_num [numericRow5, reducedSource5, Integer.Sparse.eval, Sparse.eval, nodeValue2723, nodeValue2726, nodeValue2743, nodeValue2767, nodeValue3958, nodeValue3963, nodeValue3971, nodeValue3981, nodeValue4000, nodeValue4013, nodeValue4015, nodeValue4018, nodeValue4055]
  ring

noncomputable def reducedSource6 (x : Master → ℝ) : ℝ :=
  (-1 : ℝ) * Sparse.eval nodeValue7 x + ((1 : ℝ) * Sparse.eval nodeValue378 x + ((1 : ℝ) * Sparse.eval nodeValue514 x + ((1 : ℝ) * Sparse.eval nodeValue518 x + ((1 : ℝ) * Sparse.eval nodeValue521 x + ((1 : ℝ) * Sparse.eval nodeValue526 x + ((1 : ℝ) * Sparse.eval nodeValue527 x + 0))))))

def numericRow6 : Integer.Sparse Master := [(Sum.inl 0, 26), (Sum.inl 2, 20), (Sum.inl 3, 320), (Sum.inl 4, 320), (Sum.inl 1, 10), (Sum.inl 31, -480)]

theorem reindexCheck6 : Integer.Sparse.reindex keyMap MixedData.row6 = numericRow6 := by decide +kernel

theorem numericCheck6 (x : Master → ℝ) : Integer.Sparse.eval numericRow6 x =
    (1728 : ℝ) * reducedSource6 x := by
  norm_num [numericRow6, reducedSource6, Integer.Sparse.eval, Sparse.eval, nodeValue7, nodeValue378, nodeValue514, nodeValue518, nodeValue521, nodeValue526, nodeValue527]
  ring

noncomputable def reducedSource7 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((4 : ℝ) * Sparse.eval nodeValue5443 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5488 x + ((4 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5496 x + 0))))))))

def numericRow7 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 1, 20), (Sum.inr 3885, -180), (Sum.inr 3886, -45), (Sum.inr 3902, -180), (Sum.inr 3907, -90)]

theorem reindexCheck7 : Integer.Sparse.reindex keyMap MixedData.row7 = numericRow7 := by decide +kernel

theorem numericCheck7 (x : Master → ℝ) : Integer.Sparse.eval numericRow7 x =
    (90 : ℝ) * reducedSource7 x := by
  norm_num [numericRow7, reducedSource7, Integer.Sparse.eval, Sparse.eval, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5448, nodeValue5449, nodeValue5455, nodeValue5488, nodeValue5491, nodeValue5496]
  ring

noncomputable def reducedSource8 (x : Master → ℝ) : ℝ :=
  (-1 : ℝ) * Sparse.eval nodeValue6 x + ((2 : ℝ) * Sparse.eval nodeValue494 x + ((1 : ℝ) * Sparse.eval nodeValue500 x + ((1 : ℝ) * Sparse.eval nodeValue524 x + ((2 : ℝ) * Sparse.eval nodeValue527 x + 0))))

def numericRow8 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 25, -120), (Sum.inl 1, 120)]

theorem reindexCheck8 : Integer.Sparse.reindex keyMap MixedData.row8 = numericRow8 := by decide +kernel

theorem numericCheck8 (x : Master → ℝ) : Integer.Sparse.eval numericRow8 x =
    (432 : ℝ) * reducedSource8 x := by
  norm_num [numericRow8, reducedSource8, Integer.Sparse.eval, Sparse.eval, nodeValue6, nodeValue494, nodeValue500, nodeValue524, nodeValue527]
  ring

noncomputable def reducedSource9 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5434 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((3 : ℝ) * Sparse.eval nodeValue5451 x + ((3 : ℝ) * Sparse.eval nodeValue5454 x + ((3 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0))))))))))))

def numericRow9 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3627, -36), (Sum.inr 3632, -36), (Sum.inr 3633, -12), (Sum.inr 3634, -12), (Sum.inr 3903, -72), (Sum.inr 3913, -36)]

theorem reindexCheck9 : Integer.Sparse.reindex keyMap MixedData.row9 = numericRow9 := by decide +kernel

theorem numericCheck9 (x : Master → ℝ) : Integer.Sparse.eval numericRow9 x =
    (48 : ℝ) * reducedSource9 x := by
  norm_num [numericRow9, reducedSource9, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue5293, nodeValue5294, nodeValue5296, nodeValue5309, nodeValue5310, nodeValue5434, nodeValue5442, nodeValue5451, nodeValue5454, nodeValue5492, nodeValue5494, nodeValue5495]
  ring

noncomputable def reducedSource10 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5441 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((3 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + ((3 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5496 x + 0)))))))))))

def numericRow10 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3623, -30), (Sum.inr 3633, -10), (Sum.inr 3902, -60), (Sum.inr 3907, -30)]

theorem reindexCheck10 : Integer.Sparse.reindex keyMap MixedData.row10 = numericRow10 := by decide +kernel

theorem numericCheck10 (x : Master → ℝ) : Integer.Sparse.eval numericRow10 x =
    (40 : ℝ) * reducedSource10 x := by
  norm_num [numericRow10, reducedSource10, Integer.Sparse.eval, Sparse.eval, nodeValue4094, nodeValue5306, nodeValue5308, nodeValue5310, nodeValue5439, nodeValue5441, nodeValue5443, nodeValue5453, nodeValue5455, nodeValue5456, nodeValue5491, nodeValue5496]
  ring

noncomputable def reducedSource11 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((12 : ℝ) * Sparse.eval nodeValue4092 x + ((8 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4097 x + 0))))

def numericRow11 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 4084, 24), (Sum.inr 4085, 3), (Sum.inr 4092, 36)]

theorem reindexCheck11 : Integer.Sparse.reindex keyMap MixedData.row11 = numericRow11 := by decide +kernel

theorem numericCheck11 (x : Master → ℝ) : Integer.Sparse.eval numericRow11 x =
    (3 : ℝ) * reducedSource11 x := by
  norm_num [numericRow11, reducedSource11, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4085, nodeValue4092, nodeValue4093, nodeValue4097]
  ring

noncomputable def reducedSource12 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((4 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((2 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5454 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + 0)))))))))))))

def numericRow12 : Integer.Sparse Master := [(Sum.inl 0, 379), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, -240), (Sum.inl 4, 160), (Sum.inl 1, -140), (Sum.inr 3077, -4320), (Sum.inr 3622, -4320), (Sum.inr 3625, -4320), (Sum.inr 3801, -4320), (Sum.inr 3809, -8640), (Sum.inr 3812, -4320), (Sum.inr 3813, -8640), (Sum.inr 3901, -4320), (Sum.inr 3909, -4320), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320), (Sum.inr 4025, -4320)]

theorem reindexCheck12 : Integer.Sparse.reindex keyMap MixedData.row12 = numericRow12 := by decide +kernel

theorem numericCheck12 (x : Master → ℝ) : Integer.Sparse.eval numericRow12 x =
    (8640 : ℝ) * reducedSource12 x := by
  norm_num [numericRow12, reducedSource12, Integer.Sparse.eval, Sparse.eval, nodeValue5283, nodeValue5284, nodeValue5292, nodeValue5406, nodeValue5411, nodeValue5433, nodeValue5447, nodeValue5450, nodeValue5452, nodeValue5453, nodeValue5454, nodeValue5485, nodeValue5489, nodeValue5493]
  ring

noncomputable def reducedSource13 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3801 x + ((4 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4010 x + ((2 : ℝ) * Sparse.eval nodeValue4016 x + ((2 : ℝ) * Sparse.eval nodeValue4025 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((2 : ℝ) * Sparse.eval nodeValue4033 x + ((2 : ℝ) * Sparse.eval nodeValue4039 x + ((4 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))

def numericRow13 : Integer.Sparse Master := [(Sum.inl 0, -55), (Sum.inl 12, 40), (Sum.inl 1, 15), (Sum.inr 3077, 1080), (Sum.inr 3801, 1080), (Sum.inr 3809, 2160), (Sum.inr 4010, 1080), (Sum.inr 4025, 1080)]

theorem reindexCheck13 : Integer.Sparse.reindex keyMap MixedData.row13 = numericRow13 := by decide +kernel

theorem numericCheck13 (x : Master → ℝ) : Integer.Sparse.eval numericRow13 x =
    (540 : ℝ) * reducedSource13 x := by
  norm_num [numericRow13, reducedSource13, Integer.Sparse.eval, Sparse.eval, nodeValue3076, nodeValue3077, nodeValue3100, nodeValue3801, nodeValue3809, nodeValue3912, nodeValue4009, nodeValue4010, nodeValue4016, nodeValue4025, nodeValue4029, nodeValue4033, nodeValue4039, nodeValue4040]
  ring

noncomputable def reducedSource14 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4887 x + ((4 : ℝ) * Sparse.eval nodeValue4888 x + ((4 : ℝ) * Sparse.eval nodeValue5405 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((8 : ℝ) * Sparse.eval nodeValue5434 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))

def numericRow14 : Integer.Sparse Master := [(Sum.inl 0, 79), (Sum.inl 12, -40), (Sum.inl 1, 105), (Sum.inr 2243, -720), (Sum.inr 2244, -1440), (Sum.inr 2262, -1440), (Sum.inr 3800, -1440), (Sum.inr 3805, -1440), (Sum.inr 3901, -1440), (Sum.inr 3902, -1440), (Sum.inr 3903, -2880)]

theorem reindexCheck14 : Integer.Sparse.reindex keyMap MixedData.row14 = numericRow14 := by decide +kernel

theorem numericCheck14 (x : Master → ℝ) : Integer.Sparse.eval numericRow14 x =
    (1440 : ℝ) * reducedSource14 x := by
  norm_num [numericRow14, reducedSource14, Integer.Sparse.eval, Sparse.eval, nodeValue4887, nodeValue4888, nodeValue5405, nodeValue5433, nodeValue5434, nodeValue5439, nodeValue5498, nodeValue5499]
  ring

noncomputable def reducedSource15 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))))))

def numericRow15 : Integer.Sparse Master := [(Sum.inl 0, 469), (Sum.inl 4, 560), (Sum.inl 1, -525), (Sum.inr 2764, -4320), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3581, -4320), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3632, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3907, -2160), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320), (Sum.inr 3983, -8640), (Sum.inr 4010, -4320)]

theorem reindexCheck15 : Integer.Sparse.reindex keyMap MixedData.row15 = numericRow15 := by decide +kernel

theorem numericCheck15 (x : Master → ℝ) : Integer.Sparse.eval numericRow15 x =
    (8640 : ℝ) * reducedSource15 x := by
  norm_num [numericRow15, reducedSource15, Integer.Sparse.eval, Sparse.eval, nodeValue5290, nodeValue5291, nodeValue5294, nodeValue5304, nodeValue5434, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5454, nodeValue5455, nodeValue5481, nodeValue5484, nodeValue5485, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5494, nodeValue5495]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
