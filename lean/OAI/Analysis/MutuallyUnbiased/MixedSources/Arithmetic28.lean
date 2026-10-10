import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource448 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((2 : ℝ) * Sparse.eval nodeValue3606 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + 0))))))))))))))))))))

def numericRow448 : Integer.Sparse Master := [(Sum.inl 0, -41), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, -70), (Sum.inr 1713, 2160), (Sum.inr 1714, 4320), (Sum.inr 1723, 2160), (Sum.inr 1736, 2160), (Sum.inr 3463, 4320), (Sum.inr 3466, 2160), (Sum.inr 3476, 2160), (Sum.inr 3481, 4320), (Sum.inr 3539, 2160), (Sum.inr 3540, 4320), (Sum.inr 3543, 2160), (Sum.inr 3571, 2160), (Sum.inr 3572, 4320), (Sum.inr 3580, 2160), (Sum.inr 3605, 4320), (Sum.inr 3606, 4320), (Sum.inr 3612, 4320), (Sum.inr 3805, 2160)]

theorem reindexCheck448 : Integer.Sparse.reindex keyMap MixedData.row448 = numericRow448 := by decide +kernel

theorem numericCheck448 (x : Master → ℝ) : Integer.Sparse.eval numericRow448 x =
    (2160 : ℝ) * reducedSource448 x := by
  norm_num [numericRow448, reducedSource448, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue1714, nodeValue1723, nodeValue1736, nodeValue3463, nodeValue3466, nodeValue3476, nodeValue3481, nodeValue3539, nodeValue3540, nodeValue3543, nodeValue3571, nodeValue3572, nodeValue3580, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3805, nodeValue3816, nodeValue3858, nodeValue3984]
  ring

noncomputable def reducedSource449 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow449 : Integer.Sparse Master := [(Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 3902, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem reindexCheck449 : Integer.Sparse.reindex keyMap MixedData.row449 = numericRow449 := by decide +kernel

theorem numericCheck449 (x : Master → ℝ) : Integer.Sparse.eval numericRow449 x =
    (1 : ℝ) * reducedSource449 x := by
  norm_num [numericRow449, reducedSource449, Integer.Sparse.eval, Sparse.eval, nodeValue3077, nodeValue3800, nodeValue3808, nodeValue3902, nodeValue4010, nodeValue4091]

noncomputable def reducedSource450 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow450 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1406, 2), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem reindexCheck450 : Integer.Sparse.reindex keyMap MixedData.row450 = numericRow450 := by decide +kernel

theorem numericCheck450 (x : Master → ℝ) : Integer.Sparse.eval numericRow450 x =
    (1 : ℝ) * reducedSource450 x := by
  norm_num [numericRow450, reducedSource450, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue1388, nodeValue1391, nodeValue1406, nodeValue3077, nodeValue4091]

noncomputable def reducedSource451 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow451 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2981, 1), (Sum.inr 2984, 2), (Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

theorem reindexCheck451 : Integer.Sparse.reindex keyMap MixedData.row451 = numericRow451 := by decide +kernel

theorem numericCheck451 (x : Master → ℝ) : Integer.Sparse.eval numericRow451 x =
    (1 : ℝ) * reducedSource451 x := by
  norm_num [numericRow451, reducedSource451, Integer.Sparse.eval, Sparse.eval, nodeValue2470, nodeValue2981, nodeValue2984, nodeValue3077, nodeValue3800, nodeValue4091]

noncomputable def reducedSource452 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue5097 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

def numericRow452 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2244, -1080), (Sum.inr 2245, -1080), (Sum.inr 2262, -1080), (Sum.inr 2277, -1080), (Sum.inr 2509, -1080), (Sum.inr 2694, -1080), (Sum.inr 2704, -1080), (Sum.inr 2705, -1080), (Sum.inr 3054, -2160), (Sum.inr 3077, -2160), (Sum.inr 3493, -1080), (Sum.inr 3498, -1080), (Sum.inr 3625, -2160), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4885, 4320), (Sum.inr 4891, 8640), (Sum.inr 5097, 4320), (Sum.inr 5103, 8640), (Sum.inr 5251, 4320), (Sum.inr 5254, 8640), (Sum.inr 5270, 4320), (Sum.inr 5277, 4320), (Sum.inr 5282, 4320), (Sum.inr 5287, 8640)]

theorem reindexCheck452 : Integer.Sparse.reindex keyMap MixedData.row452 = numericRow452 := by decide +kernel

theorem numericCheck452 (x : Master → ℝ) : Integer.Sparse.eval numericRow452 x =
    (4320 : ℝ) * reducedSource452 x := by
  norm_num [numericRow452, reducedSource452, Integer.Sparse.eval, Sparse.eval, nodeValue4885, nodeValue4888, nodeValue4889, nodeValue4891, nodeValue5097, nodeValue5099, nodeValue5103, nodeValue5241, nodeValue5248, nodeValue5250, nodeValue5251, nodeValue5254, nodeValue5270, nodeValue5274, nodeValue5277, nodeValue5282, nodeValue5284, nodeValue5287, nodeValue5293, nodeValue5294, nodeValue5302]
  ring

noncomputable def reducedSource453 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2746 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((2 : ℝ) * Sparse.eval nodeValue2759 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3003 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3106 x + ((2 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

def numericRow453 : Integer.Sparse Master := [(Sum.inl 0, -126), (Sum.inl 2, 155), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, 125), (Sum.inr 2233, 1440), (Sum.inr 2244, 1440), (Sum.inr 2245, 1440), (Sum.inr 2253, 2880), (Sum.inr 2710, 1440), (Sum.inr 2714, 2880), (Sum.inr 2745, 1440), (Sum.inr 2746, 1440), (Sum.inr 2751, 1440), (Sum.inr 2754, 1440), (Sum.inr 2758, 2880), (Sum.inr 2759, 2880)]

theorem reindexCheck453 : Integer.Sparse.reindex keyMap MixedData.row453 = numericRow453 := by decide +kernel

theorem numericCheck453 (x : Master → ℝ) : Integer.Sparse.eval numericRow453 x =
    (1440 : ℝ) * reducedSource453 x := by
  norm_num [numericRow453, reducedSource453, Integer.Sparse.eval, Sparse.eval, nodeValue2233, nodeValue2244, nodeValue2245, nodeValue2253, nodeValue2709, nodeValue2710, nodeValue2714, nodeValue2745, nodeValue2746, nodeValue2751, nodeValue2753, nodeValue2754, nodeValue2758, nodeValue2759, nodeValue2767, nodeValue2768, nodeValue2776, nodeValue3003, nodeValue3081, nodeValue3106, nodeValue3112]
  ring

noncomputable def reducedSource454 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((2 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((2 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

def numericRow454 : Integer.Sparse Master := [(Sum.inl 0, -231), (Sum.inl 2, 235), (Sum.inl 3, 80), (Sum.inl 13, -320), (Sum.inl 12, -80), (Sum.inl 1, 310), (Sum.inr 2694, 4320), (Sum.inr 2704, 4320), (Sum.inr 2705, 4320), (Sum.inr 3016, 8640), (Sum.inr 3024, 8640), (Sum.inr 3025, 8640), (Sum.inr 3054, 8640), (Sum.inr 3058, 4320), (Sum.inr 3059, 4320), (Sum.inr 3064, 4320), (Sum.inr 3075, 4320), (Sum.inr 3077, 8640), (Sum.inr 3078, 4320), (Sum.inr 3221, 4320), (Sum.inr 3222, 8640)]

theorem reindexCheck454 : Integer.Sparse.reindex keyMap MixedData.row454 = numericRow454 := by decide +kernel

theorem numericCheck454 (x : Master → ℝ) : Integer.Sparse.eval numericRow454 x =
    (4320 : ℝ) * reducedSource454 x := by
  norm_num [numericRow454, reducedSource454, Integer.Sparse.eval, Sparse.eval, nodeValue2694, nodeValue2704, nodeValue2705, nodeValue2742, nodeValue3016, nodeValue3024, nodeValue3025, nodeValue3054, nodeValue3058, nodeValue3059, nodeValue3064, nodeValue3065, nodeValue3075, nodeValue3077, nodeValue3078, nodeValue3101, nodeValue3102, nodeValue3221, nodeValue3222, nodeValue3223, nodeValue3227]
  ring

noncomputable def reducedSource455 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((2 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow455 : Integer.Sparse Master := [(Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 3498, 1), (Sum.inr 3625, 1), (Sum.inr 4084, -1)]

theorem reindexCheck455 : Integer.Sparse.reindex keyMap MixedData.row455 = numericRow455 := by decide +kernel

theorem numericCheck455 (x : Master → ℝ) : Integer.Sparse.eval numericRow455 x =
    (1 : ℝ) * reducedSource455 x := by
  norm_num [numericRow455, reducedSource455, Integer.Sparse.eval, Sparse.eval, nodeValue2509, nodeValue3493, nodeValue3498, nodeValue3547, nodeValue3625, nodeValue4084]

noncomputable def reducedSource456 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue995 x + ((1 : ℝ) * Sparse.eval nodeValue997 x + ((2 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1078 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((2 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2457 x + ((2 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

def numericRow456 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 2, -5), (Sum.inl 3, -400), (Sum.inl 13, -160), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, -20), (Sum.inr 995, 4320), (Sum.inr 997, 4320), (Sum.inr 1001, 8640), (Sum.inr 1078, 4320), (Sum.inr 2396, 4320), (Sum.inr 2397, 4320), (Sum.inr 2401, 8640), (Sum.inr 2457, 4320), (Sum.inr 2460, 8640), (Sum.inr 2507, 4320), (Sum.inr 2700, 8640), (Sum.inr 2702, 8640), (Sum.inr 2706, 8640), (Sum.inr 2730, 4320), (Sum.inr 2731, 8640), (Sum.inr 2738, 8640), (Sum.inr 3571, 4320), (Sum.inr 3580, 4320), (Sum.inr 3581, 8640)]

theorem reindexCheck456 : Integer.Sparse.reindex keyMap MixedData.row456 = numericRow456 := by decide +kernel

theorem numericCheck456 (x : Master → ℝ) : Integer.Sparse.eval numericRow456 x =
    (4320 : ℝ) * reducedSource456 x := by
  norm_num [numericRow456, reducedSource456, Integer.Sparse.eval, Sparse.eval, nodeValue995, nodeValue997, nodeValue1001, nodeValue1078, nodeValue2396, nodeValue2397, nodeValue2401, nodeValue2457, nodeValue2460, nodeValue2507, nodeValue2700, nodeValue2702, nodeValue2706, nodeValue2730, nodeValue2731, nodeValue2738, nodeValue2775, nodeValue3571, nodeValue3580, nodeValue3581, nodeValue3887]
  ring

noncomputable def reducedSource457 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1250 x + ((1 : ℝ) * Sparse.eval nodeValue1252 x + ((1 : ℝ) * Sparse.eval nodeValue1253 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow457 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 1252, 1), (Sum.inr 1253, 1), (Sum.inr 1270, 2), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem reindexCheck457 : Integer.Sparse.reindex keyMap MixedData.row457 = numericRow457 := by decide +kernel

theorem numericCheck457 (x : Master → ℝ) : Integer.Sparse.eval numericRow457 x =
    (1 : ℝ) * reducedSource457 x := by
  norm_num [numericRow457, reducedSource457, Integer.Sparse.eval, Sparse.eval, nodeValue1250, nodeValue1252, nodeValue1253, nodeValue1270, nodeValue2754, nodeValue4091]

noncomputable def reducedSource458 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1250 x + ((2 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2746 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow458 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 2625, 2), (Sum.inr 2746, 1), (Sum.inr 2750, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem reindexCheck458 : Integer.Sparse.reindex keyMap MixedData.row458 = numericRow458 := by decide +kernel

theorem numericCheck458 (x : Master → ℝ) : Integer.Sparse.eval numericRow458 x =
    (1 : ℝ) * reducedSource458 x := by
  norm_num [numericRow458, reducedSource458, Integer.Sparse.eval, Sparse.eval, nodeValue1250, nodeValue2625, nodeValue2746, nodeValue2750, nodeValue2754, nodeValue4091]

noncomputable def reducedSource459 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1421 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow459 : Integer.Sparse Master := [(Sum.inr 1421, 1), (Sum.inr 2564, 1), (Sum.inr 2573, 2), (Sum.inr 2754, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

theorem reindexCheck459 : Integer.Sparse.reindex keyMap MixedData.row459 = numericRow459 := by decide +kernel

theorem numericCheck459 (x : Master → ℝ) : Integer.Sparse.eval numericRow459 x =
    (1 : ℝ) * reducedSource459 x := by
  norm_num [numericRow459, reducedSource459, Integer.Sparse.eval, Sparse.eval, nodeValue1421, nodeValue2564, nodeValue2573, nodeValue2754, nodeValue3037, nodeValue4091]

noncomputable def reducedSource460 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow460 : Integer.Sparse Master := [(Sum.inr 1270, 1), (Sum.inr 2573, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem reindexCheck460 : Integer.Sparse.reindex keyMap MixedData.row460 = numericRow460 := by decide +kernel

theorem numericCheck460 (x : Master → ℝ) : Integer.Sparse.eval numericRow460 x =
    (1 : ℝ) * reducedSource460 x := by
  norm_num [numericRow460, reducedSource460, Integer.Sparse.eval, Sparse.eval, nodeValue1270, nodeValue2573, nodeValue2641, nodeValue2754, nodeValue2764, nodeValue4091]

noncomputable def reducedSource461 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4441 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4443 x + ((2 : ℝ) * Sparse.eval nodeValue4462 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5066 x + ((2 : ℝ) * Sparse.eval nodeValue5077 x + ((2 : ℝ) * Sparse.eval nodeValue5150 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

def numericRow461 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 2025, -4320), (Sum.inr 2224, -4320), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2739, -4320), (Sum.inr 2764, -2160), (Sum.inr 3534, -4320), (Sum.inr 3581, -2160), (Sum.inr 3623, -2160), (Sum.inr 4441, 8640), (Sum.inr 4442, 8640), (Sum.inr 4443, 8640), (Sum.inr 4462, 17280), (Sum.inr 4792, 8640), (Sum.inr 5066, 8640), (Sum.inr 5077, 17280), (Sum.inr 5150, 17280), (Sum.inr 5151, 17280), (Sum.inr 5173, 17280), (Sum.inr 5270, 8640), (Sum.inr 5278, 8640), (Sum.inr 5279, 8640), (Sum.inr 5288, 17280), (Sum.inr 5295, 17280)]

theorem reindexCheck461 : Integer.Sparse.reindex keyMap MixedData.row461 = numericRow461 := by decide +kernel

theorem numericCheck461 (x : Master → ℝ) : Integer.Sparse.eval numericRow461 x =
    (8640 : ℝ) * reducedSource461 x := by
  norm_num [numericRow461, reducedSource461, Integer.Sparse.eval, Sparse.eval, nodeValue4441, nodeValue4442, nodeValue4443, nodeValue4462, nodeValue4792, nodeValue4807, nodeValue4890, nodeValue5066, nodeValue5077, nodeValue5150, nodeValue5151, nodeValue5173, nodeValue5256, nodeValue5270, nodeValue5271, nodeValue5278, nodeValue5279, nodeValue5288, nodeValue5290, nodeValue5295, nodeValue5306]
  ring

noncomputable def reducedSource462 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1023 x + ((1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1025 x + ((2 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2472 x + ((2 : ℝ) * Sparse.eval nodeValue2484 x + ((2 : ℝ) * Sparse.eval nodeValue2573 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((2 : ℝ) * Sparse.eval nodeValue2575 x + ((2 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

def numericRow462 : Integer.Sparse Master := [(Sum.inl 0, -376), (Sum.inl 5, 80), (Sum.inl 6, -60), (Sum.inl 2, -500), (Sum.inl 35, -320), (Sum.inl 3, -640), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 26, -320), (Sum.inl 4, -320), (Sum.inl 1, -480), (Sum.inr 1023, 8640), (Sum.inr 1024, 8640), (Sum.inr 1025, 8640), (Sum.inr 1045, 17280), (Sum.inr 2471, 8640), (Sum.inr 2472, 8640), (Sum.inr 2484, 17280), (Sum.inr 2573, 17280), (Sum.inr 2575, 17280), (Sum.inr 2600, 17280), (Sum.inr 2747, 8640), (Sum.inr 2748, 8640), (Sum.inr 2754, 8640), (Sum.inr 2760, 17280), (Sum.inr 2764, 8640), (Sum.inr 2769, 17280)]

theorem reindexCheck462 : Integer.Sparse.reindex keyMap MixedData.row462 = numericRow462 := by decide +kernel

theorem numericCheck462 (x : Master → ℝ) : Integer.Sparse.eval numericRow462 x =
    (8640 : ℝ) * reducedSource462 x := by
  norm_num [numericRow462, reducedSource462, Integer.Sparse.eval, Sparse.eval, nodeValue1023, nodeValue1024, nodeValue1025, nodeValue1045, nodeValue2471, nodeValue2472, nodeValue2484, nodeValue2573, nodeValue2574, nodeValue2575, nodeValue2600, nodeValue2747, nodeValue2748, nodeValue2754, nodeValue2755, nodeValue2760, nodeValue2764, nodeValue2769, nodeValue3085, nodeValue3109, nodeValue3120]
  ring

noncomputable def reducedSource463 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1654 x + ((1 : ℝ) * Sparse.eval nodeValue1655 x + ((2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((2 : ℝ) * Sparse.eval nodeValue2700 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + 0))))))))))))))))))))

def numericRow463 : Integer.Sparse Master := [(Sum.inl 0, -59), (Sum.inl 2, -35), (Sum.inl 3, -80), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -220), (Sum.inr 1654, 4320), (Sum.inr 1655, 4320), (Sum.inr 1656, 8640), (Sum.inr 1744, 4320), (Sum.inr 2201, 4320), (Sum.inr 2224, 8640), (Sum.inr 2290, 4320), (Sum.inr 2668, 4320), (Sum.inr 2681, 8640), (Sum.inr 2700, 8640), (Sum.inr 2717, 8640), (Sum.inr 2735, 8640), (Sum.inr 2738, 4320), (Sum.inr 2739, 8640), (Sum.inr 2781, 8640), (Sum.inr 3050, 4320), (Sum.inr 3073, 4320), (Sum.inr 3096, 8640)]

theorem reindexCheck463 : Integer.Sparse.reindex keyMap MixedData.row463 = numericRow463 := by decide +kernel

theorem numericCheck463 (x : Master → ℝ) : Integer.Sparse.eval numericRow463 x =
    (4320 : ℝ) * reducedSource463 x := by
  norm_num [numericRow463, reducedSource463, Integer.Sparse.eval, Sparse.eval, nodeValue1654, nodeValue1655, nodeValue1656, nodeValue1744, nodeValue2201, nodeValue2224, nodeValue2290, nodeValue2668, nodeValue2681, nodeValue2700, nodeValue2717, nodeValue2720, nodeValue2735, nodeValue2738, nodeValue2739, nodeValue2781, nodeValue2784, nodeValue3050, nodeValue3073, nodeValue3096, nodeValue3099]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
