import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource432 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2857 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2985 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow432 : Integer.Sparse Master := [(Sum.inr 2857, 1), (Sum.inr 2981, 1), (Sum.inr 2985, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem reindexCheck432 : Integer.Sparse.reindex keyMap MixedData.row432 = numericRow432 := by decide +kernel

theorem numericCheck432 (x : Master → ℝ) : Integer.Sparse.eval numericRow432 x =
    (1 : ℝ) * reducedSource432 x := by
  norm_num [numericRow432, reducedSource432, Integer.Sparse.eval, Sparse.eval, nodeValue2857, nodeValue2981, nodeValue2985, nodeValue3078, nodeValue3953, nodeValue4091]

noncomputable def reducedSource433 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2985 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow433 : Integer.Sparse Master := [(Sum.inr 1407, 1), (Sum.inr 2955, 1), (Sum.inr 2985, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem reindexCheck433 : Integer.Sparse.reindex keyMap MixedData.row433 = numericRow433 := by decide +kernel

theorem numericCheck433 (x : Master → ℝ) : Integer.Sparse.eval numericRow433 x =
    (1 : ℝ) * reducedSource433 x := by
  norm_num [numericRow433, reducedSource433, Integer.Sparse.eval, Sparse.eval, nodeValue1407, nodeValue2955, nodeValue2985, nodeValue3078, nodeValue3092, nodeValue3097, nodeValue4091]

noncomputable def reducedSource434 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow434 : Integer.Sparse Master := [(Sum.inr 2865, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 2955, 1), (Sum.inr 3078, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem reindexCheck434 : Integer.Sparse.reindex keyMap MixedData.row434 = numericRow434 := by decide +kernel

theorem numericCheck434 (x : Master → ℝ) : Integer.Sparse.eval numericRow434 x =
    (1 : ℝ) * reducedSource434 x := by
  norm_num [numericRow434, reducedSource434, Integer.Sparse.eval, Sparse.eval, nodeValue2865, nodeValue2925, nodeValue2931, nodeValue2955, nodeValue3078, nodeValue3958, nodeValue4091]

noncomputable def reducedSource435 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow435 : Integer.Sparse Master := [(Sum.inr 1391, 1), (Sum.inr 2931, 2), (Sum.inr 2981, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem reindexCheck435 : Integer.Sparse.reindex keyMap MixedData.row435 = numericRow435 := by decide +kernel

theorem numericCheck435 (x : Master → ℝ) : Integer.Sparse.eval numericRow435 x =
    (1 : ℝ) * reducedSource435 x := by
  norm_num [numericRow435, reducedSource435, Integer.Sparse.eval, Sparse.eval, nodeValue1391, nodeValue2931, nodeValue2981, nodeValue3077, nodeValue3078, nodeValue4091]

noncomputable def reducedSource436 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow436 : Integer.Sparse Master := [(Sum.inr 3031, 1), (Sum.inr 3068, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem reindexCheck436 : Integer.Sparse.reindex keyMap MixedData.row436 = numericRow436 := by decide +kernel

theorem numericCheck436 (x : Master → ℝ) : Integer.Sparse.eval numericRow436 x =
    (1 : ℝ) * reducedSource436 x := by
  norm_num [numericRow436, reducedSource436, Integer.Sparse.eval, Sparse.eval, nodeValue3031, nodeValue3068, nodeValue3078, nodeValue3092, nodeValue3885, nodeValue4091]

noncomputable def reducedSource437 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1389 x + ((1 : ℝ) * Sparse.eval nodeValue2857 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow437 : Integer.Sparse Master := [(Sum.inr 1389, 1), (Sum.inr 2857, 1), (Sum.inr 2865, 2), (Sum.inr 3031, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem reindexCheck437 : Integer.Sparse.reindex keyMap MixedData.row437 = numericRow437 := by decide +kernel

theorem numericCheck437 (x : Master → ℝ) : Integer.Sparse.eval numericRow437 x =
    (1 : ℝ) * reducedSource437 x := by
  norm_num [numericRow437, reducedSource437, Integer.Sparse.eval, Sparse.eval, nodeValue1389, nodeValue2857, nodeValue2865, nodeValue3031, nodeValue3078, nodeValue4091]

noncomputable def reducedSource438 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2628 x + ((2 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3106 x + ((2 : ℝ) * Sparse.eval nodeValue3110 x + 0))))))))))))))))))))

def numericRow438 : Integer.Sparse Master := [(Sum.inl 0, -456), (Sum.inl 2, 590), (Sum.inl 3, 160), (Sum.inl 13, -160), (Sum.inl 55, 480), (Sum.inl 12, -160), (Sum.inl 27, 120), (Sum.inl 1, 710), (Sum.inr 2232, 8640), (Sum.inr 2242, 8640), (Sum.inr 2244, 8640), (Sum.inr 2251, 17280), (Sum.inr 2628, 8640), (Sum.inr 2629, 17280), (Sum.inr 2641, 8640), (Sum.inr 2708, 8640), (Sum.inr 2713, 17280), (Sum.inr 2745, 8640), (Sum.inr 2748, 8640), (Sum.inr 2751, 17280), (Sum.inr 2758, 17280), (Sum.inr 2765, 17280), (Sum.inr 2774, 17280)]

theorem reindexCheck438 : Integer.Sparse.reindex keyMap MixedData.row438 = numericRow438 := by decide +kernel

theorem numericCheck438 (x : Master → ℝ) : Integer.Sparse.eval numericRow438 x =
    (8640 : ℝ) * reducedSource438 x := by
  norm_num [numericRow438, reducedSource438, Integer.Sparse.eval, Sparse.eval, nodeValue2232, nodeValue2242, nodeValue2244, nodeValue2251, nodeValue2628, nodeValue2629, nodeValue2641, nodeValue2708, nodeValue2709, nodeValue2713, nodeValue2745, nodeValue2748, nodeValue2751, nodeValue2753, nodeValue2758, nodeValue2765, nodeValue2767, nodeValue2774, nodeValue3080, nodeValue3106, nodeValue3110]
  ring

noncomputable def reducedSource439 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((2 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow439 : Integer.Sparse Master := [(Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 3548, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem reindexCheck439 : Integer.Sparse.reindex keyMap MixedData.row439 = numericRow439 := by decide +kernel

theorem numericCheck439 (x : Master → ℝ) : Integer.Sparse.eval numericRow439 x =
    (1 : ℝ) * reducedSource439 x := by
  norm_num [numericRow439, reducedSource439, Integer.Sparse.eval, Sparse.eval, nodeValue2879, nodeValue3494, nodeValue3498, nodeValue3548, nodeValue3580, nodeValue4084]

noncomputable def reducedSource440 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((2 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow440 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 2), (Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem reindexCheck440 : Integer.Sparse.reindex keyMap MixedData.row440 = numericRow440 := by decide +kernel

theorem numericCheck440 (x : Master → ℝ) : Integer.Sparse.eval numericRow440 x =
    (1 : ℝ) * reducedSource440 x := by
  norm_num [numericRow440, reducedSource440, Integer.Sparse.eval, Sparse.eval, nodeValue2104, nodeValue2106, nodeValue2108, nodeValue2262, nodeValue3580, nodeValue4084]

noncomputable def reducedSource441 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2877 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((3 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow441 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2877, 1), (Sum.inr 3576, 1), (Sum.inr 3580, 3), (Sum.inr 4084, -1)]

theorem reindexCheck441 : Integer.Sparse.reindex keyMap MixedData.row441 = numericRow441 := by decide +kernel

theorem numericCheck441 (x : Master → ℝ) : Integer.Sparse.eval numericRow441 x =
    (1 : ℝ) * reducedSource441 x := by
  norm_num [numericRow441, reducedSource441, Integer.Sparse.eval, Sparse.eval, nodeValue2104, nodeValue2877, nodeValue3576, nodeValue3580, nodeValue4084]

noncomputable def reducedSource442 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2877 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((2 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow442 : Integer.Sparse Master := [(Sum.inr 2877, 1), (Sum.inr 2879, 1), (Sum.inr 2883, 2), (Sum.inr 3050, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem reindexCheck442 : Integer.Sparse.reindex keyMap MixedData.row442 = numericRow442 := by decide +kernel

theorem numericCheck442 (x : Master → ℝ) : Integer.Sparse.eval numericRow442 x =
    (1 : ℝ) * reducedSource442 x := by
  norm_num [numericRow442, reducedSource442, Integer.Sparse.eval, Sparse.eval, nodeValue2877, nodeValue2879, nodeValue2883, nodeValue3050, nodeValue3580, nodeValue4084]

noncomputable def reducedSource443 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow443 : Integer.Sparse Master := [(Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 3502, 1), (Sum.inr 3580, 1), (Sum.inr 3582, 2), (Sum.inr 4084, -1)]

theorem reindexCheck443 : Integer.Sparse.reindex keyMap MixedData.row443 = numericRow443 := by decide +kernel

theorem numericCheck443 (x : Master → ℝ) : Integer.Sparse.eval numericRow443 x =
    (1 : ℝ) * reducedSource443 x := by
  norm_num [numericRow443, reducedSource443, Integer.Sparse.eval, Sparse.eval, nodeValue2106, nodeValue3050, nodeValue3502, nodeValue3580, nodeValue3582, nodeValue4084]

noncomputable def reducedSource444 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5142 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5193 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))))))))))))))

def numericRow444 : Integer.Sparse Master := [(Sum.inl 0, 195), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -130), (Sum.inr 1200, -2160), (Sum.inr 1202, -2160), (Sum.inr 1205, -2160), (Sum.inr 1236, -4320), (Sum.inr 1898, -2160), (Sum.inr 1915, -4320), (Sum.inr 1940, -2160), (Sum.inr 1942, -2160), (Sum.inr 1946, -4320), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2853, -4320), (Sum.inr 2856, -4320), (Sum.inr 2881, -4320), (Sum.inr 2913, -2160), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3281, -2160), (Sum.inr 3284, -2160), (Sum.inr 3293, -4320), (Sum.inr 3605, -4320), (Sum.inr 3610, -2160), (Sum.inr 3620, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3630, -4320), (Sum.inr 3632, -4320), (Sum.inr 3801, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320)]

theorem reindexCheck444 : Integer.Sparse.reindex keyMap MixedData.row444 = numericRow444 := by decide +kernel

theorem numericCheck444 (x : Master → ℝ) : Integer.Sparse.eval numericRow444 x =
    (8640 : ℝ) * reducedSource444 x := by
  norm_num [numericRow444, reducedSource444, Integer.Sparse.eval, Sparse.eval, nodeValue4581, nodeValue4583, nodeValue4586, nodeValue4602, nodeValue4729, nodeValue4742, nodeValue4890, nodeValue5142, nodeValue5149, nodeValue5192, nodeValue5193, nodeValue5204, nodeValue5283, nodeValue5284, nodeValue5292, nodeValue5294, nodeValue5406, nodeValue5411, nodeValue5452, nodeValue5453]
  ring

noncomputable def reducedSource445 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((2 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2853 x + ((2 : ℝ) * Sparse.eval nodeValue2856 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2913 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3076 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))))))))))))))

def numericRow445 : Integer.Sparse Master := [(Sum.inl 0, -140), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 115), (Sum.inr 1200, 2160), (Sum.inr 1202, 2160), (Sum.inr 1205, 2160), (Sum.inr 1236, 4320), (Sum.inr 1898, 2160), (Sum.inr 1915, 4320), (Sum.inr 2247, 2160), (Sum.inr 2853, 4320), (Sum.inr 2856, 4320), (Sum.inr 2881, 4320), (Sum.inr 2913, 2160), (Sum.inr 2924, 4320), (Sum.inr 3077, 4320), (Sum.inr 3801, 2160), (Sum.inr 3809, 4320)]

theorem reindexCheck445 : Integer.Sparse.reindex keyMap MixedData.row445 = numericRow445 := by decide +kernel

theorem numericCheck445 (x : Master → ℝ) : Integer.Sparse.eval numericRow445 x =
    (2160 : ℝ) * reducedSource445 x := by
  norm_num [numericRow445, reducedSource445, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue1202, nodeValue1205, nodeValue1236, nodeValue1898, nodeValue1915, nodeValue2247, nodeValue2853, nodeValue2856, nodeValue2881, nodeValue2913, nodeValue2924, nodeValue3076, nodeValue3077, nodeValue3100, nodeValue3101, nodeValue3801, nodeValue3809, nodeValue3912, nodeValue4039]
  ring

noncomputable def reducedSource446 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue5065 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow446 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2485, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 2954, -4320), (Sum.inr 3481, -4320), (Sum.inr 3605, -4320), (Sum.inr 3606, -4320), (Sum.inr 3612, -4320), (Sum.inr 3800, -2160), (Sum.inr 3805, -2160), (Sum.inr 3902, -2160), (Sum.inr 4010, -2160), (Sum.inr 4439, 8640), (Sum.inr 4440, 8640), (Sum.inr 4444, 8640), (Sum.inr 4459, 17280), (Sum.inr 5065, 8640), (Sum.inr 5067, 8640), (Sum.inr 5074, 17280), (Sum.inr 5251, 8640), (Sum.inr 5252, 8640), (Sum.inr 5260, 17280), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640), (Sum.inr 5289, 17280)]

theorem reindexCheck446 : Integer.Sparse.reindex keyMap MixedData.row446 = numericRow446 := by decide +kernel

theorem numericCheck446 (x : Master → ℝ) : Integer.Sparse.eval numericRow446 x =
    (8640 : ℝ) * reducedSource446 x := by
  norm_num [numericRow446, reducedSource446, Integer.Sparse.eval, Sparse.eval, nodeValue4439, nodeValue4440, nodeValue4444, nodeValue4459, nodeValue5065, nodeValue5067, nodeValue5074, nodeValue5078, nodeValue5149, nodeValue5152, nodeValue5170, nodeValue5251, nodeValue5252, nodeValue5260, nodeValue5281, nodeValue5282, nodeValue5289, nodeValue5405, nodeValue5410, nodeValue5439, nodeValue5485]
  ring

noncomputable def reducedSource447 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2481 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((2 : ℝ) * Sparse.eval nodeValue2572 x + ((2 : ℝ) * Sparse.eval nodeValue2576 x + ((2 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

def numericRow447 : Integer.Sparse Master := [(Sum.inl 0, -78), (Sum.inl 2, 35), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, -235), (Sum.inr 1021, 1440), (Sum.inr 1022, 1440), (Sum.inr 1026, 1440), (Sum.inr 1042, 2880), (Sum.inr 2470, 1440), (Sum.inr 2473, 1440), (Sum.inr 2481, 2880), (Sum.inr 2710, 1440), (Sum.inr 2712, 1440), (Sum.inr 2724, 2880), (Sum.inr 2750, 1440), (Sum.inr 2751, 1440), (Sum.inr 2763, 2880)]

theorem reindexCheck447 : Integer.Sparse.reindex keyMap MixedData.row447 = numericRow447 := by decide +kernel

theorem numericCheck447 (x : Master → ℝ) : Integer.Sparse.eval numericRow447 x =
    (1440 : ℝ) * reducedSource447 x := by
  norm_num [numericRow447, reducedSource447, Integer.Sparse.eval, Sparse.eval, nodeValue1021, nodeValue1022, nodeValue1026, nodeValue1042, nodeValue2470, nodeValue2473, nodeValue2481, nodeValue2570, nodeValue2572, nodeValue2576, nodeValue2596, nodeValue2710, nodeValue2712, nodeValue2724, nodeValue2750, nodeValue2751, nodeValue2763, nodeValue3977, nodeValue3996, nodeValue3998, nodeValue4012]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
