import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
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

noncomputable def reducedSource352 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2603 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow352 : Integer.Sparse Master := [(Sum.inr 1310, 1), (Sum.inr 2603, 3), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem reindexCheck352 : Integer.Sparse.reindex keyMap MixedData.row352 = numericRow352 := by decide +kernel

theorem numericCheck352 (x : Master → ℝ) : Integer.Sparse.eval numericRow352 x =
    (1 : ℝ) * reducedSource352 x := by
  norm_num [numericRow352, reducedSource352, Integer.Sparse.eval, Sparse.eval, nodeValue1310, nodeValue2603, nodeValue2783, nodeValue2789, nodeValue4084]

noncomputable def reducedSource353 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))))))))))

def numericRow353 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 1240, -180), (Sum.inr 1242, -90), (Sum.inr 1246, -90), (Sum.inr 2485, -180), (Sum.inr 2519, -90), (Sum.inr 2884, -180), (Sum.inr 2889, -90), (Sum.inr 2931, -180), (Sum.inr 3299, -180), (Sum.inr 3300, -90), (Sum.inr 3301, -90), (Sum.inr 3309, -90), (Sum.inr 3481, -180), (Sum.inr 3486, -90), (Sum.inr 3607, -180), (Sum.inr 3612, -180), (Sum.inr 3621, -180), (Sum.inr 3622, -180), (Sum.inr 3627, -180), (Sum.inr 3631, -90), (Sum.inr 3632, -90), (Sum.inr 3634, -90), (Sum.inr 3903, -180), (Sum.inr 3913, -90)]

theorem reindexCheck353 : Integer.Sparse.reindex keyMap MixedData.row353 = numericRow353 := by decide +kernel

theorem numericCheck353 (x : Master → ℝ) : Integer.Sparse.eval numericRow353 x =
    (360 : ℝ) * reducedSource353 x := by
  norm_num [numericRow353, reducedSource353, Integer.Sparse.eval, Sparse.eval, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4624, nodeValue5078, nodeValue5109, nodeValue5148, nodeValue5152, nodeValue5169, nodeValue5203, nodeValue5207, nodeValue5292, nodeValue5293, nodeValue5294, nodeValue5296, nodeValue5307, nodeValue5309, nodeValue5434, nodeValue5451, nodeValue5454, nodeValue5455]; ring

noncomputable def reducedSource354 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2927 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

def numericRow354 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 2, -5), (Sum.inl 1, 10), (Sum.inr 1240, 180), (Sum.inr 1242, 90), (Sum.inr 1246, 90), (Sum.inr 2485, 180), (Sum.inr 2519, 90), (Sum.inr 2884, 180), (Sum.inr 2889, 90), (Sum.inr 2931, 180)]

theorem reindexCheck354 : Integer.Sparse.reindex keyMap MixedData.row354 = numericRow354 := by decide +kernel

theorem numericCheck354 (x : Master → ℝ) : Integer.Sparse.eval numericRow354 x =
    (90 : ℝ) * reducedSource354 x := by
  norm_num [numericRow354, reducedSource354, Integer.Sparse.eval, Sparse.eval, nodeValue1240, nodeValue1242, nodeValue1246, nodeValue1301, nodeValue2485, nodeValue2519, nodeValue2770, nodeValue2884, nodeValue2889, nodeValue2927, nodeValue2931, nodeValue2960, nodeValue3100, nodeValue3101, nodeValue3102, nodeValue3122, nodeValue3123, nodeValue3982, nodeValue3987, nodeValue4019, nodeValue4040]; ring

noncomputable def reducedSource355 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

def numericRow355 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, 15), (Sum.inl 1, 50), (Sum.inr 1041, -720), (Sum.inr 1043, -360), (Sum.inr 1050, -360), (Sum.inr 1083, -360), (Sum.inr 1724, -720), (Sum.inr 1725, -360), (Sum.inr 1728, -360), (Sum.inr 1751, -360), (Sum.inr 2480, -720), (Sum.inr 2482, -720), (Sum.inr 2489, -720), (Sum.inr 2512, -720), (Sum.inr 2723, -720), (Sum.inr 2726, -360), (Sum.inr 2743, -360), (Sum.inr 3467, -720), (Sum.inr 3468, -720), (Sum.inr 3471, -720), (Sum.inr 3482, -720), (Sum.inr 3544, -720), (Sum.inr 3545, -360), (Sum.inr 3548, -360), (Sum.inr 3607, -720), (Sum.inr 3608, -360), (Sum.inr 3616, -360), (Sum.inr 3622, -720), (Sum.inr 3623, -360), (Sum.inr 3627, -360), (Sum.inr 4047, -720)]

theorem reindexCheck355 : Integer.Sparse.reindex keyMap MixedData.row355 = numericRow355 := by decide +kernel

theorem numericCheck355 (x : Master → ℝ) : Integer.Sparse.eval numericRow355 x =
    (1440 : ℝ) * reducedSource355 x := by
  norm_num [numericRow355, reducedSource355, Integer.Sparse.eval, Sparse.eval, nodeValue4458, nodeValue4460, nodeValue4467, nodeValue4499, nodeValue5073, nodeValue5075, nodeValue5081, nodeValue5102, nodeValue5169, nodeValue5171, nodeValue5177, nodeValue5259, nodeValue5261, nodeValue5275, nodeValue5292, nodeValue5293, nodeValue5306, nodeValue5483, nodeValue5487, nodeValue5491, nodeValue5493]; ring

noncomputable def reducedSource356 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((2 : ℝ) * Sparse.eval nodeValue2489 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

def numericRow356 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 2, -1), (Sum.inl 1, -2), (Sum.inr 1041, 48), (Sum.inr 1043, 24), (Sum.inr 1050, 24), (Sum.inr 1083, 24), (Sum.inr 2480, 48), (Sum.inr 2482, 48), (Sum.inr 2489, 48), (Sum.inr 2512, 48), (Sum.inr 2723, 48), (Sum.inr 2726, 24), (Sum.inr 2743, 24)]

theorem reindexCheck356 : Integer.Sparse.reindex keyMap MixedData.row356 = numericRow356 := by decide +kernel

theorem numericCheck356 (x : Master → ℝ) : Integer.Sparse.eval numericRow356 x =
    (24 : ℝ) * reducedSource356 x := by
  norm_num [numericRow356, reducedSource356, Integer.Sparse.eval, Sparse.eval, nodeValue1041, nodeValue1043, nodeValue1050, nodeValue1083, nodeValue2480, nodeValue2482, nodeValue2489, nodeValue2512, nodeValue2595, nodeValue2598, nodeValue2605, nodeValue2723, nodeValue2726, nodeValue2743, nodeValue2766, nodeValue2767, nodeValue2784, nodeValue3981, nodeValue4000, nodeValue4014, nodeValue4018]; ring

noncomputable def reducedSource357 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))))))))

def numericRow357 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -85), (Sum.inl 3, -80), (Sum.inl 1, -100), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -8640), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -8640), (Sum.inr 3548, -2160), (Sum.inr 3582, -2160), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -4320), (Sum.inr 3632, -2160), (Sum.inr 5266, 17280), (Sum.inr 5282, 17280), (Sum.inr 5300, 8640)]

theorem reindexCheck357 : Integer.Sparse.reindex keyMap MixedData.row357 = numericRow357 := by decide +kernel

theorem numericCheck357 (x : Master → ℝ) : Integer.Sparse.eval numericRow357 x =
    (8640 : ℝ) * reducedSource357 x := by
  norm_num [numericRow357, reducedSource357, Integer.Sparse.eval, Sparse.eval, nodeValue4888, nodeValue4894, nodeValue4895, nodeValue4896, nodeValue5250, nodeValue5258, nodeValue5259, nodeValue5266, nodeValue5274, nodeValue5275, nodeValue5282, nodeValue5284, nodeValue5291, nodeValue5293, nodeValue5294, nodeValue5300, nodeValue5302, nodeValue5308, nodeValue5309]; ring

noncomputable def reducedSource358 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2709 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0))))))))))))))))))))

def numericRow358 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 2244, 120), (Sum.inr 2278, 60), (Sum.inr 2722, 120), (Sum.inr 2723, 120), (Sum.inr 2731, 120), (Sum.inr 2751, 120), (Sum.inr 2765, 60), (Sum.inr 2774, 60)]

theorem reindexCheck358 : Integer.Sparse.reindex keyMap MixedData.row358 = numericRow358 := by decide +kernel

theorem numericCheck358 (x : Master → ℝ) : Integer.Sparse.eval numericRow358 x =
    (60 : ℝ) * reducedSource358 x := by
  norm_num [numericRow358, reducedSource358, Integer.Sparse.eval, Sparse.eval, nodeValue2244, nodeValue2264, nodeValue2265, nodeValue2278, nodeValue2709, nodeValue2722, nodeValue2723, nodeValue2731, nodeValue2751, nodeValue2753, nodeValue2765, nodeValue2767, nodeValue2768, nodeValue2774, nodeValue2776, nodeValue2786, nodeValue2787, nodeValue3088, nodeValue3110, nodeValue3112, nodeValue3123]; ring

noncomputable def reducedSource359 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3065 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow359 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 2723, 90), (Sum.inr 2743, 45), (Sum.inr 3039, 90), (Sum.inr 3054, 45), (Sum.inr 3055, 45), (Sum.inr 3077, 90), (Sum.inr 3078, 90)]

theorem reindexCheck359 : Integer.Sparse.reindex keyMap MixedData.row359 = numericRow359 := by decide +kernel

theorem numericCheck359 (x : Master → ℝ) : Integer.Sparse.eval numericRow359 x =
    (45 : ℝ) * reducedSource359 x := by
  norm_num [numericRow359, reducedSource359, Integer.Sparse.eval, Sparse.eval, nodeValue2723, nodeValue2742, nodeValue2743, nodeValue2787, nodeValue3039, nodeValue3054, nodeValue3055, nodeValue3065, nodeValue3077, nodeValue3078, nodeValue3088, nodeValue3089, nodeValue3101, nodeValue3102, nodeValue3103, nodeValue3123, nodeValue3124, nodeValue3225, nodeValue3227, nodeValue3229, nodeValue3230]; ring

noncomputable def reducedSource360 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow360 : Integer.Sparse Master := [(Sum.inr 3544, 2), (Sum.inr 3548, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck360 : Integer.Sparse.reindex keyMap MixedData.row360 = numericRow360 := by decide +kernel

theorem numericCheck360 (x : Master → ℝ) : Integer.Sparse.eval numericRow360 x =
    (1 : ℝ) * reducedSource360 x := by
  norm_num [numericRow360, reducedSource360, Integer.Sparse.eval, Sparse.eval, nodeValue3544, nodeValue3547, nodeValue3548, nodeValue3627, nodeValue3635, nodeValue4084]

noncomputable def reducedSource361 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow361 : Integer.Sparse Master := [(Sum.inr 2262, 2), (Sum.inr 2266, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck361 : Integer.Sparse.reindex keyMap MixedData.row361 = numericRow361 := by decide +kernel

theorem numericCheck361 (x : Master → ℝ) : Integer.Sparse.eval numericRow361 x =
    (1 : ℝ) * reducedSource361 x := by
  norm_num [numericRow361, reducedSource361, Integer.Sparse.eval, Sparse.eval, nodeValue2262, nodeValue2264, nodeValue2266, nodeValue2291, nodeValue3627, nodeValue4084]

noncomputable def reducedSource362 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((2 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))

def numericRow362 : Integer.Sparse Master := [(Sum.inr 3627, 3), (Sum.inr 4084, -1)]

theorem reindexCheck362 : Integer.Sparse.reindex keyMap MixedData.row362 = numericRow362 := by decide +kernel

theorem numericCheck362 (x : Master → ℝ) : Integer.Sparse.eval numericRow362 x =
    (1 : ℝ) * reducedSource362 x := by
  norm_num [numericRow362, reducedSource362, Integer.Sparse.eval, Sparse.eval, nodeValue3627, nodeValue3629, nodeValue3635, nodeValue4084]

noncomputable def reducedSource363 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow363 : Integer.Sparse Master := [(Sum.inr 3548, 1), (Sum.inr 3580, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck363 : Integer.Sparse.reindex keyMap MixedData.row363 = numericRow363 := by decide +kernel

theorem numericCheck363 (x : Master → ℝ) : Integer.Sparse.eval numericRow363 x =
    (1 : ℝ) * reducedSource363 x := by
  norm_num [numericRow363, reducedSource363, Integer.Sparse.eval, Sparse.eval, nodeValue3548, nodeValue3580, nodeValue3582, nodeValue3584, nodeValue3627, nodeValue4084]

noncomputable def reducedSource364 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2264 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow364 : Integer.Sparse Master := [(Sum.inr 3533, 2), (Sum.inr 3582, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck364 : Integer.Sparse.reindex keyMap MixedData.row364 = numericRow364 := by decide +kernel

theorem numericCheck364 (x : Master → ℝ) : Integer.Sparse.eval numericRow364 x =
    (1 : ℝ) * reducedSource364 x := by
  norm_num [numericRow364, reducedSource364, Integer.Sparse.eval, Sparse.eval, nodeValue2264, nodeValue3533, nodeValue3582, nodeValue3627, nodeValue3629, nodeValue4084]

noncomputable def reducedSource365 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + 0))))))))))))))))))))

def numericRow365 : Integer.Sparse Master := [(Sum.inl 0, 233), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 12, -80), (Sum.inl 1, -90), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1246, -2160), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3077, -4320), (Sum.inr 3293, -4320), (Sum.inr 3301, -2160), (Sum.inr 3308, -2160), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3627, -2160), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160), (Sum.inr 3906, -4320), (Sum.inr 3907, -2160)]

theorem reindexCheck365 : Integer.Sparse.reindex keyMap MixedData.row365 = numericRow365 := by decide +kernel

theorem numericCheck365 (x : Master → ℝ) : Integer.Sparse.eval numericRow365 x =
    (8640 : ℝ) * reducedSource365 x := by
  norm_num [numericRow365, reducedSource365, Integer.Sparse.eval, Sparse.eval, nodeValue4602, nodeValue4605, nodeValue4612, nodeValue4623, nodeValue4807, nodeValue4843, nodeValue4890, nodeValue5149, nodeValue5152, nodeValue5172, nodeValue5204, nodeValue5207, nodeValue5284, nodeValue5292, nodeValue5293, nodeValue5294, nodeValue5307, nodeValue5435, nodeValue5443, nodeValue5453, nodeValue5454]; ring

noncomputable def reducedSource366 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

def numericRow366 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 1236, 1440), (Sum.inr 1239, 720), (Sum.inr 1246, 720), (Sum.inr 2025, 1440), (Sum.inr 2062, 720), (Sum.inr 2247, 720), (Sum.inr 2881, 1440), (Sum.inr 2889, 720), (Sum.inr 2924, 1440), (Sum.inr 2931, 1440), (Sum.inr 3077, 1440)]

theorem reindexCheck366 : Integer.Sparse.reindex keyMap MixedData.row366 = numericRow366 := by decide +kernel

theorem numericCheck366 (x : Master → ℝ) : Integer.Sparse.eval numericRow366 x =
    (720 : ℝ) * reducedSource366 x := by
  norm_num [numericRow366, reducedSource366, Integer.Sparse.eval, Sparse.eval, nodeValue1236, nodeValue1239, nodeValue1246, nodeValue1300, nodeValue2025, nodeValue2062, nodeValue2247, nodeValue2881, nodeValue2889, nodeValue2924, nodeValue2931, nodeValue2959, nodeValue3077, nodeValue3100, nodeValue3101, nodeValue3102, nodeValue3122, nodeValue3853, nodeValue3862, nodeValue3912, nodeValue4040]; ring

noncomputable def reducedSource367 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5076 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

def numericRow367 : Integer.Sparse Master := [(Sum.inl 0, 236), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 4, -80), (Sum.inl 1, -165), (Sum.inr 1044, -4320), (Sum.inr 1046, -2160), (Sum.inr 1049, -2160), (Sum.inr 1087, -2160), (Sum.inr 1737, -4320), (Sum.inr 1738, -2160), (Sum.inr 1739, -2160), (Sum.inr 1750, -2160), (Sum.inr 2483, -4320), (Sum.inr 2485, -4320), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 2764, -4320), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3477, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3481, -4320), (Sum.inr 3581, -4320), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3613, -4320), (Sum.inr 3614, -2160), (Sum.inr 3615, -2160), (Sum.inr 3632, -4320), (Sum.inr 3633, -2160), (Sum.inr 3634, -2160), (Sum.inr 3903, -4320)]

theorem reindexCheck367 : Integer.Sparse.reindex keyMap MixedData.row367 = numericRow367 := by decide +kernel

theorem numericCheck367 (x : Master → ℝ) : Integer.Sparse.eval numericRow367 x =
    (8640 : ℝ) * reducedSource367 x := by
  norm_num [numericRow367, reducedSource367, Integer.Sparse.eval, Sparse.eval, nodeValue4461, nodeValue4463, nodeValue4466, nodeValue4503, nodeValue5076, nodeValue5078, nodeValue5080, nodeValue5105, nodeValue5172, nodeValue5174, nodeValue5176, nodeValue5290, nodeValue5291, nodeValue5294, nodeValue5296, nodeValue5304, nodeValue5310, nodeValue5434, nodeValue5442, nodeValue5455, nodeValue5492]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
