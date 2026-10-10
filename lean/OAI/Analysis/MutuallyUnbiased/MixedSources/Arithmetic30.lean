import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
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

noncomputable def reducedSource480 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow480 : Integer.Sparse Master := [(Sum.inr 1261, 1), (Sum.inr 2566, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 2763, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem reindexCheck480 : Integer.Sparse.reindex keyMap MixedData.row480 = numericRow480 := by decide +kernel

theorem numericCheck480 (x : Master → ℝ) : Integer.Sparse.eval numericRow480 x =
    (1 : ℝ) * reducedSource480 x := by
  norm_num [numericRow480, reducedSource480, Integer.Sparse.eval, Sparse.eval, nodeValue1261, nodeValue2566, nodeValue2632, nodeValue2722, nodeValue2763, nodeValue2765, nodeValue4092]

noncomputable def reducedSource481 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue5070 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

def numericRow481 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 5, -20), (Sum.inl 2, -10), (Sum.inl 7, -80), (Sum.inl 3, -320), (Sum.inl 12, -80), (Sum.inl 4, -240), (Sum.inl 1, 25), (Sum.inr 1035, -4320), (Sum.inr 1037, -2160), (Sum.inr 1049, -2160), (Sum.inr 1075, -2160), (Sum.inr 1645, -4320), (Sum.inr 1647, -2160), (Sum.inr 1653, -2160), (Sum.inr 1738, -2160), (Sum.inr 2047, -4320), (Sum.inr 2065, -2160), (Sum.inr 2079, -4320), (Sum.inr 2109, -2160), (Sum.inr 2218, -2160), (Sum.inr 2261, -2160), (Sum.inr 2477, -4320), (Sum.inr 2488, -4320), (Sum.inr 2505, -4320), (Sum.inr 2590, -4320), (Sum.inr 2672, -4320), (Sum.inr 2686, -2160), (Sum.inr 2764, -4320), (Sum.inr 2782, -2160), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3444, -4320), (Sum.inr 3448, -4320), (Sum.inr 3478, -4320), (Sum.inr 3564, -4320), (Sum.inr 3581, -4320), (Sum.inr 3583, -2160), (Sum.inr 3614, -2160), (Sum.inr 3632, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160)]

theorem reindexCheck481 : Integer.Sparse.reindex keyMap MixedData.row481 = numericRow481 := by decide +kernel

theorem numericCheck481 (x : Master → ℝ) : Integer.Sparse.eval numericRow481 x =
    (8640 : ℝ) * reducedSource481 x := by
  norm_num [numericRow481, reducedSource481, Integer.Sparse.eval, Sparse.eval, nodeValue4452, nodeValue4454, nodeValue4466, nodeValue4491, nodeValue4827, nodeValue4845, nodeValue4868, nodeValue5070, nodeValue5080, nodeValue5095, nodeValue5163, nodeValue5176, nodeValue5228, nodeValue5238, nodeValue5290, nodeValue5294, nodeValue5304, nodeValue5438, nodeValue5443, nodeValue5451, nodeValue5492]
  ring

noncomputable def reducedSource482 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2477 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2505 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

def numericRow482 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 5, 4), (Sum.inl 2, 3), (Sum.inl 7, 16), (Sum.inl 3, 48), (Sum.inl 4, 32), (Sum.inl 1, 2), (Sum.inr 1035, 864), (Sum.inr 1037, 432), (Sum.inr 1049, 432), (Sum.inr 1075, 432), (Sum.inr 2079, 864), (Sum.inr 2109, 432), (Sum.inr 2218, 432), (Sum.inr 2477, 864), (Sum.inr 2488, 864), (Sum.inr 2505, 864), (Sum.inr 2590, 864), (Sum.inr 2672, 864), (Sum.inr 2686, 432), (Sum.inr 2764, 864), (Sum.inr 2782, 432), (Sum.inr 3876, 864), (Sum.inr 3907, 432)]

theorem reindexCheck482 : Integer.Sparse.reindex keyMap MixedData.row482 = numericRow482 := by decide +kernel

theorem numericCheck482 (x : Master → ℝ) : Integer.Sparse.eval numericRow482 x =
    (432 : ℝ) * reducedSource482 x := by
  norm_num [numericRow482, reducedSource482, Integer.Sparse.eval, Sparse.eval, nodeValue1035, nodeValue1037, nodeValue1049, nodeValue1075, nodeValue2079, nodeValue2109, nodeValue2218, nodeValue2477, nodeValue2488, nodeValue2505, nodeValue2590, nodeValue2604, nodeValue2672, nodeValue2686, nodeValue2764, nodeValue2768, nodeValue2782, nodeValue3876, nodeValue3888, nodeValue3907, nodeValue4017]
  ring

noncomputable def reducedSource483 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((2 : ℝ) * Sparse.eval nodeValue5249 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5297 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

def numericRow483 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inr 2106, -1440), (Sum.inr 2109, -720), (Sum.inr 2115, -720), (Sum.inr 2242, -1440), (Sum.inr 2261, -720), (Sum.inr 2276, -720), (Sum.inr 2722, -1440), (Sum.inr 2743, -720), (Sum.inr 2765, -1440), (Sum.inr 2783, -1440), (Sum.inr 3533, -1440), (Sum.inr 3548, -720), (Sum.inr 3582, -1440), (Sum.inr 3627, -720), (Sum.inr 3633, -720), (Sum.inr 5161, 5760), (Sum.inr 5175, 2880), (Sum.inr 5249, 5760), (Sum.inr 5260, 5760), (Sum.inr 5264, 5760), (Sum.inr 5276, 2880), (Sum.inr 5279, 5760), (Sum.inr 5282, 5760), (Sum.inr 5297, 2880), (Sum.inr 5300, 2880)]

theorem reindexCheck483 : Integer.Sparse.reindex keyMap MixedData.row483 = numericRow483 := by decide +kernel

theorem numericCheck483 (x : Master → ℝ) : Integer.Sparse.eval numericRow483 x =
    (2880 : ℝ) * reducedSource483 x := by
  norm_num [numericRow483, reducedSource483, Integer.Sparse.eval, Sparse.eval, nodeValue4865, nodeValue4868, nodeValue4874, nodeValue4894, nodeValue5161, nodeValue5175, nodeValue5249, nodeValue5258, nodeValue5260, nodeValue5264, nodeValue5275, nodeValue5276, nodeValue5279, nodeValue5282, nodeValue5291, nodeValue5293, nodeValue5297, nodeValue5300, nodeValue5305, nodeValue5308, nodeValue5310]
  ring

noncomputable def reducedSource484 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((2 : ℝ) * Sparse.eval nodeValue2708 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((2 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))))))))))

def numericRow484 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 2242, 2160), (Sum.inr 2261, 1080), (Sum.inr 2276, 1080), (Sum.inr 2708, 2160), (Sum.inr 2719, 2160), (Sum.inr 2722, 2160), (Sum.inr 2729, 2160), (Sum.inr 2748, 2160), (Sum.inr 2751, 2160), (Sum.inr 2761, 1080), (Sum.inr 2765, 2160), (Sum.inr 2771, 1080), (Sum.inr 2774, 1080), (Sum.inr 2777, 1080), (Sum.inr 2783, 1080), (Sum.inr 3086, 2160)]

theorem reindexCheck484 : Integer.Sparse.reindex keyMap MixedData.row484 = numericRow484 := by decide +kernel

theorem numericCheck484 (x : Master → ℝ) : Integer.Sparse.eval numericRow484 x =
    (1080 : ℝ) * reducedSource484 x := by
  norm_num [numericRow484, reducedSource484, Integer.Sparse.eval, Sparse.eval, nodeValue2242, nodeValue2261, nodeValue2264, nodeValue2276, nodeValue2708, nodeValue2719, nodeValue2722, nodeValue2729, nodeValue2748, nodeValue2751, nodeValue2761, nodeValue2765, nodeValue2767, nodeValue2771, nodeValue2774, nodeValue2777, nodeValue2783, nodeValue2786, nodeValue3086, nodeValue3110, nodeValue3121]
  ring

noncomputable def reducedSource485 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((2 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((2 : ℝ) * Sparse.eval nodeValue3066 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3079 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow485 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 2, 150), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 1, 130), (Sum.inr 2724, 2880), (Sum.inr 2743, 1440), (Sum.inr 2744, 1440), (Sum.inr 2964, 2880), (Sum.inr 2967, 1440), (Sum.inr 3040, 2880), (Sum.inr 3055, 1440), (Sum.inr 3056, 1440), (Sum.inr 3066, 2880), (Sum.inr 3078, 2880), (Sum.inr 3079, 2880)]

theorem reindexCheck485 : Integer.Sparse.reindex keyMap MixedData.row485 = numericRow485 := by decide +kernel

theorem numericCheck485 (x : Master → ℝ) : Integer.Sparse.eval numericRow485 x =
    (1440 : ℝ) * reducedSource485 x := by
  norm_num [numericRow485, reducedSource485, Integer.Sparse.eval, Sparse.eval, nodeValue2724, nodeValue2743, nodeValue2744, nodeValue2788, nodeValue2964, nodeValue2966, nodeValue2967, nodeValue3040, nodeValue3055, nodeValue3056, nodeValue3066, nodeValue3078, nodeValue3079, nodeValue3089, nodeValue3102, nodeValue3103, nodeValue3124, nodeValue3125, nodeValue3185, nodeValue3187, nodeValue3230]
  ring

noncomputable def reducedSource486 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2106 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow486 : Integer.Sparse Master := [(Sum.inr 2106, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem reindexCheck486 : Integer.Sparse.reindex keyMap MixedData.row486 = numericRow486 := by decide +kernel

theorem numericCheck486 (x : Master → ℝ) : Integer.Sparse.eval numericRow486 x =
    (1 : ℝ) * reducedSource486 x := by
  norm_num [numericRow486, reducedSource486, Integer.Sparse.eval, Sparse.eval, nodeValue2106, nodeValue2109, nodeValue2115, nodeValue2264, nodeValue3582, nodeValue4084]

noncomputable def reducedSource487 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4593 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))))))))))

def numericRow487 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 190), (Sum.inr 1240, -4320), (Sum.inr 2480, -4320), (Sum.inr 2485, -4320), (Sum.inr 2489, -4320), (Sum.inr 2556, -4320), (Sum.inr 2721, -4320), (Sum.inr 2723, -8640), (Sum.inr 2764, -4320), (Sum.inr 3299, -4320), (Sum.inr 3467, -4320), (Sum.inr 3481, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3544, -8640), (Sum.inr 3581, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3902, -4320), (Sum.inr 4590, 17280), (Sum.inr 4591, 17280), (Sum.inr 4593, 17280), (Sum.inr 4603, 17280), (Sum.inr 5128, 17280), (Sum.inr 5139, 17280), (Sum.inr 5145, 17280), (Sum.inr 5185, 17280), (Sum.inr 5189, 17280), (Sum.inr 5199, 17280), (Sum.inr 5252, 17280), (Sum.inr 5282, 17280)]

theorem reindexCheck487 : Integer.Sparse.reindex keyMap MixedData.row487 = numericRow487 := by decide +kernel

theorem numericCheck487 (x : Master → ℝ) : Integer.Sparse.eval numericRow487 x =
    (17280 : ℝ) * reducedSource487 x := by
  norm_num [numericRow487, reducedSource487, Integer.Sparse.eval, Sparse.eval, nodeValue4590, nodeValue4591, nodeValue4593, nodeValue4603, nodeValue4606, nodeValue5073, nodeValue5078, nodeValue5081, nodeValue5104, nodeValue5128, nodeValue5130, nodeValue5137, nodeValue5139, nodeValue5145, nodeValue5185, nodeValue5189, nodeValue5199, nodeValue5250, nodeValue5252, nodeValue5257, nodeValue5259, nodeValue5273, nodeValue5282, nodeValue5290, nodeValue5410, nodeValue5424, nodeValue5438, nodeValue5439, nodeValue5440]
  ring

noncomputable def reducedSource488 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2917 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2936 x + ((1 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2991 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))))))))))

def numericRow488 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, -200), (Sum.inr 1213, 1080), (Sum.inr 1215, 1080), (Sum.inr 1220, 1080), (Sum.inr 1237, 1080), (Sum.inr 2543, 1080), (Sum.inr 2558, 1080), (Sum.inr 2712, 1080), (Sum.inr 2862, 1080), (Sum.inr 2868, 1080), (Sum.inr 2882, 1080), (Sum.inr 2925, 1080), (Sum.inr 3078, 1080)]

theorem reindexCheck488 : Integer.Sparse.reindex keyMap MixedData.row488 = numericRow488 := by decide +kernel

theorem numericCheck488 (x : Master → ℝ) : Integer.Sparse.eval numericRow488 x =
    (1080 : ℝ) * reducedSource488 x := by
  norm_num [numericRow488, reducedSource488, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue1215, nodeValue1220, nodeValue1237, nodeValue1266, nodeValue2543, nodeValue2558, nodeValue2572, nodeValue2712, nodeValue2862, nodeValue2868, nodeValue2882, nodeValue2917, nodeValue2925, nodeValue2936, nodeValue2987, nodeValue2991, nodeValue3000, nodeValue3065, nodeValue3078, nodeValue3087, nodeValue3088, nodeValue3099, nodeValue3111, nodeValue3990, nodeValue3993, nodeValue3996, nodeValue4012, nodeValue4036]
  ring

noncomputable def reducedSource489 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + 0))))))))))))))))))))))))))))

def numericRow489 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 3290, 4320), (Sum.inr 3291, 4320), (Sum.inr 3294, 4320), (Sum.inr 3297, 4320), (Sum.inr 3299, 4320), (Sum.inr 3467, 4320), (Sum.inr 3481, 4320), (Sum.inr 3482, 4320), (Sum.inr 3519, 4320), (Sum.inr 3521, 4320), (Sum.inr 3523, 4320), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3542, 4320), (Sum.inr 3543, 4320), (Sum.inr 3544, 8640), (Sum.inr 3562, 4320), (Sum.inr 3578, 4320), (Sum.inr 3580, 4320), (Sum.inr 3581, 4320), (Sum.inr 3843, 4320), (Sum.inr 3857, 4320)]

theorem reindexCheck489 : Integer.Sparse.reindex keyMap MixedData.row489 = numericRow489 := by decide +kernel

theorem numericCheck489 (x : Master → ℝ) : Integer.Sparse.eval numericRow489 x =
    (4320 : ℝ) * reducedSource489 x := by
  norm_num [numericRow489, reducedSource489, Integer.Sparse.eval, Sparse.eval, nodeValue3290, nodeValue3291, nodeValue3294, nodeValue3297, nodeValue3299, nodeValue3467, nodeValue3481, nodeValue3482, nodeValue3483, nodeValue3519, nodeValue3520, nodeValue3521, nodeValue3523, nodeValue3529, nodeValue3531, nodeValue3532, nodeValue3542, nodeValue3543, nodeValue3544, nodeValue3546, nodeValue3562, nodeValue3578, nodeValue3580, nodeValue3581, nodeValue3816, nodeValue3843, nodeValue3857, nodeValue3858, nodeValue3859]
  ring

noncomputable def reducedSource490 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3904 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow490 : Integer.Sparse Master := [(Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 3876, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem reindexCheck490 : Integer.Sparse.reindex keyMap MixedData.row490 = numericRow490 := by decide +kernel

theorem numericCheck490 (x : Master → ℝ) : Integer.Sparse.eval numericRow490 x =
    (1 : ℝ) * reducedSource490 x := by
  norm_num [numericRow490, reducedSource490, Integer.Sparse.eval, Sparse.eval, nodeValue2723, nodeValue3808, nodeValue3838, nodeValue3876, nodeValue3902, nodeValue3904, nodeValue4091]

noncomputable def reducedSource491 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow491 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1217, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem reindexCheck491 : Integer.Sparse.reindex keyMap MixedData.row491 = numericRow491 := by decide +kernel

theorem numericCheck491 (x : Master → ℝ) : Integer.Sparse.eval numericRow491 x =
    (1 : ℝ) * reducedSource491 x := by
  norm_num [numericRow491, reducedSource491, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue1217, nodeValue1220, nodeValue1240, nodeValue1262, nodeValue2723, nodeValue4091]

noncomputable def reducedSource492 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow492 : Integer.Sparse Master := [(Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

theorem reindexCheck492 : Integer.Sparse.reindex keyMap MixedData.row492 = numericRow492 := by decide +kernel

theorem numericCheck492 (x : Master → ℝ) : Integer.Sparse.eval numericRow492 x =
    (1 : ℝ) * reducedSource492 x := by
  norm_num [numericRow492, reducedSource492, Integer.Sparse.eval, Sparse.eval, nodeValue1240, nodeValue2514, nodeValue2556, nodeValue2723, nodeValue2741, nodeValue4091]

noncomputable def reducedSource493 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow493 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 2618, 1), (Sum.inr 2621, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem reindexCheck493 : Integer.Sparse.reindex keyMap MixedData.row493 = numericRow493 := by decide +kernel

theorem numericCheck493 (x : Master → ℝ) : Integer.Sparse.eval numericRow493 x =
    (1 : ℝ) * reducedSource493 x := by
  norm_num [numericRow493, reducedSource493, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue2618, nodeValue2621, nodeValue2633, nodeValue2723, nodeValue3876, nodeValue4091]

noncomputable def reducedSource494 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow494 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 1), (Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

theorem reindexCheck494 : Integer.Sparse.reindex keyMap MixedData.row494 = numericRow494 := by decide +kernel

theorem numericCheck494 (x : Master → ℝ) : Integer.Sparse.eval numericRow494 x =
    (1 : ℝ) * reducedSource494 x := by
  norm_num [numericRow494, reducedSource494, Integer.Sparse.eval, Sparse.eval, nodeValue2543, nodeValue2546, nodeValue2556, nodeValue2567, nodeValue2723, nodeValue3838, nodeValue4091]

noncomputable def reducedSource495 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow495 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 2489, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem reindexCheck495 : Integer.Sparse.reindex keyMap MixedData.row495 = numericRow495 := by decide +kernel

theorem numericCheck495 (x : Master → ℝ) : Integer.Sparse.eval numericRow495 x =
    (1 : ℝ) * reducedSource495 x := by
  norm_num [numericRow495, reducedSource495, Integer.Sparse.eval, Sparse.eval, nodeValue2480, nodeValue2485, nodeValue2489, nodeValue2514, nodeValue2723, nodeValue3808, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
