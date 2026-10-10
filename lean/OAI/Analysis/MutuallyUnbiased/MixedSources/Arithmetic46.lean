import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
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

noncomputable def reducedSource736 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((2 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

def numericRow736 : Integer.Sparse Master := [(Sum.inl 0, -102), (Sum.inl 2, -50), (Sum.inl 3, 480), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -420), (Sum.inr 2260, 8640), (Sum.inr 2287, 4320), (Sum.inr 2288, 4320), (Sum.inr 2718, 8640), (Sum.inr 2735, 8640), (Sum.inr 2736, 8640), (Sum.inr 2739, 8640), (Sum.inr 2760, 8640), (Sum.inr 2761, 4320), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2769, 4320), (Sum.inr 2779, 4320), (Sum.inr 2781, 4320), (Sum.inr 2782, 4320), (Sum.inr 3097, 8640)]

theorem reindexCheck736 : Integer.Sparse.reindex keyMap MixedData.row736 = numericRow736 := by decide +kernel

theorem numericCheck736 (x : Master → ℝ) : Integer.Sparse.eval numericRow736 x =
    (4320 : ℝ) * reducedSource736 x := by
  norm_num [numericRow736, reducedSource736, Integer.Sparse.eval, Sparse.eval, nodeValue2260, nodeValue2287, nodeValue2288, nodeValue2291, nodeValue2718, nodeValue2735, nodeValue2736, nodeValue2739, nodeValue2760, nodeValue2761, nodeValue2763, nodeValue2764, nodeValue2769, nodeValue2779, nodeValue2781, nodeValue2782, nodeValue2784, nodeValue2785, nodeValue3097, nodeValue3119, nodeValue3120]; ring

noncomputable def reducedSource737 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((4 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + 0)))))))))))))

def numericRow737 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3307, -48), (Sum.inr 3308, -24), (Sum.inr 3309, -48), (Sum.inr 3602, -48), (Sum.inr 3607, -96), (Sum.inr 3613, -48), (Sum.inr 3622, -96), (Sum.inr 3627, -48), (Sum.inr 3632, -48)]

theorem reindexCheck737 : Integer.Sparse.reindex keyMap MixedData.row737 = numericRow737 := by decide +kernel

theorem numericCheck737 (x : Master → ℝ) : Integer.Sparse.eval numericRow737 x =
    (96 : ℝ) * reducedSource737 x := by
  norm_num [numericRow737, reducedSource737, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue4622, nodeValue4623, nodeValue4624, nodeValue5167, nodeValue5169, nodeValue5172, nodeValue5292, nodeValue5293, nodeValue5294, nodeValue5307, nodeValue5309, nodeValue5440, nodeValue5454]; ring

noncomputable def reducedSource738 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))))))))))))))))))

def numericRow738 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 1236, -4320), (Sum.inr 2508, -4320), (Sum.inr 2512, -4320), (Sum.inr 2515, -4320), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 2782, -4320), (Sum.inr 3293, -4320), (Sum.inr 3460, -4320), (Sum.inr 3471, -4320), (Sum.inr 3479, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3548, -4320), (Sum.inr 3583, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 4599, 17280), (Sum.inr 4603, 17280), (Sum.inr 4607, 17280), (Sum.inr 4616, 17280), (Sum.inr 5138, 17280), (Sum.inr 5160, 17280), (Sum.inr 5260, 17280), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5289, 17280), (Sum.inr 5299, 17280)]

theorem reindexCheck738 : Integer.Sparse.reindex keyMap MixedData.row738 = numericRow738 := by decide +kernel

theorem numericCheck738 (x : Master → ℝ) : Integer.Sparse.eval numericRow738 x =
    (17280 : ℝ) * reducedSource738 x := by
  norm_num [numericRow738, reducedSource738, Integer.Sparse.eval, Sparse.eval, nodeValue4599, nodeValue4602, nodeValue4603, nodeValue4607, nodeValue4616, nodeValue5098, nodeValue5101, nodeValue5102, nodeValue5105, nodeValue5134, nodeValue5135, nodeValue5138, nodeValue5160, nodeValue5256, nodeValue5258, nodeValue5260, nodeValue5265, nodeValue5266, nodeValue5267, nodeValue5271, nodeValue5274, nodeValue5275, nodeValue5289, nodeValue5299, nodeValue5304, nodeValue5410, nodeValue5424, nodeValue5434, nodeValue5435, nodeValue5442]; ring

noncomputable def reducedSource739 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + 0)))))))))))))))))))))))))))))

def numericRow739 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 195), (Sum.inr 3289, 4320), (Sum.inr 3293, 4320), (Sum.inr 3294, 4320), (Sum.inr 3296, 4320), (Sum.inr 3303, 4320), (Sum.inr 3460, 4320), (Sum.inr 3471, 4320), (Sum.inr 3479, 4320), (Sum.inr 3514, 4320), (Sum.inr 3517, 4320), (Sum.inr 3526, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3540, 4320), (Sum.inr 3541, 4320), (Sum.inr 3548, 4320), (Sum.inr 3558, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3583, 4320), (Sum.inr 3838, 4320)]

theorem reindexCheck739 : Integer.Sparse.reindex keyMap MixedData.row739 = numericRow739 := by decide +kernel

theorem numericCheck739 (x : Master → ℝ) : Integer.Sparse.eval numericRow739 x =
    (4320 : ℝ) * reducedSource739 x := by
  norm_num [numericRow739, reducedSource739, Integer.Sparse.eval, Sparse.eval, nodeValue3289, nodeValue3293, nodeValue3294, nodeValue3296, nodeValue3303, nodeValue3460, nodeValue3470, nodeValue3471, nodeValue3479, nodeValue3514, nodeValue3515, nodeValue3517, nodeValue3525, nodeValue3526, nodeValue3533, nodeValue3534, nodeValue3535, nodeValue3540, nodeValue3541, nodeValue3547, nodeValue3548, nodeValue3558, nodeValue3572, nodeValue3573, nodeValue3583, nodeValue3808, nodeValue3838, nodeValue3852, nodeValue3853, nodeValue3861]; ring

noncomputable def reducedSource740 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((1 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5055 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))))))))))

def numericRow740 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 2, 1), (Sum.inl 1, -1), (Sum.inr 998, -72), (Sum.inr 999, -72), (Sum.inr 1000, -72), (Sum.inr 1005, -72), (Sum.inr 1079, -72), (Sum.inr 1600, -72), (Sum.inr 1602, -72), (Sum.inr 1605, -72), (Sum.inr 1623, -72), (Sum.inr 1708, -72), (Sum.inr 2398, -72), (Sum.inr 2399, -72), (Sum.inr 2400, -72), (Sum.inr 2404, -72), (Sum.inr 2458, -144), (Sum.inr 2459, -72), (Sum.inr 2462, -72), (Sum.inr 2467, -72), (Sum.inr 2508, -72), (Sum.inr 2509, -72), (Sum.inr 2703, -72), (Sum.inr 2704, -72), (Sum.inr 2705, -72), (Sum.inr 2721, -72), (Sum.inr 2722, -72), (Sum.inr 2723, -72), (Sum.inr 2739, -144), (Sum.inr 2740, -144), (Sum.inr 2743, -72), (Sum.inr 3341, -72), (Sum.inr 3344, -72), (Sum.inr 3357, -72), (Sum.inr 3429, -72), (Sum.inr 3436, -72), (Sum.inr 3460, -72), (Sum.inr 3496, -72), (Sum.inr 3498, -72), (Sum.inr 3532, -72), (Sum.inr 3533, -72), (Sum.inr 3534, -144), (Sum.inr 3544, -72), (Sum.inr 3548, -72), (Sum.inr 3622, -72), (Sum.inr 3623, -72), (Sum.inr 3958, -72), (Sum.inr 3961, -72), (Sum.inr 3974, -144), (Sum.inr 4010, -72)]

theorem reindexCheck740 : Integer.Sparse.reindex keyMap MixedData.row740 = numericRow740 := by decide +kernel

theorem numericCheck740 (x : Master → ℝ) : Integer.Sparse.eval numericRow740 x =
    (288 : ℝ) * reducedSource740 x := by
  norm_num [numericRow740, reducedSource740, Integer.Sparse.eval, Sparse.eval, nodeValue4417, nodeValue4418, nodeValue4419, nodeValue4424, nodeValue4495, nodeValue5013, nodeValue5014, nodeValue5015, nodeValue5018, nodeValue5055, nodeValue5056, nodeValue5059, nodeValue5098, nodeValue5099, nodeValue5247, nodeValue5248, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5272, nodeValue5275, nodeValue5292, nodeValue5306, nodeValue5473, nodeValue5478, nodeValue5485, nodeValue5490, nodeValue5492]; ring

noncomputable def reducedSource741 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2458 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + 0))))))))))))))))))))))))))))

def numericRow741 : Integer.Sparse Master := [(Sum.inl 0, -198), (Sum.inl 2, -65), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 998, 4320), (Sum.inr 999, 4320), (Sum.inr 1000, 4320), (Sum.inr 1005, 4320), (Sum.inr 1079, 4320), (Sum.inr 2398, 4320), (Sum.inr 2399, 4320), (Sum.inr 2400, 4320), (Sum.inr 2404, 4320), (Sum.inr 2458, 4320), (Sum.inr 2459, 4320), (Sum.inr 2462, 4320), (Sum.inr 2508, 4320), (Sum.inr 2703, 4320), (Sum.inr 2704, 4320), (Sum.inr 2705, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 4320), (Sum.inr 2723, 4320), (Sum.inr 2739, 8640), (Sum.inr 2740, 4320), (Sum.inr 2743, 4320), (Sum.inr 3961, 4320), (Sum.inr 3974, 4320), (Sum.inr 4010, 4320)]

theorem reindexCheck741 : Integer.Sparse.reindex keyMap MixedData.row741 = numericRow741 := by decide +kernel

theorem numericCheck741 (x : Master → ℝ) : Integer.Sparse.eval numericRow741 x =
    (4320 : ℝ) * reducedSource741 x := by
  norm_num [numericRow741, reducedSource741, Integer.Sparse.eval, Sparse.eval, nodeValue998, nodeValue999, nodeValue1000, nodeValue1005, nodeValue1079, nodeValue2398, nodeValue2399, nodeValue2400, nodeValue2404, nodeValue2458, nodeValue2459, nodeValue2462, nodeValue2508, nodeValue2703, nodeValue2704, nodeValue2705, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2739, nodeValue2740, nodeValue2743, nodeValue2766, nodeValue2784, nodeValue3961, nodeValue3974, nodeValue4010, nodeValue4013, nodeValue4015]; ring

noncomputable def reducedSource742 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5246 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((3 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))))))))))

def numericRow742 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 2020, -864), (Sum.inr 2025, -864), (Sum.inr 2029, -864), (Sum.inr 2202, -864), (Sum.inr 2224, -864), (Sum.inr 2225, -864), (Sum.inr 2684, -864), (Sum.inr 2703, -864), (Sum.inr 2721, -864), (Sum.inr 2739, -2592), (Sum.inr 2764, -864), (Sum.inr 2782, -864), (Sum.inr 3394, -864), (Sum.inr 3496, -864), (Sum.inr 3532, -864), (Sum.inr 3534, -2592), (Sum.inr 3581, -864), (Sum.inr 3583, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 5150, 3456), (Sum.inr 5151, 3456), (Sum.inr 5173, 3456), (Sum.inr 5226, 3456), (Sum.inr 5236, 3456), (Sum.inr 5255, 3456), (Sum.inr 5269, 3456), (Sum.inr 5270, 3456), (Sum.inr 5281, 3456), (Sum.inr 5289, 3456), (Sum.inr 5299, 3456)]

theorem reindexCheck742 : Integer.Sparse.reindex keyMap MixedData.row742 = numericRow742 := by decide +kernel

theorem numericCheck742 (x : Master → ℝ) : Integer.Sparse.eval numericRow742 x =
    (3456 : ℝ) * reducedSource742 x := by
  norm_num [numericRow742, reducedSource742, Integer.Sparse.eval, Sparse.eval, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4895, nodeValue5150, nodeValue5151, nodeValue5173, nodeValue5226, nodeValue5236, nodeValue5237, nodeValue5246, nodeValue5247, nodeValue5255, nodeValue5256, nodeValue5257, nodeValue5269, nodeValue5270, nodeValue5271, nodeValue5273, nodeValue5281, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5299, nodeValue5304, nodeValue5306, nodeValue5307]; ring

noncomputable def reducedSource743 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((3 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + 0)))))))))))))))))))))))))))

def numericRow743 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -200), (Sum.inr 2202, 4320), (Sum.inr 2224, 4320), (Sum.inr 2225, 4320), (Sum.inr 2669, 4320), (Sum.inr 2681, 4320), (Sum.inr 2682, 4320), (Sum.inr 2684, 4320), (Sum.inr 2700, 4320), (Sum.inr 2703, 4320), (Sum.inr 2718, 4320), (Sum.inr 2721, 4320), (Sum.inr 2735, 4320), (Sum.inr 2736, 4320), (Sum.inr 2738, 4320), (Sum.inr 2739, 12960), (Sum.inr 2782, 4320), (Sum.inr 3051, 4320), (Sum.inr 3074, 4320), (Sum.inr 3097, 4320)]

theorem reindexCheck743 : Integer.Sparse.reindex keyMap MixedData.row743 = numericRow743 := by decide +kernel

theorem numericCheck743 (x : Master → ℝ) : Integer.Sparse.eval numericRow743 x =
    (4320 : ℝ) * reducedSource743 x := by
  norm_num [numericRow743, reducedSource743, Integer.Sparse.eval, Sparse.eval, nodeValue2202, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2291, nodeValue2669, nodeValue2681, nodeValue2682, nodeValue2684, nodeValue2700, nodeValue2701, nodeValue2703, nodeValue2718, nodeValue2720, nodeValue2721, nodeValue2735, nodeValue2736, nodeValue2738, nodeValue2739, nodeValue2741, nodeValue2782, nodeValue2784, nodeValue2785, nodeValue3051, nodeValue3074, nodeValue3097, nodeValue3099, nodeValue3100]; ring

noncomputable def reducedSource744 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((3 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((3 : ℝ) * Sparse.eval nodeValue5104 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((6 : ℝ) * Sparse.eval nodeValue5259 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))

def numericRow744 : Integer.Sparse Master := [(Sum.inr 1235, -1), (Sum.inr 1240, -3), (Sum.inr 1293, -1), (Sum.inr 2556, -3), (Sum.inr 2589, -1), (Sum.inr 2721, -3), (Sum.inr 2723, -6), (Sum.inr 2764, -3), (Sum.inr 3292, -1), (Sum.inr 3299, -3), (Sum.inr 3304, -1), (Sum.inr 3521, -3), (Sum.inr 3532, -3), (Sum.inr 3544, -6), (Sum.inr 3563, -1), (Sum.inr 3581, -3), (Sum.inr 4091, 4)]

theorem reindexCheck744 : Integer.Sparse.reindex keyMap MixedData.row744 = numericRow744 := by decide +kernel

theorem numericCheck744 (x : Master → ℝ) : Integer.Sparse.eval numericRow744 x =
    (4 : ℝ) * reducedSource744 x := by
  norm_num [numericRow744, reducedSource744, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue4601, nodeValue4606, nodeValue4618, nodeValue5100, nodeValue5104, nodeValue5137, nodeValue5162, nodeValue5257, nodeValue5259, nodeValue5290, nodeValue5427, nodeValue5440]; ring

noncomputable def reducedSource745 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5247 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((6 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))

def numericRow745 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2671, -1440), (Sum.inr 2684, -4320), (Sum.inr 2703, -4320), (Sum.inr 2721, -4320), (Sum.inr 2739, -8640), (Sum.inr 3053, -1440), (Sum.inr 3390, -1440), (Sum.inr 3394, -4320), (Sum.inr 3496, -4320), (Sum.inr 3532, -4320), (Sum.inr 3534, -8640), (Sum.inr 3619, -1440), (Sum.inr 3622, -4320), (Sum.inr 4083, 5760)]

theorem reindexCheck745 : Integer.Sparse.reindex keyMap MixedData.row745 = numericRow745 := by decide +kernel

theorem numericCheck745 (x : Master → ℝ) : Integer.Sparse.eval numericRow745 x =
    (5760 : ℝ) * reducedSource745 x := by
  norm_num [numericRow745, reducedSource745, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4833, nodeValue4838, nodeValue5227, nodeValue5237, nodeValue5247, nodeValue5257, nodeValue5271, nodeValue5273, nodeValue5283, nodeValue5292, nodeValue5301, nodeValue5307]; ring

noncomputable def reducedSource746 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4438 x + ((2 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((4 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4885 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((4 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5283 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + 0)))))))))))))

def numericRow746 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1039, -4320), (Sum.inr 1706, -4320), (Sum.inr 2105, -4320), (Sum.inr 2241, -4320), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2277, -4320), (Sum.inr 3622, -4320), (Sum.inr 4439, 17280), (Sum.inr 4851, 17280), (Sum.inr 4852, 34560), (Sum.inr 4885, 17280), (Sum.inr 5281, 17280)]

theorem reindexCheck746 : Integer.Sparse.reindex keyMap MixedData.row746 = numericRow746 := by decide +kernel

theorem numericCheck746 (x : Master → ℝ) : Integer.Sparse.eval numericRow746 x =
    (8640 : ℝ) * reducedSource746 x := by
  norm_num [numericRow746, reducedSource746, Integer.Sparse.eval, Sparse.eval, nodeValue4438, nodeValue4439, nodeValue4456, nodeValue4851, nodeValue4852, nodeValue4864, nodeValue4885, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5281, nodeValue5283, nodeValue5292]; ring

noncomputable def reducedSource747 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((2 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((2 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((4 : ℝ) * Sparse.eval nodeValue2250 x + ((2 : ℝ) * Sparse.eval nodeValue2252 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((4 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2752 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + 0)))))))))))))

def numericRow747 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 1706, 4320), (Sum.inr 1713, 4320), (Sum.inr 2240, 4320), (Sum.inr 2241, 4320), (Sum.inr 2243, 4320), (Sum.inr 2250, 8640), (Sum.inr 2252, 4320), (Sum.inr 2262, 4320), (Sum.inr 2277, 4320), (Sum.inr 2750, 4320)]

theorem reindexCheck747 : Integer.Sparse.reindex keyMap MixedData.row747 = numericRow747 := by decide +kernel

theorem numericCheck747 (x : Master → ℝ) : Integer.Sparse.eval numericRow747 x =
    (2160 : ℝ) * reducedSource747 x := by
  norm_num [numericRow747, reducedSource747, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1706, nodeValue1713, nodeValue2240, nodeValue2241, nodeValue2243, nodeValue2250, nodeValue2252, nodeValue2262, nodeValue2263, nodeValue2277, nodeValue2750, nodeValue2752, nodeValue2766]; ring

noncomputable def reducedSource748 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4248 x + ((4 : ℝ) * Sparse.eval nodeValue4249 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((8 : ℝ) * Sparse.eval nodeValue4802 x + ((4 : ℝ) * Sparse.eval nodeValue4831 x + ((4 : ℝ) * Sparse.eval nodeValue4888 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + 0)))))))

def numericRow748 : Integer.Sparse Master := [(Sum.inl 0, 64), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -120), (Sum.inl 4, -160), (Sum.inl 1, 15), (Sum.inr 782, -2160), (Sum.inr 783, -4320), (Sum.inr 803, -4320), (Sum.inr 2019, -4320), (Sum.inr 2020, -8640), (Sum.inr 2051, -4320), (Sum.inr 2190, -4320), (Sum.inr 2191, -4320), (Sum.inr 2202, -8640), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 3901, -4320)]

theorem reindexCheck748 : Integer.Sparse.reindex keyMap MixedData.row748 = numericRow748 := by decide +kernel

theorem numericCheck748 (x : Master → ℝ) : Integer.Sparse.eval numericRow748 x =
    (4320 : ℝ) * reducedSource748 x := by
  norm_num [numericRow748, reducedSource748, Integer.Sparse.eval, Sparse.eval, nodeValue4248, nodeValue4249, nodeValue4801, nodeValue4802, nodeValue4831, nodeValue4888, nodeValue5433, nodeValue5452]; ring

noncomputable def reducedSource749 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((3 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))

def numericRow749 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1039, -2160), (Sum.inr 1041, -4320), (Sum.inr 1044, -2160), (Sum.inr 1706, -2160), (Sum.inr 1724, -4320), (Sum.inr 1737, -2160), (Sum.inr 2020, -4320), (Sum.inr 2023, -2160), (Sum.inr 2105, -2160), (Sum.inr 2107, -4320), (Sum.inr 2110, -2160), (Sum.inr 2202, -4320), (Sum.inr 2214, -2160), (Sum.inr 2241, -2160), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2260, -4320), (Sum.inr 2262, -4320), (Sum.inr 2275, -2160), (Sum.inr 2277, -4320), (Sum.inr 2721, -2160), (Sum.inr 2764, -2160), (Sum.inr 3532, -2160), (Sum.inr 3581, -2160), (Sum.inr 3622, -4320), (Sum.inr 4083, 8640)]

theorem reindexCheck749 : Integer.Sparse.reindex keyMap MixedData.row749 = numericRow749 := by decide +kernel

theorem numericCheck749 (x : Master → ℝ) : Integer.Sparse.eval numericRow749 x =
    (8640 : ℝ) * reducedSource749 x := by
  norm_num [numericRow749, reducedSource749, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4497, nodeValue4802, nodeValue4805, nodeValue4833, nodeValue4864, nodeValue4866, nodeValue4869, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue4895, nodeValue5257, nodeValue5290, nodeValue5292, nodeValue5307]; ring

noncomputable def reducedSource750 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4068 x + ((3 : ℝ) * Sparse.eval nodeValue4069 x + ((2 : ℝ) * Sparse.eval nodeValue4079 x + ((6 : ℝ) * Sparse.eval nodeValue4080 x + ((6 : ℝ) * Sparse.eval nodeValue4083 x + ((6 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4091 x + ((3 : ℝ) * Sparse.eval nodeValue4093 x + 0)))))))

def numericRow750 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 4068, 16), (Sum.inr 4069, 24), (Sum.inr 4079, 16), (Sum.inr 4080, 48), (Sum.inr 4083, 48), (Sum.inr 4084, 48), (Sum.inr 4091, 16)]

theorem reindexCheck750 : Integer.Sparse.reindex keyMap MixedData.row750 = numericRow750 := by decide +kernel

theorem numericCheck750 (x : Master → ℝ) : Integer.Sparse.eval numericRow750 x =
    (8 : ℝ) * reducedSource750 x := by
  norm_num [numericRow750, reducedSource750, Integer.Sparse.eval, Sparse.eval, nodeValue4068, nodeValue4069, nodeValue4079, nodeValue4080, nodeValue4083, nodeValue4084, nodeValue4091, nodeValue4093]; ring

noncomputable def reducedSource751 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2970 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3473 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3648 x + ((1 : ℝ) * Sparse.eval nodeValue3658 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + 0)))))))))))))))))))))))))))))

def numericRow751 : Integer.Sparse Master := [(Sum.inl 0, -44), (Sum.inl 2, 10), (Sum.inl 3, 560), (Sum.inl 13, 80), (Sum.inl 12, 320), (Sum.inl 4, 240), (Sum.inl 1, -170), (Sum.inr 1902, 4320), (Sum.inr 1904, 4320), (Sum.inr 1910, 4320), (Sum.inr 1923, 4320), (Sum.inr 2253, 4320), (Sum.inr 2970, 4320), (Sum.inr 2974, 4320), (Sum.inr 2984, 4320), (Sum.inr 3016, 4320), (Sum.inr 3463, 4320), (Sum.inr 3464, 4320), (Sum.inr 3473, 4320), (Sum.inr 3528, 4320), (Sum.inr 3648, 4320), (Sum.inr 3658, 4320), (Sum.inr 3761, 4320), (Sum.inr 3762, 4320), (Sum.inr 3780, 4320), (Sum.inr 3783, 4320), (Sum.inr 3788, 4320), (Sum.inr 3800, 4320), (Sum.inr 3801, 4320), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3814, 4320)]

theorem reindexCheck751 : Integer.Sparse.reindex keyMap MixedData.row751 = numericRow751 := by decide +kernel

theorem numericCheck751 (x : Master → ℝ) : Integer.Sparse.eval numericRow751 x =
    (4320 : ℝ) * reducedSource751 x := by
  norm_num [numericRow751, reducedSource751, Integer.Sparse.eval, Sparse.eval, nodeValue1902, nodeValue1904, nodeValue1910, nodeValue1923, nodeValue2253, nodeValue2970, nodeValue2974, nodeValue2984, nodeValue3016, nodeValue3463, nodeValue3464, nodeValue3473, nodeValue3528, nodeValue3648, nodeValue3658, nodeValue3761, nodeValue3762, nodeValue3780, nodeValue3783, nodeValue3788, nodeValue3800, nodeValue3801, nodeValue3802, nodeValue3803, nodeValue3813, nodeValue3814, nodeValue3847, nodeValue3856, nodeValue3883, nodeValue3977]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
