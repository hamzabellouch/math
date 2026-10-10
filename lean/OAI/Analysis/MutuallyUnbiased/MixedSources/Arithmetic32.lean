import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
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

noncomputable def reducedSource512 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4996 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5015 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + 0)))))))))))))))))))))))))))))

def numericRow512 : Integer.Sparse Master := [(Sum.inl 0, 300), (Sum.inl 6, -5), (Sum.inl 2, 70), (Sum.inl 7, 80), (Sum.inl 3, 320), (Sum.inl 12, 80), (Sum.inl 4, 240), (Sum.inl 1, 175), (Sum.inr 977, -4320), (Sum.inr 979, -4320), (Sum.inr 985, -4320), (Sum.inr 1000, -4320), (Sum.inr 1040, -4320), (Sum.inr 1597, -4320), (Sum.inr 1599, -4320), (Sum.inr 1605, -4320), (Sum.inr 1618, -4320), (Sum.inr 1707, -4320), (Sum.inr 1987, -4320), (Sum.inr 1996, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2022, -4320), (Sum.inr 2052, -4320), (Sum.inr 2193, -4320), (Sum.inr 2203, -4320), (Sum.inr 2382, -4320), (Sum.inr 2388, -4320), (Sum.inr 2400, -4320), (Sum.inr 2452, -4320), (Sum.inr 2459, -4320), (Sum.inr 2479, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2694, -4320), (Sum.inr 2705, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 3340, -4320), (Sum.inr 3344, -4320), (Sum.inr 3354, -4320), (Sum.inr 3429, -4320), (Sum.inr 3433, -4320), (Sum.inr 3459, -4320), (Sum.inr 3493, -4320), (Sum.inr 3498, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3603, -4320), (Sum.inr 3622, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320)]

theorem reindexCheck512 : Integer.Sparse.reindex keyMap MixedData.row512 = numericRow512 := by decide +kernel

theorem numericCheck512 (x : Master → ℝ) : Integer.Sparse.eval numericRow512 x =
    (17280 : ℝ) * reducedSource512 x := by
  norm_num [numericRow512, reducedSource512, Integer.Sparse.eval, Sparse.eval, nodeValue4396, nodeValue4398, nodeValue4404, nodeValue4419, nodeValue4457, nodeValue4779, nodeValue4788, nodeValue4804, nodeValue4832, nodeValue4996, nodeValue5003, nodeValue5015, nodeValue5050, nodeValue5056, nodeValue5072, nodeValue5134, nodeValue5141, nodeValue5168, nodeValue5241, nodeValue5248, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5424, nodeValue5428, nodeValue5434, nodeValue5439, nodeValue5490]
  ring

noncomputable def reducedSource513 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + 0)))))))))))))))))))))))))))))

def numericRow513 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, 1), (Sum.inl 2, -15), (Sum.inl 7, -16), (Sum.inl 3, -48), (Sum.inl 4, -32), (Sum.inl 1, -12), (Sum.inr 977, 864), (Sum.inr 979, 864), (Sum.inr 985, 864), (Sum.inr 1000, 864), (Sum.inr 1040, 864), (Sum.inr 1987, 864), (Sum.inr 2003, 864), (Sum.inr 2022, 864), (Sum.inr 2193, 864), (Sum.inr 2382, 864), (Sum.inr 2388, 864), (Sum.inr 2400, 864), (Sum.inr 2452, 864), (Sum.inr 2459, 864), (Sum.inr 2479, 864), (Sum.inr 2553, 864), (Sum.inr 2561, 864), (Sum.inr 2694, 864), (Sum.inr 2705, 864), (Sum.inr 2721, 864), (Sum.inr 2722, 864), (Sum.inr 2723, 864), (Sum.inr 2739, 864), (Sum.inr 3838, 864), (Sum.inr 3845, 864), (Sum.inr 3902, 864)]

theorem reindexCheck513 : Integer.Sparse.reindex keyMap MixedData.row513 = numericRow513 := by decide +kernel

theorem numericCheck513 (x : Master → ℝ) : Integer.Sparse.eval numericRow513 x =
    (864 : ℝ) * reducedSource513 x := by
  norm_num [numericRow513, reducedSource513, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue979, nodeValue985, nodeValue1000, nodeValue1040, nodeValue1987, nodeValue2003, nodeValue2022, nodeValue2193, nodeValue2382, nodeValue2388, nodeValue2400, nodeValue2452, nodeValue2459, nodeValue2479, nodeValue2553, nodeValue2561, nodeValue2594, nodeValue2694, nodeValue2705, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2739, nodeValue2766, nodeValue3838, nodeValue3845, nodeValue3852, nodeValue3902, nodeValue4013]
  ring

noncomputable def reducedSource514 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue5133 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0)))))))))))))))))))))))))))

def numericRow514 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2019, -2160), (Sum.inr 2022, -2160), (Sum.inr 2028, -2160), (Sum.inr 2190, -2160), (Sum.inr 2203, -2160), (Sum.inr 2215, -2160), (Sum.inr 2672, -2160), (Sum.inr 2694, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 2765, -2160), (Sum.inr 3391, -2160), (Sum.inr 3493, -2160), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3582, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 5140, 8640), (Sum.inr 5161, 8640), (Sum.inr 5219, 8640), (Sum.inr 5232, 8640), (Sum.inr 5243, 8640), (Sum.inr 5249, 8640), (Sum.inr 5251, 8640), (Sum.inr 5260, 8640), (Sum.inr 5264, 8640), (Sum.inr 5266, 8640), (Sum.inr 5267, 8640)]

theorem reindexCheck514 : Integer.Sparse.reindex keyMap MixedData.row514 = numericRow514 := by decide +kernel

theorem numericCheck514 (x : Master → ℝ) : Integer.Sparse.eval numericRow514 x =
    (8640 : ℝ) * reducedSource514 x := by
  norm_num [numericRow514, reducedSource514, Integer.Sparse.eval, Sparse.eval, nodeValue4801, nodeValue4804, nodeValue4810, nodeValue4834, nodeValue4894, nodeValue5133, nodeValue5140, nodeValue5161, nodeValue5219, nodeValue5228, nodeValue5232, nodeValue5241, nodeValue5243, nodeValue5249, nodeValue5250, nodeValue5251, nodeValue5258, nodeValue5259, nodeValue5260, nodeValue5264, nodeValue5266, nodeValue5267, nodeValue5272, nodeValue5274, nodeValue5291, nodeValue5293, nodeValue5294, nodeValue5308]
  ring

noncomputable def reducedSource515 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))))))))))

def numericRow515 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 29), (Sum.inl 3, 16), (Sum.inl 1, 32), (Sum.inr 2190, 864), (Sum.inr 2203, 864), (Sum.inr 2215, 864), (Sum.inr 2661, 864), (Sum.inr 2670, 864), (Sum.inr 2672, 864), (Sum.inr 2677, 864), (Sum.inr 2694, 864), (Sum.inr 2697, 864), (Sum.inr 2708, 864), (Sum.inr 2719, 864), (Sum.inr 2722, 1728), (Sum.inr 2723, 864), (Sum.inr 2729, 864), (Sum.inr 2731, 864), (Sum.inr 2740, 864), (Sum.inr 2765, 864), (Sum.inr 3038, 864), (Sum.inr 3064, 864), (Sum.inr 3086, 864)]

theorem reindexCheck515 : Integer.Sparse.reindex keyMap MixedData.row515 = numericRow515 := by decide +kernel

theorem numericCheck515 (x : Master → ℝ) : Integer.Sparse.eval numericRow515 x =
    (864 : ℝ) * reducedSource515 x := by
  norm_num [numericRow515, reducedSource515, Integer.Sparse.eval, Sparse.eval, nodeValue2190, nodeValue2203, nodeValue2205, nodeValue2215, nodeValue2264, nodeValue2661, nodeValue2670, nodeValue2672, nodeValue2677, nodeValue2693, nodeValue2694, nodeValue2697, nodeValue2708, nodeValue2709, nodeValue2719, nodeValue2722, nodeValue2723, nodeValue2729, nodeValue2731, nodeValue2740, nodeValue2742, nodeValue2765, nodeValue2767, nodeValue2786, nodeValue3038, nodeValue3064, nodeValue3086, nodeValue3088, nodeValue3101]
  ring

noncomputable def reducedSource516 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2940 x + ((1 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))))))))))

def numericRow516 : Integer.Sparse Master := [(Sum.inl 0, -220), (Sum.inl 2, 270), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 1, 290), (Sum.inr 2710, 2160), (Sum.inr 2723, 2160), (Sum.inr 2724, 2160), (Sum.inr 2732, 2160), (Sum.inr 2942, 2160), (Sum.inr 2964, 2160), (Sum.inr 3030, 2160), (Sum.inr 3039, 2160), (Sum.inr 3040, 2160), (Sum.inr 3045, 2160), (Sum.inr 3066, 2160), (Sum.inr 3069, 2160)]

theorem reindexCheck516 : Integer.Sparse.reindex keyMap MixedData.row516 = numericRow516 := by decide +kernel

theorem numericCheck516 (x : Master → ℝ) : Integer.Sparse.eval numericRow516 x =
    (2160 : ℝ) * reducedSource516 x := by
  norm_num [numericRow516, reducedSource516, Integer.Sparse.eval, Sparse.eval, nodeValue2710, nodeValue2723, nodeValue2724, nodeValue2732, nodeValue2768, nodeValue2940, nodeValue2941, nodeValue2942, nodeValue2964, nodeValue3030, nodeValue3039, nodeValue3040, nodeValue3045, nodeValue3065, nodeValue3066, nodeValue3069, nodeValue3081, nodeValue3088, nodeValue3089, nodeValue3094, nodeValue3102, nodeValue3103, nodeValue3112, nodeValue3113, nodeValue3124, nodeValue3205, nodeValue3206, nodeValue3214, nodeValue3230]
  ring

noncomputable def reducedSource517 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow517 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 3533, 1), (Sum.inr 4084, -1)]

theorem reindexCheck517 : Integer.Sparse.reindex keyMap MixedData.row517 = numericRow517 := by decide +kernel

theorem numericCheck517 (x : Master → ℝ) : Integer.Sparse.eval numericRow517 x =
    (1 : ℝ) * reducedSource517 x := by
  norm_num [numericRow517, reducedSource517, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue2022, nodeValue2028, nodeValue2053, nodeValue2264, nodeValue3533, nodeValue4084]

noncomputable def reducedSource518 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((6 : ℝ) * Sparse.eval nodeValue5169 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((3 : ℝ) * Sparse.eval nodeValue5177 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((3 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((3 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

def numericRow518 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3309, -72), (Sum.inr 3310, -24), (Sum.inr 3312, -24), (Sum.inr 3607, -144), (Sum.inr 3615, -72), (Sum.inr 3616, -72), (Sum.inr 3627, -72), (Sum.inr 3634, -24)]

theorem reindexCheck518 : Integer.Sparse.reindex keyMap MixedData.row518 = numericRow518 := by decide +kernel

theorem numericCheck518 (x : Master → ℝ) : Integer.Sparse.eval numericRow518 x =
    (96 : ℝ) * reducedSource518 x := by
  norm_num [numericRow518, reducedSource518, Integer.Sparse.eval, Sparse.eval, nodeValue4093, nodeValue4624, nodeValue4625, nodeValue4628, nodeValue5169, nodeValue5174, nodeValue5177, nodeValue5293, nodeValue5296, nodeValue5307, nodeValue5309, nodeValue5442, nodeValue5455]
  ring

noncomputable def reducedSource519 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((6 : ℝ) * Sparse.eval nodeValue5168 x + ((3 : ℝ) * Sparse.eval nodeValue5171 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((3 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + ((3 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

def numericRow519 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3308, -90), (Sum.inr 3310, -30), (Sum.inr 3311, -30), (Sum.inr 3603, -180), (Sum.inr 3608, -90), (Sum.inr 3614, -90), (Sum.inr 3623, -90), (Sum.inr 3633, -30)]

theorem reindexCheck519 : Integer.Sparse.reindex keyMap MixedData.row519 = numericRow519 := by decide +kernel

theorem numericCheck519 (x : Master → ℝ) : Integer.Sparse.eval numericRow519 x =
    (120 : ℝ) * reducedSource519 x := by
  norm_num [numericRow519, reducedSource519, Integer.Sparse.eval, Sparse.eval, nodeValue4094, nodeValue4623, nodeValue4625, nodeValue4627, nodeValue5168, nodeValue5171, nodeValue5176, nodeValue5306, nodeValue5308, nodeValue5310, nodeValue5312, nodeValue5441, nodeValue5455]
  ring

noncomputable def reducedSource520 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((6 : ℝ) * Sparse.eval nodeValue5161 x + ((3 : ℝ) * Sparse.eval nodeValue5175 x + ((3 : ℝ) * Sparse.eval nodeValue5272 x + ((3 : ℝ) * Sparse.eval nodeValue5291 x + ((3 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

def numericRow520 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1297, -144), (Sum.inr 2109, -432), (Sum.inr 2261, -432), (Sum.inr 2289, -144), (Sum.inr 2740, -864), (Sum.inr 2765, -432), (Sum.inr 3582, -432), (Sum.inr 3633, -144), (Sum.inr 4617, 1728), (Sum.inr 4626, 576), (Sum.inr 5161, 3456), (Sum.inr 5175, 1728), (Sum.inr 5295, 1728), (Sum.inr 5311, 576)]

theorem reindexCheck520 : Integer.Sparse.reindex keyMap MixedData.row520 = numericRow520 := by decide +kernel

theorem numericCheck520 (x : Master → ℝ) : Integer.Sparse.eval numericRow520 x =
    (576 : ℝ) * reducedSource520 x := by
  norm_num [numericRow520, reducedSource520, Integer.Sparse.eval, Sparse.eval, nodeValue4617, nodeValue4621, nodeValue4626, nodeValue4868, nodeValue4897, nodeValue5161, nodeValue5175, nodeValue5272, nodeValue5291, nodeValue5295, nodeValue5308, nodeValue5310, nodeValue5311]
  ring

noncomputable def reducedSource521 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((6 : ℝ) * Sparse.eval nodeValue2964 x + ((3 : ℝ) * Sparse.eval nodeValue2966 x + ((3 : ℝ) * Sparse.eval nodeValue2967 x + ((3 : ℝ) * Sparse.eval nodeValue3103 x + ((3 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))

def numericRow521 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 2, 40), (Sum.inl 26, 160), (Sum.inl 1, 30), (Sum.inr 1306, 1440), (Sum.inr 1310, 480), (Sum.inr 2769, 1440), (Sum.inr 2789, 480), (Sum.inr 2964, 2880), (Sum.inr 2967, 1440)]

theorem reindexCheck521 : Integer.Sparse.reindex keyMap MixedData.row521 = numericRow521 := by decide +kernel

theorem numericCheck521 (x : Master → ℝ) : Integer.Sparse.eval numericRow521 x =
    (480 : ℝ) * reducedSource521 x := by
  norm_num [numericRow521, reducedSource521, Integer.Sparse.eval, Sparse.eval, nodeValue1306, nodeValue1308, nodeValue1310, nodeValue2769, nodeValue2788, nodeValue2789, nodeValue2964, nodeValue2966, nodeValue2967, nodeValue3103, nodeValue3113, nodeValue3114, nodeValue3124]
  ring

noncomputable def reducedSource522 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((6 : ℝ) * Sparse.eval nodeValue2719 x + ((3 : ℝ) * Sparse.eval nodeValue2737 x + ((3 : ℝ) * Sparse.eval nodeValue2740 x + ((3 : ℝ) * Sparse.eval nodeValue2761 x + ((3 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

def numericRow522 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, -2), (Sum.inr 2261, 432), (Sum.inr 2289, 144), (Sum.inr 2719, 864), (Sum.inr 2737, 432), (Sum.inr 2740, 432), (Sum.inr 2761, 432), (Sum.inr 2765, 432), (Sum.inr 2780, 144), (Sum.inr 2789, 144), (Sum.inr 3098, 432)]

theorem reindexCheck522 : Integer.Sparse.reindex keyMap MixedData.row522 = numericRow522 := by decide +kernel

theorem numericCheck522 (x : Master → ℝ) : Integer.Sparse.eval numericRow522 x =
    (144 : ℝ) * reducedSource522 x := by
  norm_num [numericRow522, reducedSource522, Integer.Sparse.eval, Sparse.eval, nodeValue2261, nodeValue2289, nodeValue2292, nodeValue2719, nodeValue2737, nodeValue2740, nodeValue2761, nodeValue2765, nodeValue2780, nodeValue2786, nodeValue2789, nodeValue3098, nodeValue3121]
  ring

noncomputable def reducedSource523 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4493 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue5094 x + ((6 : ℝ) * Sparse.eval nodeValue5110 x + ((6 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0)))))))

def numericRow523 : Integer.Sparse Master := [(Sum.inl 0, 12), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -5), (Sum.inr 1074, -2160), (Sum.inr 1077, -720), (Sum.inr 1094, -720), (Sum.inr 1650, -2160), (Sum.inr 1741, -720), (Sum.inr 2504, -4320), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2782, -2160), (Sum.inr 3583, -2160), (Sum.inr 3633, -720)]

theorem reindexCheck523 : Integer.Sparse.reindex keyMap MixedData.row523 = numericRow523 := by decide +kernel

theorem numericCheck523 (x : Master → ℝ) : Integer.Sparse.eval numericRow523 x =
    (1440 : ℝ) * reducedSource523 x := by
  norm_num [numericRow523, reducedSource523, Integer.Sparse.eval, Sparse.eval, nodeValue4490, nodeValue4493, nodeValue4510, nodeValue5094, nodeValue5110, nodeValue5304, nodeValue5310, nodeValue5494]
  ring

noncomputable def reducedSource524 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5135 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

def numericRow524 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 50), (Sum.inr 1246, -2160), (Sum.inr 2512, -4320), (Sum.inr 2519, -2160), (Sum.inr 2561, -4320), (Sum.inr 2739, -4320), (Sum.inr 2782, -2160), (Sum.inr 3301, -2160), (Sum.inr 3471, -4320), (Sum.inr 3486, -2160), (Sum.inr 3522, -4320), (Sum.inr 3534, -4320), (Sum.inr 3583, -2160), (Sum.inr 3845, -8640), (Sum.inr 3907, -2160), (Sum.inr 4603, 17280), (Sum.inr 4609, 8640), (Sum.inr 4620, 8640), (Sum.inr 5139, 17280), (Sum.inr 5164, 17280), (Sum.inr 5266, 17280), (Sum.inr 5268, 8640), (Sum.inr 5300, 8640)]

theorem reindexCheck524 : Integer.Sparse.reindex keyMap MixedData.row524 = numericRow524 := by decide +kernel

theorem numericCheck524 (x : Master → ℝ) : Integer.Sparse.eval numericRow524 x =
    (8640 : ℝ) * reducedSource524 x := by
  norm_num [numericRow524, reducedSource524, Integer.Sparse.eval, Sparse.eval, nodeValue4603, nodeValue4609, nodeValue4612, nodeValue4620, nodeValue5102, nodeValue5109, nodeValue5111, nodeValue5135, nodeValue5139, nodeValue5141, nodeValue5164, nodeValue5266, nodeValue5268, nodeValue5271, nodeValue5274, nodeValue5300, nodeValue5304, nodeValue5413, nodeValue5428, nodeValue5442, nodeValue5443]
  ring

noncomputable def reducedSource525 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2934 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue2998 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((2 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

def numericRow525 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 1262, 1080), (Sum.inr 1264, 540), (Sum.inr 1295, 540), (Sum.inr 2618, 1080), (Sum.inr 2734, 540), (Sum.inr 2955, 1080), (Sum.inr 3039, 1080), (Sum.inr 3055, 540)]

theorem reindexCheck525 : Integer.Sparse.reindex keyMap MixedData.row525 = numericRow525 := by decide +kernel

theorem numericCheck525 (x : Master → ℝ) : Integer.Sparse.eval numericRow525 x =
    (540 : ℝ) * reducedSource525 x := by
  norm_num [numericRow525, reducedSource525, Integer.Sparse.eval, Sparse.eval, nodeValue1262, nodeValue1264, nodeValue1274, nodeValue1295, nodeValue2618, nodeValue2640, nodeValue2734, nodeValue2934, nodeValue2943, nodeValue2955, nodeValue2998, nodeValue3006, nodeValue3039, nodeValue3055, nodeValue3109, nodeValue3112, nodeValue3119, nodeValue3889, nodeValue4001, nodeValue4003, nodeValue4006]
  ring

noncomputable def reducedSource526 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3515 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

def numericRow526 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 3294, 4320), (Sum.inr 3301, 2160), (Sum.inr 3302, 2160), (Sum.inr 3306, 2160), (Sum.inr 3471, 4320), (Sum.inr 3486, 2160), (Sum.inr 3522, 4320), (Sum.inr 3523, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3549, 2160), (Sum.inr 3565, 4320), (Sum.inr 3583, 2160), (Sum.inr 3584, 2160), (Sum.inr 3845, 4320)]

theorem reindexCheck526 : Integer.Sparse.reindex keyMap MixedData.row526 = numericRow526 := by decide +kernel

theorem numericCheck526 (x : Master → ℝ) : Integer.Sparse.eval numericRow526 x =
    (2160 : ℝ) * reducedSource526 x := by
  norm_num [numericRow526, reducedSource526, Integer.Sparse.eval, Sparse.eval, nodeValue3294, nodeValue3301, nodeValue3302, nodeValue3306, nodeValue3471, nodeValue3485, nodeValue3486, nodeValue3515, nodeValue3522, nodeValue3523, nodeValue3534, nodeValue3535, nodeValue3547, nodeValue3549, nodeValue3565, nodeValue3583, nodeValue3584, nodeValue3817, nodeValue3845, nodeValue3861, nodeValue3862]
  ring

noncomputable def reducedSource527 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3908 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow527 : Integer.Sparse Master := [(Sum.inr 2743, 1), (Sum.inr 3845, 2), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem reindexCheck527 : Integer.Sparse.reindex keyMap MixedData.row527 = numericRow527 := by decide +kernel

theorem numericCheck527 (x : Master → ℝ) : Integer.Sparse.eval numericRow527 x =
    (1 : ℝ) * reducedSource527 x := by
  norm_num [numericRow527, reducedSource527, Integer.Sparse.eval, Sparse.eval, nodeValue2743, nodeValue3817, nodeValue3845, nodeValue3907, nodeValue3908, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
