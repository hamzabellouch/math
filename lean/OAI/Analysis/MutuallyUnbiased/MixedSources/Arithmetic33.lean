import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
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

noncomputable def reducedSource528 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow528 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 2591, 1), (Sum.inr 2743, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

theorem reindexCheck528 : Integer.Sparse.reindex keyMap MixedData.row528 = numericRow528 := by decide +kernel

theorem numericCheck528 (x : Master → ℝ) : Integer.Sparse.eval numericRow528 x =
    (1 : ℝ) * reducedSource528 x := by
  norm_num [numericRow528, reducedSource528, Integer.Sparse.eval, Sparse.eval, nodeValue2554, nodeValue2558, nodeValue2561, nodeValue2591, nodeValue2743, nodeValue3845, nodeValue4092]

noncomputable def reducedSource529 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow529 : Integer.Sparse Master := [(Sum.inr 2512, 2), (Sum.inr 2519, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem reindexCheck529 : Integer.Sparse.reindex keyMap MixedData.row529 = numericRow529 := by decide +kernel

theorem numericCheck529 (x : Master → ℝ) : Integer.Sparse.eval numericRow529 x =
    (1 : ℝ) * reducedSource529 x := by
  norm_num [numericRow529, reducedSource529, Integer.Sparse.eval, Sparse.eval, nodeValue2512, nodeValue2519, nodeValue2523, nodeValue2743, nodeValue3817, nodeValue4092]

noncomputable def reducedSource530 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow530 : Integer.Sparse Master := [(Sum.inr 1246, 1), (Sum.inr 2561, 2), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem reindexCheck530 : Integer.Sparse.reindex keyMap MixedData.row530 = numericRow530 := by decide +kernel

theorem numericCheck530 (x : Master → ℝ) : Integer.Sparse.eval numericRow530 x =
    (1 : ℝ) * reducedSource530 x := by
  norm_num [numericRow530, reducedSource530, Integer.Sparse.eval, Sparse.eval, nodeValue1246, nodeValue2523, nodeValue2561, nodeValue2742, nodeValue2743, nodeValue4092]

noncomputable def reducedSource531 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((2 : ℝ) * Sparse.eval nodeValue5014 x + ((2 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((1 : ℝ) * Sparse.eval nodeValue5023 x + ((2 : ℝ) * Sparse.eval nodeValue5059 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

def numericRow531 : Integer.Sparse Master := [(Sum.inl 0, 137), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 290), (Sum.inr 1005, -4320), (Sum.inr 1009, -2160), (Sum.inr 1012, -2160), (Sum.inr 1083, -2160), (Sum.inr 1623, -4320), (Sum.inr 1627, -2160), (Sum.inr 1630, -2160), (Sum.inr 1728, -2160), (Sum.inr 2385, -4320), (Sum.inr 2399, -4320), (Sum.inr 2404, -4320), (Sum.inr 2407, -2160), (Sum.inr 2410, -4320), (Sum.inr 2462, -4320), (Sum.inr 2467, -4320), (Sum.inr 2512, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -2160), (Sum.inr 2739, -4320), (Sum.inr 2740, -4320), (Sum.inr 3353, -4320), (Sum.inr 3357, -4320), (Sum.inr 3360, -2160), (Sum.inr 3436, -4320), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -2160), (Sum.inr 3623, -2160), (Sum.inr 3627, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3963, -4320)]

theorem reindexCheck531 : Integer.Sparse.reindex keyMap MixedData.row531 = numericRow531 := by decide +kernel

theorem numericCheck531 (x : Master → ℝ) : Integer.Sparse.eval numericRow531 x =
    (8640 : ℝ) * reducedSource531 x := by
  norm_num [numericRow531, reducedSource531, Integer.Sparse.eval, Sparse.eval, nodeValue4424, nodeValue4428, nodeValue4431, nodeValue4499, nodeValue5000, nodeValue5014, nodeValue5018, nodeValue5021, nodeValue5023, nodeValue5059, nodeValue5102, nodeValue5259, nodeValue5261, nodeValue5271, nodeValue5272, nodeValue5293, nodeValue5306, nodeValue5473, nodeValue5475, nodeValue5491, nodeValue5492]
  ring

noncomputable def reducedSource532 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2385 x + ((2 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((1 : ℝ) * Sparse.eval nodeValue2410 x + ((2 : ℝ) * Sparse.eval nodeValue2462 x + ((2 : ℝ) * Sparse.eval nodeValue2467 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4015 x + 0))))))))))))))))))))

def numericRow532 : Integer.Sparse Master := [(Sum.inl 0, -18), (Sum.inl 2, 5), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, -37), (Sum.inr 1005, 864), (Sum.inr 1009, 432), (Sum.inr 1012, 432), (Sum.inr 1083, 432), (Sum.inr 2385, 864), (Sum.inr 2404, 864), (Sum.inr 2407, 432), (Sum.inr 2410, 432), (Sum.inr 2462, 864), (Sum.inr 2467, 864), (Sum.inr 2512, 864), (Sum.inr 2723, 864), (Sum.inr 2726, 432), (Sum.inr 2739, 864), (Sum.inr 2740, 432), (Sum.inr 3958, 864), (Sum.inr 3963, 432)]

theorem reindexCheck532 : Integer.Sparse.reindex keyMap MixedData.row532 = numericRow532 := by decide +kernel

theorem numericCheck532 (x : Master → ℝ) : Integer.Sparse.eval numericRow532 x =
    (432 : ℝ) * reducedSource532 x := by
  norm_num [numericRow532, reducedSource532, Integer.Sparse.eval, Sparse.eval, nodeValue1005, nodeValue1009, nodeValue1012, nodeValue1083, nodeValue2385, nodeValue2404, nodeValue2407, nodeValue2410, nodeValue2462, nodeValue2467, nodeValue2512, nodeValue2723, nodeValue2726, nodeValue2739, nodeValue2740, nodeValue2767, nodeValue2784, nodeValue3958, nodeValue3963, nodeValue4014, nodeValue4015]
  ring

noncomputable def reducedSource533 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5242 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

def numericRow533 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inr 2054, -1440), (Sum.inr 2062, -720), (Sum.inr 2206, -1440), (Sum.inr 2230, -720), (Sum.inr 2686, -720), (Sum.inr 2705, -1440), (Sum.inr 2723, -1440), (Sum.inr 2743, -1440), (Sum.inr 2765, -720), (Sum.inr 3397, -720), (Sum.inr 3498, -1440), (Sum.inr 3544, -1440), (Sum.inr 3548, -1440), (Sum.inr 3582, -720), (Sum.inr 3627, -720), (Sum.inr 3633, -720), (Sum.inr 5205, 5760), (Sum.inr 5206, 2880), (Sum.inr 5229, 5760), (Sum.inr 5260, 5760), (Sum.inr 5276, 2880), (Sum.inr 5282, 5760), (Sum.inr 5300, 2880)]

theorem reindexCheck533 : Integer.Sparse.reindex keyMap MixedData.row533 = numericRow533 := by decide +kernel

theorem numericCheck533 (x : Master → ℝ) : Integer.Sparse.eval numericRow533 x =
    (2880 : ℝ) * reducedSource533 x := by
  norm_num [numericRow533, reducedSource533, Integer.Sparse.eval, Sparse.eval, nodeValue4835, nodeValue4843, nodeValue4846, nodeValue4901, nodeValue5205, nodeValue5206, nodeValue5229, nodeValue5238, nodeValue5242, nodeValue5248, nodeValue5259, nodeValue5260, nodeValue5274, nodeValue5275, nodeValue5276, nodeValue5282, nodeValue5291, nodeValue5293, nodeValue5300, nodeValue5309, nodeValue5310]
  ring

noncomputable def reducedSource534 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2695 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((2 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + 0))))))))))))))))))))

def numericRow534 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, 120), (Sum.inl 3, -320), (Sum.inl 26, 160), (Sum.inl 1, 50), (Sum.inr 2206, 8640), (Sum.inr 2230, 4320), (Sum.inr 2673, 8640), (Sum.inr 2686, 4320), (Sum.inr 2687, 4320), (Sum.inr 2705, 8640), (Sum.inr 2706, 8640), (Sum.inr 2723, 8640), (Sum.inr 2724, 8640), (Sum.inr 2743, 8640), (Sum.inr 2744, 4320), (Sum.inr 3055, 4320), (Sum.inr 3078, 8640)]

theorem reindexCheck534 : Integer.Sparse.reindex keyMap MixedData.row534 = numericRow534 := by decide +kernel

theorem numericCheck534 (x : Master → ℝ) : Integer.Sparse.eval numericRow534 x =
    (4320 : ℝ) * reducedSource534 x := by
  norm_num [numericRow534, reducedSource534, Integer.Sparse.eval, Sparse.eval, nodeValue2206, nodeValue2229, nodeValue2230, nodeValue2293, nodeValue2673, nodeValue2686, nodeValue2687, nodeValue2695, nodeValue2705, nodeValue2706, nodeValue2723, nodeValue2724, nodeValue2742, nodeValue2743, nodeValue2744, nodeValue2787, nodeValue2788, nodeValue3055, nodeValue3078, nodeValue3102, nodeValue3103]
  ring

noncomputable def reducedSource535 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2066 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow535 : Integer.Sparse Master := [(Sum.inr 2054, 2), (Sum.inr 2062, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem reindexCheck535 : Integer.Sparse.reindex keyMap MixedData.row535 = numericRow535 := by decide +kernel

theorem numericCheck535 (x : Master → ℝ) : Integer.Sparse.eval numericRow535 x =
    (1 : ℝ) * reducedSource535 x := by
  norm_num [numericRow535, reducedSource535, Integer.Sparse.eval, Sparse.eval, nodeValue2054, nodeValue2062, nodeValue2066, nodeValue2293, nodeValue3548, nodeValue4084]

noncomputable def reducedSource536 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0))))))))))))))))))))

def numericRow536 : Integer.Sparse Master := [(Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2482, -2), (Sum.inr 2553, -2), (Sum.inr 2561, -2), (Sum.inr 2590, -2), (Sum.inr 2722, -2), (Sum.inr 2726, -1), (Sum.inr 2739, -2), (Sum.inr 2743, -1), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -2), (Sum.inr 3514, -2), (Sum.inr 3522, -2), (Sum.inr 3533, -2), (Sum.inr 3534, -2), (Sum.inr 3545, -1), (Sum.inr 3548, -1), (Sum.inr 3564, -2), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 4092, 4)]

theorem reindexCheck536 : Integer.Sparse.reindex keyMap MixedData.row536 = numericRow536 := by decide +kernel

theorem numericCheck536 (x : Master → ℝ) : Integer.Sparse.eval numericRow536 x =
    (4 : ℝ) * reducedSource536 x := by
  norm_num [numericRow536, reducedSource536, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4602, nodeValue4608, nodeValue4612, nodeValue4619, nodeValue5075, nodeValue5101, nodeValue5107, nodeValue5111, nodeValue5134, nodeValue5141, nodeValue5163, nodeValue5258, nodeValue5261, nodeValue5271, nodeValue5275, nodeValue5291, nodeValue5304, nodeValue5409, nodeValue5441, nodeValue5442]
  ring

noncomputable def reducedSource537 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5241 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))))))))))

def numericRow537 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2509, -4320), (Sum.inr 2522, -2160), (Sum.inr 2672, -4320), (Sum.inr 2685, -2160), (Sum.inr 2686, -2160), (Sum.inr 2694, -4320), (Sum.inr 2704, -4320), (Sum.inr 2705, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 2743, -2160), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3493, -4320), (Sum.inr 3498, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3548, -2160), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4084, 8640)]

theorem reindexCheck537 : Integer.Sparse.reindex keyMap MixedData.row537 = numericRow537 := by decide +kernel

theorem numericCheck537 (x : Master → ℝ) : Integer.Sparse.eval numericRow537 x =
    (8640 : ℝ) * reducedSource537 x := by
  norm_num [numericRow537, reducedSource537, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4834, nodeValue4841, nodeValue4846, nodeValue5099, nodeValue5110, nodeValue5228, nodeValue5238, nodeValue5241, nodeValue5248, nodeValue5258, nodeValue5259, nodeValue5272, nodeValue5274, nodeValue5275, nodeValue5284, nodeValue5293, nodeValue5294, nodeValue5302, nodeValue5308, nodeValue5309]
  ring

noncomputable def reducedSource538 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4600 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5133 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))))))))))

def numericRow538 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1239, -2160), (Sum.inr 2022, -4320), (Sum.inr 2203, -4320), (Sum.inr 2226, -2160), (Sum.inr 2509, -4320), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2704, -4320), (Sum.inr 2722, -4320), (Sum.inr 2740, -8640), (Sum.inr 2783, -4320), (Sum.inr 3533, -4320), (Sum.inr 3632, -2160), (Sum.inr 4600, 17280), (Sum.inr 4611, 8640), (Sum.inr 4617, 8640), (Sum.inr 5140, 17280), (Sum.inr 5161, 17280), (Sum.inr 5270, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640)]

theorem reindexCheck538 : Integer.Sparse.reindex keyMap MixedData.row538 = numericRow538 := by decide +kernel

theorem numericCheck538 (x : Master → ℝ) : Integer.Sparse.eval numericRow538 x =
    (8640 : ℝ) * reducedSource538 x := by
  norm_num [numericRow538, reducedSource538, Integer.Sparse.eval, Sparse.eval, nodeValue4600, nodeValue4605, nodeValue4611, nodeValue4617, nodeValue4804, nodeValue4841, nodeValue4897, nodeValue5099, nodeValue5110, nodeValue5133, nodeValue5140, nodeValue5161, nodeValue5258, nodeValue5270, nodeValue5272, nodeValue5274, nodeValue5276, nodeValue5294, nodeValue5295, nodeValue5305, nodeValue5308]
  ring

noncomputable def reducedSource539 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((2 : ℝ) * Sparse.eval nodeValue2940 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((2 : ℝ) * Sparse.eval nodeValue2942 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((2 : ℝ) * Sparse.eval nodeValue3003 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((2 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))))))))))

def numericRow539 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, 140), (Sum.inl 26, -160), (Sum.inl 1, 150), (Sum.inr 1270, 2160), (Sum.inr 1273, 1080), (Sum.inr 1306, 1080), (Sum.inr 2754, 2160), (Sum.inr 2769, 1080), (Sum.inr 2777, 1080), (Sum.inr 2942, 2160), (Sum.inr 2964, 2160)]

theorem reindexCheck539 : Integer.Sparse.reindex keyMap MixedData.row539 = numericRow539 := by decide +kernel

theorem numericCheck539 (x : Master → ℝ) : Integer.Sparse.eval numericRow539 x =
    (1080 : ℝ) * reducedSource539 x := by
  norm_num [numericRow539, reducedSource539, Integer.Sparse.eval, Sparse.eval, nodeValue1270, nodeValue1271, nodeValue1273, nodeValue1306, nodeValue2754, nodeValue2768, nodeValue2769, nodeValue2777, nodeValue2940, nodeValue2941, nodeValue2942, nodeValue2964, nodeValue3003, nodeValue3004, nodeValue3005, nodeValue3089, nodeValue3112, nodeValue3113, nodeValue3114, nodeValue3124, nodeValue3125]
  ring

noncomputable def reducedSource540 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2693 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))

def numericRow540 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2203, 4320), (Sum.inr 2226, 2160), (Sum.inr 2670, 4320), (Sum.inr 2683, 2160), (Sum.inr 2685, 2160), (Sum.inr 2702, 4320), (Sum.inr 2704, 4320), (Sum.inr 2719, 4320), (Sum.inr 2722, 4320), (Sum.inr 2737, 2160), (Sum.inr 2740, 4320), (Sum.inr 2783, 2160), (Sum.inr 3052, 2160), (Sum.inr 3075, 4320), (Sum.inr 3098, 2160)]

theorem reindexCheck540 : Integer.Sparse.reindex keyMap MixedData.row540 = numericRow540 := by decide +kernel

theorem numericCheck540 (x : Master → ℝ) : Integer.Sparse.eval numericRow540 x =
    (2160 : ℝ) * reducedSource540 x := by
  norm_num [numericRow540, reducedSource540, Integer.Sparse.eval, Sparse.eval, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2292, nodeValue2670, nodeValue2683, nodeValue2685, nodeValue2693, nodeValue2702, nodeValue2704, nodeValue2719, nodeValue2722, nodeValue2737, nodeValue2740, nodeValue2742, nodeValue2783, nodeValue2786, nodeValue3052, nodeValue3075, nodeValue3098, nodeValue3101]
  ring

noncomputable def reducedSource541 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4421 x + ((2 : ℝ) * Sparse.eval nodeValue4431 x + ((2 : ℝ) * Sparse.eval nodeValue4496 x + ((4 : ℝ) * Sparse.eval nodeValue5014 x + ((1 : ℝ) * Sparse.eval nodeValue5023 x + ((2 : ℝ) * Sparse.eval nodeValue5055 x + ((4 : ℝ) * Sparse.eval nodeValue5099 x + ((4 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))

def numericRow541 : Integer.Sparse Master := [(Sum.inl 0, 42), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 95), (Sum.inr 999, -4320), (Sum.inr 1002, -2160), (Sum.inr 1012, -2160), (Sum.inr 1080, -2160), (Sum.inr 1602, -4320), (Sum.inr 1627, -2160), (Sum.inr 1710, -2160), (Sum.inr 2399, -4320), (Sum.inr 2410, -2160), (Sum.inr 2458, -4320), (Sum.inr 2467, -4320), (Sum.inr 2509, -4320), (Sum.inr 2704, -4320), (Sum.inr 2739, -4320), (Sum.inr 2740, -2160), (Sum.inr 2743, -2160), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3623, -2160)]

theorem reindexCheck541 : Integer.Sparse.reindex keyMap MixedData.row541 = numericRow541 := by decide +kernel

theorem numericCheck541 (x : Master → ℝ) : Integer.Sparse.eval numericRow541 x =
    (4320 : ℝ) * reducedSource541 x := by
  norm_num [numericRow541, reducedSource541, Integer.Sparse.eval, Sparse.eval, nodeValue4418, nodeValue4421, nodeValue4431, nodeValue4496, nodeValue5014, nodeValue5023, nodeValue5055, nodeValue5099, nodeValue5271, nodeValue5272, nodeValue5275, nodeValue5306, nodeValue5492]
  ring

noncomputable def reducedSource542 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((2 : ℝ) * Sparse.eval nodeValue4819 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))

def numericRow542 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1087, -2160), (Sum.inr 1739, -2160), (Sum.inr 2058, -4320), (Sum.inr 2216, -4320), (Sum.inr 2245, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -4320), (Sum.inr 2278, -4320), (Sum.inr 3054, -2160), (Sum.inr 3626, -2160), (Sum.inr 3632, -2160), (Sum.inr 4475, 17280), (Sum.inr 4478, 8640), (Sum.inr 4480, 8640), (Sum.inr 4816, 17280), (Sum.inr 4819, 17280), (Sum.inr 4821, 17280), (Sum.inr 4844, 8640), (Sum.inr 4880, 17280), (Sum.inr 4884, 8640), (Sum.inr 4891, 17280), (Sum.inr 4892, 8640), (Sum.inr 5267, 17280), (Sum.inr 5276, 8640)]

theorem reindexCheck542 : Integer.Sparse.reindex keyMap MixedData.row542 = numericRow542 := by decide +kernel

theorem numericCheck542 (x : Master → ℝ) : Integer.Sparse.eval numericRow542 x =
    (8640 : ℝ) * reducedSource542 x := by
  norm_num [numericRow542, reducedSource542, Integer.Sparse.eval, Sparse.eval, nodeValue4475, nodeValue4478, nodeValue4480, nodeValue4503, nodeValue4816, nodeValue4819, nodeValue4821, nodeValue4839, nodeValue4844, nodeValue4880, nodeValue4884, nodeValue4889, nodeValue4891, nodeValue4892, nodeValue4895, nodeValue4896, nodeValue5267, nodeValue5276, nodeValue5294, nodeValue5302]
  ring

noncomputable def reducedSource543 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((2 : ℝ) * Sparse.eval nodeValue2221 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + 0))))))))))))))))))))

def numericRow543 : Integer.Sparse Master := [(Sum.inl 0, -30), (Sum.inl 2, 35), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, 5), (Sum.inr 1715, 4320), (Sum.inr 1739, 2160), (Sum.inr 1740, 2160), (Sum.inr 1746, 2160), (Sum.inr 2196, 4320), (Sum.inr 2216, 4320), (Sum.inr 2217, 4320), (Sum.inr 2221, 4320), (Sum.inr 2222, 2160), (Sum.inr 2245, 4320), (Sum.inr 2253, 4320), (Sum.inr 2254, 4320), (Sum.inr 2266, 2160), (Sum.inr 2278, 2160), (Sum.inr 2280, 2160), (Sum.inr 2284, 2160), (Sum.inr 2732, 4320), (Sum.inr 2777, 2160)]

theorem reindexCheck543 : Integer.Sparse.reindex keyMap MixedData.row543 = numericRow543 := by decide +kernel

theorem numericCheck543 (x : Master → ℝ) : Integer.Sparse.eval numericRow543 x =
    (2160 : ℝ) * reducedSource543 x := by
  norm_num [numericRow543, reducedSource543, Integer.Sparse.eval, Sparse.eval, nodeValue1715, nodeValue1739, nodeValue1740, nodeValue1746, nodeValue2196, nodeValue2216, nodeValue2217, nodeValue2221, nodeValue2222, nodeValue2245, nodeValue2253, nodeValue2254, nodeValue2265, nodeValue2266, nodeValue2278, nodeValue2280, nodeValue2284, nodeValue2732, nodeValue2768, nodeValue2776, nodeValue2777]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
