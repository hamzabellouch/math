import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
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

noncomputable def reducedSource496 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow496 : Integer.Sparse Master := [(Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 2621, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

theorem reindexCheck496 : Integer.Sparse.reindex keyMap MixedData.row496 = numericRow496 := by decide +kernel

theorem numericCheck496 (x : Master → ℝ) : Integer.Sparse.eval numericRow496 x =
    (1 : ℝ) * reducedSource496 x := by
  norm_num [numericRow496, reducedSource496, Integer.Sparse.eval, Sparse.eval, nodeValue1220, nodeValue2489, nodeValue2546, nodeValue2621, nodeValue2723, nodeValue4091]

noncomputable def reducedSource497 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5018 x + ((1 : ℝ) * Sparse.eval nodeValue5047 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5059 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))))))))))))))))))))))))))

def numericRow497 : Integer.Sparse Master := [(Sum.inl 0, 438), (Sum.inl 6, -5), (Sum.inl 2, 55), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 170), (Sum.inr 980, -4320), (Sum.inr 982, -4320), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1041, -4320), (Sum.inr 1616, -4320), (Sum.inr 1617, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1724, -4320), (Sum.inr 2383, -4320), (Sum.inr 2385, -4320), (Sum.inr 2388, -4320), (Sum.inr 2404, -4320), (Sum.inr 2449, -4320), (Sum.inr 2452, -4320), (Sum.inr 2462, -4320), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 3352, -4320), (Sum.inr 3353, -4320), (Sum.inr 3354, -4320), (Sum.inr 3357, -4320), (Sum.inr 3432, -4320), (Sum.inr 3433, -4320), (Sum.inr 3436, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -4320), (Sum.inr 3548, -4320), (Sum.inr 3607, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320)]

theorem reindexCheck497 : Integer.Sparse.reindex keyMap MixedData.row497 = numericRow497 := by decide +kernel

theorem numericCheck497 (x : Master → ℝ) : Integer.Sparse.eval numericRow497 x =
    (17280 : ℝ) * reducedSource497 x := by
  norm_num [numericRow497, reducedSource497, Integer.Sparse.eval, Sparse.eval, nodeValue4399, nodeValue4401, nodeValue4404, nodeValue4424, nodeValue4458, nodeValue4998, nodeValue5000, nodeValue5003, nodeValue5018, nodeValue5047, nodeValue5050, nodeValue5059, nodeValue5073, nodeValue5075, nodeValue5137, nodeValue5141, nodeValue5169, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5261, nodeValue5271, nodeValue5275, nodeValue5292, nodeValue5293, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5490, nodeValue5491]
  ring

noncomputable def reducedSource498 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2404 x + ((1 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2462 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + 0)))))))))))))))))))))))))))))

def numericRow498 : Integer.Sparse Master := [(Sum.inl 0, -323), (Sum.inl 6, 5), (Sum.inl 2, -55), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -5), (Sum.inr 980, 4320), (Sum.inr 982, 4320), (Sum.inr 985, 4320), (Sum.inr 1005, 4320), (Sum.inr 1041, 4320), (Sum.inr 2383, 4320), (Sum.inr 2385, 4320), (Sum.inr 2388, 4320), (Sum.inr 2404, 4320), (Sum.inr 2449, 4320), (Sum.inr 2452, 4320), (Sum.inr 2462, 4320), (Sum.inr 2480, 4320), (Sum.inr 2482, 4320), (Sum.inr 2556, 4320), (Sum.inr 2561, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 4320), (Sum.inr 2723, 4320), (Sum.inr 2726, 4320), (Sum.inr 2739, 4320), (Sum.inr 2743, 4320), (Sum.inr 3958, 4320)]

theorem reindexCheck498 : Integer.Sparse.reindex keyMap MixedData.row498 = numericRow498 := by decide +kernel

theorem numericCheck498 (x : Master → ℝ) : Integer.Sparse.eval numericRow498 x =
    (4320 : ℝ) * reducedSource498 x := by
  norm_num [numericRow498, reducedSource498, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue982, nodeValue985, nodeValue1005, nodeValue1041, nodeValue2383, nodeValue2385, nodeValue2388, nodeValue2404, nodeValue2449, nodeValue2452, nodeValue2462, nodeValue2480, nodeValue2482, nodeValue2556, nodeValue2561, nodeValue2595, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2726, nodeValue2739, nodeValue2743, nodeValue2766, nodeValue2767, nodeValue3958, nodeValue3971, nodeValue3981, nodeValue4013, nodeValue4014]
  ring

noncomputable def reducedSource499 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((3 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))))))

def numericRow499 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -85), (Sum.inl 3, -80), (Sum.inl 1, -100), (Sum.inr 2051, -2160), (Sum.inr 2054, -2160), (Sum.inr 2058, -2160), (Sum.inr 2191, -2160), (Sum.inr 2206, -2160), (Sum.inr 2216, -2160), (Sum.inr 2672, -2160), (Sum.inr 2694, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -6480), (Sum.inr 2743, -2160), (Sum.inr 3391, -2160), (Sum.inr 3493, -2160), (Sum.inr 3533, -4320), (Sum.inr 3544, -6480), (Sum.inr 3548, -2160), (Sum.inr 3627, -4320), (Sum.inr 3632, -2160), (Sum.inr 5220, 8640), (Sum.inr 5229, 8640), (Sum.inr 5233, 8640), (Sum.inr 5244, 8640), (Sum.inr 5251, 8640), (Sum.inr 5260, 8640), (Sum.inr 5266, 17280), (Sum.inr 5267, 8640)]

theorem reindexCheck499 : Integer.Sparse.reindex keyMap MixedData.row499 = numericRow499 := by decide +kernel

theorem numericCheck499 (x : Master → ℝ) : Integer.Sparse.eval numericRow499 x =
    (8640 : ℝ) * reducedSource499 x := by
  norm_num [numericRow499, reducedSource499, Integer.Sparse.eval, Sparse.eval, nodeValue4831, nodeValue4834, nodeValue4835, nodeValue4839, nodeValue4895, nodeValue5220, nodeValue5228, nodeValue5229, nodeValue5233, nodeValue5241, nodeValue5242, nodeValue5244, nodeValue5250, nodeValue5251, nodeValue5258, nodeValue5259, nodeValue5260, nodeValue5266, nodeValue5267, nodeValue5274, nodeValue5275, nodeValue5293, nodeValue5294, nodeValue5309]
  ring

noncomputable def reducedSource500 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))))))))))

def numericRow500 : Integer.Sparse Master := [(Sum.inl 0, -394), (Sum.inl 2, 500), (Sum.inl 26, -160), (Sum.inl 1, 510), (Sum.inr 2191, 8640), (Sum.inr 2206, 8640), (Sum.inr 2216, 8640), (Sum.inr 2662, 8640), (Sum.inr 2672, 8640), (Sum.inr 2673, 8640), (Sum.inr 2678, 8640), (Sum.inr 2694, 8640), (Sum.inr 2698, 8640), (Sum.inr 2710, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 17280), (Sum.inr 2724, 8640), (Sum.inr 2731, 8640), (Sum.inr 2732, 8640), (Sum.inr 2743, 8640), (Sum.inr 3039, 8640)]

theorem reindexCheck500 : Integer.Sparse.reindex keyMap MixedData.row500 = numericRow500 := by decide +kernel

theorem numericCheck500 (x : Master → ℝ) : Integer.Sparse.eval numericRow500 x =
    (8640 : ℝ) * reducedSource500 x := by
  norm_num [numericRow500, reducedSource500, Integer.Sparse.eval, Sparse.eval, nodeValue2191, nodeValue2205, nodeValue2206, nodeValue2216, nodeValue2265, nodeValue2662, nodeValue2672, nodeValue2673, nodeValue2678, nodeValue2694, nodeValue2695, nodeValue2698, nodeValue2709, nodeValue2710, nodeValue2722, nodeValue2723, nodeValue2724, nodeValue2731, nodeValue2732, nodeValue2742, nodeValue2743, nodeValue2767, nodeValue2768, nodeValue2787, nodeValue3039, nodeValue3065, nodeValue3088, nodeValue3089, nodeValue3102]
  ring

noncomputable def reducedSource501 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3211 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))))))))))

def numericRow501 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 29), (Sum.inl 3, 16), (Sum.inl 1, 32), (Sum.inr 2722, 216), (Sum.inr 2723, 216), (Sum.inr 2731, 216), (Sum.inr 3029, 216), (Sum.inr 3038, 216), (Sum.inr 3039, 216), (Sum.inr 3044, 216), (Sum.inr 3064, 216), (Sum.inr 3068, 216), (Sum.inr 3086, 216), (Sum.inr 3092, 216)]

theorem reindexCheck501 : Integer.Sparse.reindex keyMap MixedData.row501 = numericRow501 := by decide +kernel

theorem numericCheck501 (x : Master → ℝ) : Integer.Sparse.eval numericRow501 x =
    (216 : ℝ) * reducedSource501 x := by
  norm_num [numericRow501, reducedSource501, Integer.Sparse.eval, Sparse.eval, nodeValue2709, nodeValue2722, nodeValue2723, nodeValue2731, nodeValue2767, nodeValue3029, nodeValue3038, nodeValue3039, nodeValue3044, nodeValue3064, nodeValue3065, nodeValue3068, nodeValue3080, nodeValue3081, nodeValue3086, nodeValue3088, nodeValue3089, nodeValue3092, nodeValue3094, nodeValue3101, nodeValue3102, nodeValue3110, nodeValue3112, nodeValue3123, nodeValue3209, nodeValue3210, nodeValue3211, nodeValue3214, nodeValue3229]
  ring

noncomputable def reducedSource502 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow502 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 2054, 1), (Sum.inr 2058, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem reindexCheck502 : Integer.Sparse.reindex keyMap MixedData.row502 = numericRow502 := by decide +kernel

theorem numericCheck502 (x : Master → ℝ) : Integer.Sparse.eval numericRow502 x =
    (1 : ℝ) * reducedSource502 x := by
  norm_num [numericRow502, reducedSource502, Integer.Sparse.eval, Sparse.eval, nodeValue2051, nodeValue2053, nodeValue2054, nodeValue2058, nodeValue2291, nodeValue3544, nodeValue4084]

noncomputable def reducedSource503 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0)))))))))))))))))))))))))))))

def numericRow503 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 1236, -4320), (Sum.inr 2479, -4320), (Sum.inr 2482, -4320), (Sum.inr 2488, -4320), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 2726, -4320), (Sum.inr 2739, -4320), (Sum.inr 2765, -4320), (Sum.inr 3293, -4320), (Sum.inr 3459, -4320), (Sum.inr 3468, -4320), (Sum.inr 3478, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3545, -4320), (Sum.inr 3582, -4320), (Sum.inr 3837, -8640), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 4589, 17280), (Sum.inr 4591, 17280), (Sum.inr 4592, 17280), (Sum.inr 4607, 17280), (Sum.inr 5129, 17280), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5184, 17280), (Sum.inr 5188, 17280), (Sum.inr 5198, 17280), (Sum.inr 5260, 17280), (Sum.inr 5289, 17280)]

theorem reindexCheck503 : Integer.Sparse.reindex keyMap MixedData.row503 = numericRow503 := by decide +kernel

theorem numericCheck503 (x : Master → ℝ) : Integer.Sparse.eval numericRow503 x =
    (17280 : ℝ) * reducedSource503 x := by
  norm_num [numericRow503, reducedSource503, Integer.Sparse.eval, Sparse.eval, nodeValue4589, nodeValue4591, nodeValue4592, nodeValue4602, nodeValue4607, nodeValue5072, nodeValue5075, nodeValue5080, nodeValue5101, nodeValue5127, nodeValue5129, nodeValue5134, nodeValue5144, nodeValue5147, nodeValue5184, nodeValue5188, nodeValue5198, nodeValue5256, nodeValue5258, nodeValue5260, nodeValue5261, nodeValue5271, nodeValue5274, nodeValue5289, nodeValue5291, nodeValue5409, nodeValue5423, nodeValue5432, nodeValue5434, nodeValue5441]
  ring

noncomputable def reducedSource504 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2914 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue2988 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3001 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4032 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))))))))))))

def numericRow504 : Integer.Sparse Master := [(Sum.inl 0, -196), (Sum.inl 2, -210), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 1, 170), (Sum.inr 1216, 2160), (Sum.inr 1217, 2160), (Sum.inr 1219, 2160), (Sum.inr 1241, 2160), (Sum.inr 2864, 2160), (Sum.inr 2865, 2160), (Sum.inr 2867, 2160), (Sum.inr 2885, 2160), (Sum.inr 2916, 2160), (Sum.inr 2928, 2160), (Sum.inr 3086, 2160), (Sum.inr 3097, 2160)]

theorem reindexCheck504 : Integer.Sparse.reindex keyMap MixedData.row504 = numericRow504 := by decide +kernel

theorem numericCheck504 (x : Master → ℝ) : Integer.Sparse.eval numericRow504 x =
    (2160 : ℝ) * reducedSource504 x := by
  norm_num [numericRow504, reducedSource504, Integer.Sparse.eval, Sparse.eval, nodeValue1216, nodeValue1217, nodeValue1219, nodeValue1241, nodeValue1267, nodeValue2864, nodeValue2865, nodeValue2867, nodeValue2885, nodeValue2914, nodeValue2916, nodeValue2928, nodeValue2937, nodeValue2939, nodeValue2988, nodeValue2990, nodeValue3001, nodeValue3085, nodeValue3086, nodeValue3089, nodeValue3090, nodeValue3097, nodeValue3103, nodeValue3109, nodeValue3112, nodeValue3982, nodeValue4027, nodeValue4032, nodeValue4035, nodeValue4037]
  ring

noncomputable def reducedSource505 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + 0)))))))))))))))))))))))))))))

def numericRow505 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 3288, 4320), (Sum.inr 3291, 4320), (Sum.inr 3293, 4320), (Sum.inr 3295, 4320), (Sum.inr 3296, 4320), (Sum.inr 3459, 4320), (Sum.inr 3468, 4320), (Sum.inr 3478, 4320), (Sum.inr 3514, 4320), (Sum.inr 3516, 4320), (Sum.inr 3524, 4320), (Sum.inr 3530, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3538, 4320), (Sum.inr 3540, 4320), (Sum.inr 3545, 4320), (Sum.inr 3557, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3582, 4320), (Sum.inr 3837, 4320), (Sum.inr 3850, 4320)]

theorem reindexCheck505 : Integer.Sparse.reindex keyMap MixedData.row505 = numericRow505 := by decide +kernel

theorem numericCheck505 (x : Master → ℝ) : Integer.Sparse.eval numericRow505 x =
    (4320 : ℝ) * reducedSource505 x := by
  norm_num [numericRow505, reducedSource505, Integer.Sparse.eval, Sparse.eval, nodeValue3288, nodeValue3291, nodeValue3293, nodeValue3295, nodeValue3296, nodeValue3459, nodeValue3468, nodeValue3470, nodeValue3478, nodeValue3513, nodeValue3514, nodeValue3516, nodeValue3524, nodeValue3525, nodeValue3530, nodeValue3533, nodeValue3534, nodeValue3538, nodeValue3540, nodeValue3545, nodeValue3547, nodeValue3557, nodeValue3570, nodeValue3572, nodeValue3582, nodeValue3807, nodeValue3837, nodeValue3850, nodeValue3852, nodeValue3860]
  ring

noncomputable def reducedSource506 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow506 : Integer.Sparse Master := [(Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

theorem reindexCheck506 : Integer.Sparse.reindex keyMap MixedData.row506 = numericRow506 := by decide +kernel

theorem numericCheck506 (x : Master → ℝ) : Integer.Sparse.eval numericRow506 x =
    (1 : ℝ) * reducedSource506 x := by
  norm_num [numericRow506, reducedSource506, Integer.Sparse.eval, Sparse.eval, nodeValue2722, nodeValue3807, nodeValue3837, nodeValue3850, nodeValue3903, nodeValue3905, nodeValue4092]

noncomputable def reducedSource507 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow507 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1215, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 2722, 1), (Sum.inr 4092, -1)]

theorem reindexCheck507 : Integer.Sparse.reindex keyMap MixedData.row507 = numericRow507 := by decide +kernel

theorem numericCheck507 (x : Master → ℝ) : Integer.Sparse.eval numericRow507 x =
    (1 : ℝ) * reducedSource507 x := by
  norm_num [numericRow507, reducedSource507, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue1215, nodeValue1219, nodeValue1236, nodeValue1261, nodeValue2722, nodeValue4092]

noncomputable def reducedSource508 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue2511 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow508 : Integer.Sparse Master := [(Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 2722, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

theorem reindexCheck508 : Integer.Sparse.reindex keyMap MixedData.row508 = numericRow508 := by decide +kernel

theorem numericCheck508 (x : Master → ℝ) : Integer.Sparse.eval numericRow508 x =
    (1 : ℝ) * reducedSource508 x := by
  norm_num [numericRow508, reducedSource508, Integer.Sparse.eval, Sparse.eval, nodeValue1236, nodeValue2511, nodeValue2553, nodeValue2722, nodeValue2739, nodeValue2742, nodeValue4092]

noncomputable def reducedSource509 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow509 : Integer.Sparse Master := [(Sum.inr 2569, 1), (Sum.inr 2614, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

theorem reindexCheck509 : Integer.Sparse.reindex keyMap MixedData.row509 = numericRow509 := by decide +kernel

theorem numericCheck509 (x : Master → ℝ) : Integer.Sparse.eval numericRow509 x =
    (1 : ℝ) * reducedSource509 x := by
  norm_num [numericRow509, reducedSource509, Integer.Sparse.eval, Sparse.eval, nodeValue2569, nodeValue2614, nodeValue2620, nodeValue2632, nodeValue2722, nodeValue3850, nodeValue4092]

noncomputable def reducedSource510 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow510 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 2614, 1), (Sum.inr 2722, 2), (Sum.inr 4092, -1)]

theorem reindexCheck510 : Integer.Sparse.reindex keyMap MixedData.row510 = numericRow510 := by decide +kernel

theorem numericCheck510 (x : Master → ℝ) : Integer.Sparse.eval numericRow510 x =
    (1 : ℝ) * reducedSource510 x := by
  norm_num [numericRow510, reducedSource510, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue2479, nodeValue2614, nodeValue2720, nodeValue2722, nodeValue4092]

noncomputable def reducedSource511 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow511 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 4092, -1)]

theorem reindexCheck511 : Integer.Sparse.reindex keyMap MixedData.row511 = numericRow511 := by decide +kernel

theorem numericCheck511 (x : Master → ℝ) : Integer.Sparse.eval numericRow511 x =
    (1 : ℝ) * reducedSource511 x := by
  norm_num [numericRow511, reducedSource511, Integer.Sparse.eval, Sparse.eval, nodeValue2542, nodeValue2545, nodeValue2553, nodeValue2566, nodeValue2722, nodeValue3837, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
