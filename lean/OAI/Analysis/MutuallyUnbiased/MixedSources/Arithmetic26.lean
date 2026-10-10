import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource416 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow416 : Integer.Sparse Master := [(Sum.inr 2495, 1), (Sum.inr 2759, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 3054, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

theorem reindexCheck416 : Integer.Sparse.reindex keyMap MixedData.row416 = numericRow416 := by decide +kernel

theorem numericCheck416 (x : Master → ℝ) : Integer.Sparse.eval numericRow416 x =
    (1 : ℝ) * reducedSource416 x := by
  norm_num [numericRow416, reducedSource416, Integer.Sparse.eval, Sparse.eval, nodeValue2495, nodeValue2759, nodeValue2974, nodeValue2979, nodeValue3054, nodeValue3813, nodeValue4092]

noncomputable def reducedSource417 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + 0))))))))))))))))))))

def numericRow417 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 2522, -2160), (Sum.inr 2672, -4320), (Sum.inr 2685, -2160), (Sum.inr 2686, -2160), (Sum.inr 3077, -4320), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3625, -4320), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4880, 17280), (Sum.inr 4881, 8640), (Sum.inr 4884, 8640), (Sum.inr 4891, 17280), (Sum.inr 4892, 8640), (Sum.inr 5103, 17280), (Sum.inr 5254, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5276, 8640), (Sum.inr 5287, 17280), (Sum.inr 5300, 8640)]

theorem reindexCheck417 : Integer.Sparse.reindex keyMap MixedData.row417 = numericRow417 := by decide +kernel

theorem numericCheck417 (x : Master → ℝ) : Integer.Sparse.eval numericRow417 x =
    (8640 : ℝ) * reducedSource417 x := by
  norm_num [numericRow417, reducedSource417, Integer.Sparse.eval, Sparse.eval, nodeValue4880, nodeValue4881, nodeValue4884, nodeValue4891, nodeValue4892, nodeValue4896, nodeValue4898, nodeValue5103, nodeValue5110, nodeValue5228, nodeValue5238, nodeValue5254, nodeValue5266, nodeValue5267, nodeValue5274, nodeValue5276, nodeValue5284, nodeValue5287, nodeValue5293, nodeValue5294, nodeValue5300]; ring

noncomputable def reducedSource418 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

def numericRow418 : Integer.Sparse Master := [(Sum.inl 0, -70), (Sum.inl 2, 125), (Sum.inl 3, 160), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 95), (Sum.inr 2254, 4320), (Sum.inr 2255, 2160), (Sum.inr 2267, 2160), (Sum.inr 2280, 2160), (Sum.inr 2672, 4320), (Sum.inr 2685, 2160), (Sum.inr 2686, 2160), (Sum.inr 3016, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3038, 4320), (Sum.inr 3039, 4320), (Sum.inr 3052, 2160), (Sum.inr 3055, 2160), (Sum.inr 3077, 4320), (Sum.inr 3222, 4320)]

theorem reindexCheck418 : Integer.Sparse.reindex keyMap MixedData.row418 = numericRow418 := by decide +kernel

theorem numericCheck418 (x : Master → ℝ) : Integer.Sparse.eval numericRow418 x =
    (2160 : ℝ) * reducedSource418 x := by
  norm_num [numericRow418, reducedSource418, Integer.Sparse.eval, Sparse.eval, nodeValue2254, nodeValue2255, nodeValue2267, nodeValue2280, nodeValue2672, nodeValue2685, nodeValue2686, nodeValue2742, nodeValue3016, nodeValue3024, nodeValue3025, nodeValue3038, nodeValue3039, nodeValue3052, nodeValue3055, nodeValue3077, nodeValue3101, nodeValue3102, nodeValue3222, nodeValue3224, nodeValue3225]; ring

noncomputable def reducedSource419 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((2 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((2 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

def numericRow419 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, -90), (Sum.inr 2396, 4320), (Sum.inr 2397, 4320), (Sum.inr 2401, 8640), (Sum.inr 2738, 4320), (Sum.inr 3282, 4320), (Sum.inr 3283, 4320), (Sum.inr 3294, 8640), (Sum.inr 3350, 4320), (Sum.inr 3355, 8640), (Sum.inr 3543, 4320), (Sum.inr 3544, 8640), (Sum.inr 3562, 8640), (Sum.inr 3568, 8640), (Sum.inr 3571, 4320), (Sum.inr 3578, 8640), (Sum.inr 3581, 8640), (Sum.inr 3874, 4320), (Sum.inr 3884, 8640)]

theorem reindexCheck419 : Integer.Sparse.reindex keyMap MixedData.row419 = numericRow419 := by decide +kernel

theorem numericCheck419 (x : Master → ℝ) : Integer.Sparse.eval numericRow419 x =
    (4320 : ℝ) * reducedSource419 x := by
  norm_num [numericRow419, reducedSource419, Integer.Sparse.eval, Sparse.eval, nodeValue2396, nodeValue2397, nodeValue2401, nodeValue2738, nodeValue3282, nodeValue3283, nodeValue3294, nodeValue3350, nodeValue3355, nodeValue3531, nodeValue3543, nodeValue3544, nodeValue3562, nodeValue3568, nodeValue3571, nodeValue3578, nodeValue3581, nodeValue3858, nodeValue3874, nodeValue3884, nodeValue3887]; ring

noncomputable def reducedSource420 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow420 : Integer.Sparse Master := [(Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 3881, 2), (Sum.inr 3902, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

theorem reindexCheck420 : Integer.Sparse.reindex keyMap MixedData.row420 = numericRow420 := by decide +kernel

theorem numericCheck420 (x : Master → ℝ) : Integer.Sparse.eval numericRow420 x =
    (1 : ℝ) * reducedSource420 x := by
  norm_num [numericRow420, reducedSource420, Integer.Sparse.eval, Sparse.eval, nodeValue2751, nodeValue3846, nodeValue3881, nodeValue3902, nodeValue3910, nodeValue4091]

noncomputable def reducedSource421 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue1253 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow421 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1249, 1), (Sum.inr 1253, 1), (Sum.inr 1262, 2), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem reindexCheck421 : Integer.Sparse.reindex keyMap MixedData.row421 = numericRow421 := by decide +kernel

theorem numericCheck421 (x : Master → ℝ) : Integer.Sparse.eval numericRow421 x =
    (1 : ℝ) * reducedSource421 x := by
  norm_num [numericRow421, reducedSource421, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue1249, nodeValue1253, nodeValue1262, nodeValue2751, nodeValue4091]

noncomputable def reducedSource422 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow422 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 2564, 1), (Sum.inr 2567, 2), (Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

theorem reindexCheck422 : Integer.Sparse.reindex keyMap MixedData.row422 = numericRow422 := by decide +kernel

theorem numericCheck422 (x : Master → ℝ) : Integer.Sparse.eval numericRow422 x =
    (1 : ℝ) * reducedSource422 x := by
  norm_num [numericRow422, reducedSource422, Integer.Sparse.eval, Sparse.eval, nodeValue2562, nodeValue2564, nodeValue2567, nodeValue2751, nodeValue3846, nodeValue4091]

noncomputable def reducedSource423 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow423 : Integer.Sparse Master := [(Sum.inr 1262, 1), (Sum.inr 2567, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 2751, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem reindexCheck423 : Integer.Sparse.reindex keyMap MixedData.row423 = numericRow423 := by decide +kernel

theorem numericCheck423 (x : Master → ℝ) : Integer.Sparse.eval numericRow423 x =
    (1 : ℝ) * reducedSource423 x := by
  norm_num [numericRow423, reducedSource423, Integer.Sparse.eval, Sparse.eval, nodeValue1262, nodeValue2567, nodeValue2633, nodeValue2723, nodeValue2751, nodeValue2764, nodeValue4091]

noncomputable def reducedSource424 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow424 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2624, 1), (Sum.inr 2627, 1), (Sum.inr 2633, 1), (Sum.inr 2751, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem reindexCheck424 : Integer.Sparse.reindex keyMap MixedData.row424 = numericRow424 := by decide +kernel

theorem numericCheck424 (x : Master → ℝ) : Integer.Sparse.eval numericRow424 x =
    (1 : ℝ) * reducedSource424 x := by
  norm_num [numericRow424, reducedSource424, Integer.Sparse.eval, Sparse.eval, nodeValue2622, nodeValue2624, nodeValue2627, nodeValue2633, nodeValue2751, nodeValue3881, nodeValue4091]

noncomputable def reducedSource425 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1253 x + ((1 : ℝ) * Sparse.eval nodeValue2564 x + ((2 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow425 : Integer.Sparse Master := [(Sum.inr 1253, 1), (Sum.inr 2564, 1), (Sum.inr 2627, 2), (Sum.inr 2751, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem reindexCheck425 : Integer.Sparse.reindex keyMap MixedData.row425 = numericRow425 := by decide +kernel

theorem numericCheck425 (x : Master → ℝ) : Integer.Sparse.eval numericRow425 x =
    (1 : ℝ) * reducedSource425 x := by
  norm_num [numericRow425, reducedSource425, Integer.Sparse.eval, Sparse.eval, nodeValue1253, nodeValue2564, nodeValue2627, nodeValue2751, nodeValue2754, nodeValue4091]

noncomputable def reducedSource426 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4437 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue5064 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5071 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow426 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2931, -8640), (Sum.inr 3077, -4320), (Sum.inr 3612, -8640), (Sum.inr 3625, -4320), (Sum.inr 3885, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 4010, -4320), (Sum.inr 4436, 17280), (Sum.inr 4437, 17280), (Sum.inr 4444, 17280), (Sum.inr 4453, 34560), (Sum.inr 5064, 17280), (Sum.inr 5067, 17280), (Sum.inr 5071, 34560), (Sum.inr 5145, 34560), (Sum.inr 5147, 34560), (Sum.inr 5164, 34560), (Sum.inr 5220, 17280), (Sum.inr 5222, 17280), (Sum.inr 5229, 34560), (Sum.inr 5281, 17280), (Sum.inr 5289, 34560)]

theorem reindexCheck426 : Integer.Sparse.reindex keyMap MixedData.row426 = numericRow426 := by decide +kernel

theorem numericCheck426 (x : Master → ℝ) : Integer.Sparse.eval numericRow426 x =
    (17280 : ℝ) * reducedSource426 x := by
  norm_num [numericRow426, reducedSource426, Integer.Sparse.eval, Sparse.eval, nodeValue4436, nodeValue4437, nodeValue4444, nodeValue4453, nodeValue5064, nodeValue5067, nodeValue5071, nodeValue5145, nodeValue5147, nodeValue5152, nodeValue5164, nodeValue5220, nodeValue5222, nodeValue5229, nodeValue5281, nodeValue5284, nodeValue5289, nodeValue5448, nodeValue5471, nodeValue5473, nodeValue5485]; ring

noncomputable def reducedSource427 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2478 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((2 : ℝ) * Sparse.eval nodeValue2569 x + ((2 : ℝ) * Sparse.eval nodeValue2576 x + ((2 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

def numericRow427 : Integer.Sparse Master := [(Sum.inl 0, -334), (Sum.inl 5, 240), (Sum.inl 2, -160), (Sum.inl 7, -320), (Sum.inl 8, -320), (Sum.inl 51, 960), (Sum.inl 3, -1120), (Sum.inl 13, -160), (Sum.inl 12, -160), (Sum.inl 4, -640), (Sum.inl 1, 190), (Sum.inl 31, 960), (Sum.inr 1018, 8640), (Sum.inr 1019, 8640), (Sum.inr 1026, 8640), (Sum.inr 1036, 17280), (Sum.inr 2469, 8640), (Sum.inr 2473, 8640), (Sum.inr 2478, 17280), (Sum.inr 2567, 17280), (Sum.inr 2569, 17280), (Sum.inr 2591, 17280), (Sum.inr 2662, 8640), (Sum.inr 2664, 8640), (Sum.inr 2673, 17280), (Sum.inr 2750, 8640), (Sum.inr 2763, 17280), (Sum.inr 3885, 8640)]

theorem reindexCheck427 : Integer.Sparse.reindex keyMap MixedData.row427 = numericRow427 := by decide +kernel

theorem numericCheck427 (x : Master → ℝ) : Integer.Sparse.eval numericRow427 x =
    (8640 : ℝ) * reducedSource427 x := by
  norm_num [numericRow427, reducedSource427, Integer.Sparse.eval, Sparse.eval, nodeValue1018, nodeValue1019, nodeValue1026, nodeValue1036, nodeValue2469, nodeValue2473, nodeValue2478, nodeValue2567, nodeValue2569, nodeValue2576, nodeValue2591, nodeValue2662, nodeValue2664, nodeValue2673, nodeValue2750, nodeValue2753, nodeValue2763, nodeValue3885, nodeValue3976, nodeValue3995, nodeValue3998]; ring

noncomputable def reducedSource428 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1643 x + ((2 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((2 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3443 x + ((2 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + 0))))))))))))))))))))

def numericRow428 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 25), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 25, 240), (Sum.inl 4, -160), (Sum.inl 1, -50), (Sum.inr 1642, 4320), (Sum.inr 1643, 4320), (Sum.inr 1646, 8640), (Sum.inr 1736, 4320), (Sum.inr 3388, 4320), (Sum.inr 3389, 4320), (Sum.inr 3392, 8640), (Sum.inr 3443, 4320), (Sum.inr 3445, 8640), (Sum.inr 3476, 4320), (Sum.inr 3530, 8640), (Sum.inr 3562, 8640), (Sum.inr 3565, 8640), (Sum.inr 3571, 4320), (Sum.inr 3572, 8640), (Sum.inr 3612, 8640), (Sum.inr 3625, 4320), (Sum.inr 3961, 8640)]

theorem reindexCheck428 : Integer.Sparse.reindex keyMap MixedData.row428 = numericRow428 := by decide +kernel

theorem numericCheck428 (x : Master → ℝ) : Integer.Sparse.eval numericRow428 x =
    (4320 : ℝ) * reducedSource428 x := by
  norm_num [numericRow428, reducedSource428, Integer.Sparse.eval, Sparse.eval, nodeValue1642, nodeValue1643, nodeValue1646, nodeValue1736, nodeValue3388, nodeValue3389, nodeValue3392, nodeValue3443, nodeValue3445, nodeValue3476, nodeValue3530, nodeValue3562, nodeValue3565, nodeValue3571, nodeValue3572, nodeValue3612, nodeValue3625, nodeValue3956, nodeValue3961, nodeValue3984, nodeValue4028]; ring

noncomputable def reducedSource429 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow429 : Integer.Sparse Master := [(Sum.inr 3078, 1), (Sum.inr 3885, 1), (Sum.inr 3958, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem reindexCheck429 : Integer.Sparse.reindex keyMap MixedData.row429 = numericRow429 := by decide +kernel

theorem numericCheck429 (x : Master → ℝ) : Integer.Sparse.eval numericRow429 x =
    (1 : ℝ) * reducedSource429 x := by
  norm_num [numericRow429, reducedSource429, Integer.Sparse.eval, Sparse.eval, nodeValue3078, nodeValue3885, nodeValue3953, nodeValue3958, nodeValue4010, nodeValue4091]

noncomputable def reducedSource430 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1389 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow430 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 1389, 1), (Sum.inr 1391, 1), (Sum.inr 1407, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem reindexCheck430 : Integer.Sparse.reindex keyMap MixedData.row430 = numericRow430 := by decide +kernel

theorem numericCheck430 (x : Master → ℝ) : Integer.Sparse.eval numericRow430 x =
    (1 : ℝ) * reducedSource430 x := by
  norm_num [numericRow430, reducedSource430, Integer.Sparse.eval, Sparse.eval, nodeValue1384, nodeValue1389, nodeValue1391, nodeValue1407, nodeValue3078, nodeValue4091]

noncomputable def reducedSource431 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1384 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow431 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 2925, 2), (Sum.inr 3068, 1), (Sum.inr 3074, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

theorem reindexCheck431 : Integer.Sparse.reindex keyMap MixedData.row431 = numericRow431 := by decide +kernel

theorem numericCheck431 (x : Master → ℝ) : Integer.Sparse.eval numericRow431 x =
    (1 : ℝ) * reducedSource431 x := by
  norm_num [numericRow431, reducedSource431, Integer.Sparse.eval, Sparse.eval, nodeValue1384, nodeValue2925, nodeValue3068, nodeValue3074, nodeValue3078, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
