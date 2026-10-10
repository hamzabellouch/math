import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource304 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((2 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow304 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 2622, 2), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem reindexCheck304 : Integer.Sparse.reindex keyMap MixedData.row304 = numericRow304 := by decide +kernel

theorem numericCheck304 (x : Master → ℝ) : Integer.Sparse.eval numericRow304 x =
    (1 : ℝ) * reducedSource304 x := by
  norm_num [numericRow304, reducedSource304, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue2622, nodeValue2709, nodeValue2750, nodeValue2751, nodeValue4091]

noncomputable def reducedSource305 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow305 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 2), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

theorem reindexCheck305 : Integer.Sparse.reindex keyMap MixedData.row305 = numericRow305 := by decide +kernel

theorem numericCheck305 (x : Master → ℝ) : Integer.Sparse.eval numericRow305 x =
    (1 : ℝ) * reducedSource305 x := by
  norm_num [numericRow305, reducedSource305, Integer.Sparse.eval, Sparse.eval, nodeValue2470, nodeValue2473, nodeValue2480, nodeValue2709, nodeValue3800, nodeValue4091]

noncomputable def reducedSource306 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow306 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 2615, 1), (Sum.inr 2721, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem reindexCheck306 : Integer.Sparse.reindex keyMap MixedData.row306 = numericRow306 := by decide +kernel

theorem numericCheck306 (x : Master → ℝ) : Integer.Sparse.eval numericRow306 x =
    (1 : ℝ) * reducedSource306 x := by
  norm_num [numericRow306, reducedSource306, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue2480, nodeValue2615, nodeValue2709, nodeValue2721, nodeValue2723, nodeValue4091]

noncomputable def reducedSource307 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow307 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2612, 1), (Sum.inr 2615, 1), (Sum.inr 2622, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

theorem reindexCheck307 : Integer.Sparse.reindex keyMap MixedData.row307 = numericRow307 := by decide +kernel

theorem numericCheck307 (x : Master → ℝ) : Integer.Sparse.eval numericRow307 x =
    (1 : ℝ) * reducedSource307 x := by
  norm_num [numericRow307, reducedSource307, Integer.Sparse.eval, Sparse.eval, nodeValue2610, nodeValue2612, nodeValue2615, nodeValue2622, nodeValue2709, nodeValue3871, nodeValue4091]

noncomputable def reducedSource308 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1208 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow308 : Integer.Sparse Master := [(Sum.inr 1208, 1), (Sum.inr 2473, 1), (Sum.inr 2612, 2), (Sum.inr 2710, 1), (Sum.inr 4091, -1)]

theorem reindexCheck308 : Integer.Sparse.reindex keyMap MixedData.row308 = numericRow308 := by decide +kernel

theorem numericCheck308 (x : Master → ℝ) : Integer.Sparse.eval numericRow308 x =
    (1 : ℝ) * reducedSource308 x := by
  norm_num [numericRow308, reducedSource308, Integer.Sparse.eval, Sparse.eval, nodeValue1208, nodeValue2473, nodeValue2612, nodeValue2709, nodeValue2710, nodeValue4091]

noncomputable def reducedSource309 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5223 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5253 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0)))))))))))))))))))

def numericRow309 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 2019, -180), (Sum.inr 2051, -180), (Sum.inr 2190, -180), (Sum.inr 2191, -180), (Sum.inr 2244, -180), (Sum.inr 2262, -180), (Sum.inr 2694, -180), (Sum.inr 2722, -360), (Sum.inr 2723, -720), (Sum.inr 3077, -180), (Sum.inr 3493, -180), (Sum.inr 3533, -360), (Sum.inr 3544, -720), (Sum.inr 3625, -180), (Sum.inr 3627, -360), (Sum.inr 4803, 1440), (Sum.inr 5219, 720), (Sum.inr 5220, 720), (Sum.inr 5223, 1440), (Sum.inr 5244, 720), (Sum.inr 5249, 720), (Sum.inr 5251, 720), (Sum.inr 5253, 1440), (Sum.inr 5254, 1440), (Sum.inr 5266, 1440), (Sum.inr 5282, 720)]

theorem reindexCheck309 : Integer.Sparse.reindex keyMap MixedData.row309 = numericRow309 := by decide +kernel

theorem numericCheck309 (x : Master → ℝ) : Integer.Sparse.eval numericRow309 x =
    (720 : ℝ) * reducedSource309 x := by
  norm_num [numericRow309, reducedSource309, Integer.Sparse.eval, Sparse.eval, nodeValue4801, nodeValue4803, nodeValue4831, nodeValue4888, nodeValue5219, nodeValue5220, nodeValue5223, nodeValue5241, nodeValue5242, nodeValue5244, nodeValue5249, nodeValue5251, nodeValue5253, nodeValue5254, nodeValue5258, nodeValue5259, nodeValue5266, nodeValue5282, nodeValue5284, nodeValue5293]
  ring

noncomputable def reducedSource310 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2665 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((2 : ℝ) * Sparse.eval nodeValue2714 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + 0))))))))))))))))))))

def numericRow310 : Integer.Sparse Master := [(Sum.inl 0, -222), (Sum.inl 5, 20), (Sum.inl 2, 255), (Sum.inl 35, 80), (Sum.inl 55, -240), (Sum.inl 26, 160), (Sum.inl 27, -60), (Sum.inl 1, 265), (Sum.inr 2190, 4320), (Sum.inr 2191, 4320), (Sum.inr 2195, 8640), (Sum.inr 2244, 4320), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2665, 8640), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2713, 8640), (Sum.inr 2714, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2731, 8640), (Sum.inr 2751, 4320), (Sum.inr 3029, 4320)]

theorem reindexCheck310 : Integer.Sparse.reindex keyMap MixedData.row310 = numericRow310 := by decide +kernel

theorem numericCheck310 (x : Master → ℝ) : Integer.Sparse.eval numericRow310 x =
    (4320 : ℝ) * reducedSource310 x := by
  norm_num [numericRow310, reducedSource310, Integer.Sparse.eval, Sparse.eval, nodeValue2190, nodeValue2191, nodeValue2195, nodeValue2244, nodeValue2661, nodeValue2662, nodeValue2665, nodeValue2708, nodeValue2710, nodeValue2713, nodeValue2714, nodeValue2722, nodeValue2723, nodeValue2731, nodeValue2751, nodeValue2753, nodeValue2767, nodeValue3029, nodeValue3080, nodeValue3081, nodeValue3088]
  ring

noncomputable def reducedSource311 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3017 x + ((2 : ℝ) * Sparse.eval nodeValue3019 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

def numericRow311 : Integer.Sparse Master := [(Sum.inl 0, -688), (Sum.inl 5, -120), (Sum.inl 6, 20), (Sum.inl 2, 920), (Sum.inl 7, 160), (Sum.inl 35, 480), (Sum.inl 3, 160), (Sum.inl 13, 640), (Sum.inl 52, 320), (Sum.inl 54, -480), (Sum.inl 12, 160), (Sum.inl 1, 780), (Sum.inr 2694, 8640), (Sum.inr 2698, 8640), (Sum.inr 2723, 17280), (Sum.inr 3016, 17280), (Sum.inr 3017, 17280), (Sum.inr 3019, 17280), (Sum.inr 3039, 17280), (Sum.inr 3064, 8640), (Sum.inr 3066, 8640), (Sum.inr 3068, 8640), (Sum.inr 3069, 8640), (Sum.inr 3077, 8640), (Sum.inr 3078, 8640), (Sum.inr 3202, 17280)]

theorem reindexCheck311 : Integer.Sparse.reindex keyMap MixedData.row311 = numericRow311 := by decide +kernel

theorem numericCheck311 (x : Master → ℝ) : Integer.Sparse.eval numericRow311 x =
    (8640 : ℝ) * reducedSource311 x := by
  norm_num [numericRow311, reducedSource311, Integer.Sparse.eval, Sparse.eval, nodeValue2694, nodeValue2695, nodeValue2698, nodeValue2723, nodeValue3016, nodeValue3017, nodeValue3019, nodeValue3039, nodeValue3064, nodeValue3066, nodeValue3068, nodeValue3069, nodeValue3077, nodeValue3078, nodeValue3088, nodeValue3089, nodeValue3102, nodeValue3202, nodeValue3205, nodeValue3209, nodeValue3227]
  ring

noncomputable def reducedSource312 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3493 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow312 : Integer.Sparse Master := [(Sum.inr 3493, 1), (Sum.inr 3497, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

theorem reindexCheck312 : Integer.Sparse.reindex keyMap MixedData.row312 = numericRow312 := by decide +kernel

theorem numericCheck312 (x : Master → ℝ) : Integer.Sparse.eval numericRow312 x =
    (1 : ℝ) * reducedSource312 x := by
  norm_num [numericRow312, reducedSource312, Integer.Sparse.eval, Sparse.eval, nodeValue3493, nodeValue3494, nodeValue3497, nodeValue3531, nodeValue3544, nodeValue4084]

noncomputable def reducedSource313 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((2 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow313 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2021, 2), (Sum.inr 2051, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

theorem reindexCheck313 : Integer.Sparse.reindex keyMap MixedData.row313 = numericRow313 := by decide +kernel

theorem numericCheck313 (x : Master → ℝ) : Integer.Sparse.eval numericRow313 x =
    (1 : ℝ) * reducedSource313 x := by
  norm_num [numericRow313, reducedSource313, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue2021, nodeValue2051, nodeValue2262, nodeValue3531, nodeValue4084]

noncomputable def reducedSource314 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow314 : Integer.Sparse Master := [(Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3627, 2), (Sum.inr 4084, -1)]

theorem reindexCheck314 : Integer.Sparse.reindex keyMap MixedData.row314 = numericRow314 := by decide +kernel

theorem numericCheck314 (x : Master → ℝ) : Integer.Sparse.eval numericRow314 x =
    (1 : ℝ) * reducedSource314 x := by
  norm_num [numericRow314, reducedSource314, Integer.Sparse.eval, Sparse.eval, nodeValue2262, nodeValue3531, nodeValue3580, nodeValue3625, nodeValue3627, nodeValue4084]

noncomputable def reducedSource315 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3375 x + ((2 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow315 : Integer.Sparse Master := [(Sum.inr 3375, 1), (Sum.inr 3377, 2), (Sum.inr 3388, 1), (Sum.inr 3497, 1), (Sum.inr 4084, -1)]

theorem reindexCheck315 : Integer.Sparse.reindex keyMap MixedData.row315 = numericRow315 := by decide +kernel

theorem numericCheck315 (x : Master → ℝ) : Integer.Sparse.eval numericRow315 x =
    (1 : ℝ) * reducedSource315 x := by
  norm_num [numericRow315, reducedSource315, Integer.Sparse.eval, Sparse.eval, nodeValue3375, nodeValue3377, nodeValue3388, nodeValue3497, nodeValue3531, nodeValue4084]

noncomputable def reducedSource316 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow316 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 3388, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

theorem reindexCheck316 : Integer.Sparse.reindex keyMap MixedData.row316 = numericRow316 := by decide +kernel

theorem numericCheck316 (x : Master → ℝ) : Integer.Sparse.eval numericRow316 x =
    (1 : ℝ) * reducedSource316 x := by
  norm_num [numericRow316, reducedSource316, Integer.Sparse.eval, Sparse.eval, nodeValue2051, nodeValue3388, nodeValue3531, nodeValue3539, nodeValue3544, nodeValue4084]

noncomputable def reducedSource317 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow317 : Integer.Sparse Master := [(Sum.inr 3502, 1), (Sum.inr 3504, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

theorem reindexCheck317 : Integer.Sparse.reindex keyMap MixedData.row317 = numericRow317 := by decide +kernel

theorem numericCheck317 (x : Master → ℝ) : Integer.Sparse.eval numericRow317 x =
    (1 : ℝ) * reducedSource317 x := by
  norm_num [numericRow317, reducedSource317, Integer.Sparse.eval, Sparse.eval, nodeValue3494, nodeValue3502, nodeValue3504, nodeValue3531, nodeValue3580, nodeValue4084]

noncomputable def reducedSource318 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow318 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 3375, 1), (Sum.inr 3502, 1), (Sum.inr 3533, 2), (Sum.inr 4084, -1)]

theorem reindexCheck318 : Integer.Sparse.reindex keyMap MixedData.row318 = numericRow318 := by decide +kernel

theorem numericCheck318 (x : Master → ℝ) : Integer.Sparse.eval numericRow318 x =
    (1 : ℝ) * reducedSource318 x := by
  norm_num [numericRow318, reducedSource318, Integer.Sparse.eval, Sparse.eval, nodeValue2019, nodeValue3375, nodeValue3502, nodeValue3531, nodeValue3533, nodeValue4084]

noncomputable def reducedSource319 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1995 x + ((2 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((2 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3536 x + ((2 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + 0))))))))))))))))))))

def numericRow319 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 75), (Sum.inl 3, 720), (Sum.inl 13, 320), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, -210), (Sum.inr 1995, 4320), (Sum.inr 1998, 8640), (Sum.inr 2050, 4320), (Sum.inr 2201, 4320), (Sum.inr 3278, 4320), (Sum.inr 3280, 4320), (Sum.inr 3288, 8640), (Sum.inr 3476, 4320), (Sum.inr 3477, 8640), (Sum.inr 3532, 8640), (Sum.inr 3536, 8640), (Sum.inr 3537, 8640), (Sum.inr 3539, 8640), (Sum.inr 3571, 4320), (Sum.inr 3574, 8640), (Sum.inr 3576, 4320), (Sum.inr 3812, 4320), (Sum.inr 3840, 8640)]

theorem reindexCheck319 : Integer.Sparse.reindex keyMap MixedData.row319 = numericRow319 := by decide +kernel

theorem numericCheck319 (x : Master → ℝ) : Integer.Sparse.eval numericRow319 x =
    (4320 : ℝ) * reducedSource319 x := by
  norm_num [numericRow319, reducedSource319, Integer.Sparse.eval, Sparse.eval, nodeValue1995, nodeValue1998, nodeValue2050, nodeValue2201, nodeValue3278, nodeValue3280, nodeValue3288, nodeValue3476, nodeValue3477, nodeValue3531, nodeValue3532, nodeValue3536, nodeValue3537, nodeValue3539, nodeValue3571, nodeValue3574, nodeValue3576, nodeValue3812, nodeValue3840, nodeValue3851, nodeValue3855]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
