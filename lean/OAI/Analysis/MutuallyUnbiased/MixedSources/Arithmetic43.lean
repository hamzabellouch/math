import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource688 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2457 x + ((2 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((2 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

def numericRow688 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 50), (Sum.inl 3, 400), (Sum.inl 13, 80), (Sum.inl 12, 280), (Sum.inl 4, 240), (Sum.inl 1, -175), (Sum.inr 2457, 2160), (Sum.inr 2460, 4320), (Sum.inr 2507, 2160), (Sum.inr 2738, 2160), (Sum.inr 3278, 2160), (Sum.inr 3282, 2160), (Sum.inr 3289, 4320), (Sum.inr 3532, 4320), (Sum.inr 3539, 2160), (Sum.inr 3568, 4320), (Sum.inr 3569, 4320), (Sum.inr 3571, 4320), (Sum.inr 3574, 4320), (Sum.inr 3576, 2160), (Sum.inr 3580, 2160), (Sum.inr 3581, 4320), (Sum.inr 3880, 4320)]

theorem reindexCheck688 : Integer.Sparse.reindex keyMap MixedData.row688 = numericRow688 := by decide +kernel

theorem numericCheck688 (x : Master → ℝ) : Integer.Sparse.eval numericRow688 x =
    (2160 : ℝ) * reducedSource688 x := by
  norm_num [numericRow688, reducedSource688, Integer.Sparse.eval, Sparse.eval, nodeValue2457, nodeValue2460, nodeValue2507, nodeValue2738, nodeValue3278, nodeValue3282, nodeValue3289, nodeValue3531, nodeValue3532, nodeValue3539, nodeValue3568, nodeValue3569, nodeValue3571, nodeValue3574, nodeValue3576, nodeValue3580, nodeValue3581, nodeValue3851, nodeValue3880, nodeValue3882, nodeValue3887]
  ring

noncomputable def reducedSource689 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow689 : Integer.Sparse Master := [(Sum.inr 2750, 1), (Sum.inr 3880, 2), (Sum.inr 3901, 1), (Sum.inr 3909, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

theorem reindexCheck689 : Integer.Sparse.reindex keyMap MixedData.row689 = numericRow689 := by decide +kernel

theorem numericCheck689 (x : Master → ℝ) : Integer.Sparse.eval numericRow689 x =
    (1 : ℝ) * reducedSource689 x := by
  norm_num [numericRow689, reducedSource689, Integer.Sparse.eval, Sparse.eval, nodeValue2750, nodeValue3880, nodeValue3901, nodeValue3909, nodeValue3910, nodeValue4091]

noncomputable def reducedSource690 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue1248 x + ((1 : ℝ) * Sparse.eval nodeValue1250 x + ((2 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow690 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1248, 1), (Sum.inr 1250, 1), (Sum.inr 1260, 2), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

theorem reindexCheck690 : Integer.Sparse.reindex keyMap MixedData.row690 = numericRow690 := by decide +kernel

theorem numericCheck690 (x : Master → ℝ) : Integer.Sparse.eval numericRow690 x =
    (1 : ℝ) * reducedSource690 x := by
  norm_num [numericRow690, reducedSource690, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue1248, nodeValue1250, nodeValue1260, nodeValue2750, nodeValue4091]

noncomputable def reducedSource691 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow691 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem reindexCheck691 : Integer.Sparse.reindex keyMap MixedData.row691 = numericRow691 := by decide +kernel

theorem numericCheck691 (x : Master → ℝ) : Integer.Sparse.eval numericRow691 x =
    (1 : ℝ) * reducedSource691 x := by
  norm_num [numericRow691, reducedSource691, Integer.Sparse.eval, Sparse.eval, nodeValue1260, nodeValue2631, nodeValue2721, nodeValue2750, nodeValue2764, nodeValue4091]

noncomputable def reducedSource692 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow692 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2623, 1), (Sum.inr 2625, 1), (Sum.inr 2631, 1), (Sum.inr 2750, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem reindexCheck692 : Integer.Sparse.reindex keyMap MixedData.row692 = numericRow692 := by decide +kernel

theorem numericCheck692 (x : Master → ℝ) : Integer.Sparse.eval numericRow692 x =
    (1 : ℝ) * reducedSource692 x := by
  norm_num [numericRow692, reducedSource692, Integer.Sparse.eval, Sparse.eval, nodeValue2622, nodeValue2623, nodeValue2625, nodeValue2631, nodeValue2750, nodeValue3880, nodeValue4091]

noncomputable def reducedSource693 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4449 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow693 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2924, -8640), (Sum.inr 3077, -4320), (Sum.inr 3605, -8640), (Sum.inr 3625, -4320), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3974, -17280), (Sum.inr 4010, -4320), (Sum.inr 4435, 17280), (Sum.inr 4436, 17280), (Sum.inr 4439, 17280), (Sum.inr 4449, 34560), (Sum.inr 5144, 34560), (Sum.inr 5145, 34560), (Sum.inr 5160, 34560), (Sum.inr 5219, 17280), (Sum.inr 5220, 17280), (Sum.inr 5226, 34560), (Sum.inr 5249, 17280), (Sum.inr 5251, 17280), (Sum.inr 5255, 34560), (Sum.inr 5282, 17280), (Sum.inr 5289, 34560)]

theorem reindexCheck693 : Integer.Sparse.reindex keyMap MixedData.row693 = numericRow693 := by decide +kernel

theorem numericCheck693 (x : Master → ℝ) : Integer.Sparse.eval numericRow693 x =
    (17280 : ℝ) * reducedSource693 x := by
  norm_num [numericRow693, reducedSource693, Integer.Sparse.eval, Sparse.eval, nodeValue4435, nodeValue4436, nodeValue4439, nodeValue4449, nodeValue5144, nodeValue5145, nodeValue5149, nodeValue5160, nodeValue5219, nodeValue5220, nodeValue5226, nodeValue5249, nodeValue5251, nodeValue5255, nodeValue5282, nodeValue5284, nodeValue5289, nodeValue5431, nodeValue5478, nodeValue5481, nodeValue5485]
  ring

noncomputable def reducedSource694 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((2 : ℝ) * Sparse.eval nodeValue1032 x + ((2 : ℝ) * Sparse.eval nodeValue2566 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((2 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0))))))))))))))))))))

def numericRow694 : Integer.Sparse Master := [(Sum.inl 0, -115), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, 260), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 51, -480), (Sum.inl 3, 1040), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 12, 240), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -525), (Sum.inl 31, -480), (Sum.inr 1017, 4320), (Sum.inr 1018, 4320), (Sum.inr 1021, 4320), (Sum.inr 1032, 8640), (Sum.inr 2566, 8640), (Sum.inr 2567, 8640), (Sum.inr 2587, 8640), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2669, 8640), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2718, 8640), (Sum.inr 2751, 4320), (Sum.inr 2763, 8640), (Sum.inr 3849, 4320)]

theorem reindexCheck694 : Integer.Sparse.reindex keyMap MixedData.row694 = numericRow694 := by decide +kernel

theorem numericCheck694 (x : Master → ℝ) : Integer.Sparse.eval numericRow694 x =
    (4320 : ℝ) * reducedSource694 x := by
  norm_num [numericRow694, reducedSource694, Integer.Sparse.eval, Sparse.eval, nodeValue1017, nodeValue1018, nodeValue1021, nodeValue1032, nodeValue2566, nodeValue2567, nodeValue2570, nodeValue2587, nodeValue2661, nodeValue2662, nodeValue2669, nodeValue2708, nodeValue2710, nodeValue2718, nodeValue2751, nodeValue2753, nodeValue2763, nodeValue3849, nodeValue3979, nodeValue3994, nodeValue3998]
  ring

noncomputable def reducedSource695 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1635 x + ((2 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1642 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((2 : ℝ) * Sparse.eval nodeValue3558 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + 0))))))))))))))))))))

def numericRow695 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, 50), (Sum.inl 3, 640), (Sum.inl 12, 320), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -230), (Sum.inr 1635, 4320), (Sum.inr 1636, 8640), (Sum.inr 1642, 4320), (Sum.inr 1713, 4320), (Sum.inr 3375, 4320), (Sum.inr 3376, 8640), (Sum.inr 3388, 4320), (Sum.inr 3502, 4320), (Sum.inr 3503, 8640), (Sum.inr 3539, 4320), (Sum.inr 3557, 8640), (Sum.inr 3558, 8640), (Sum.inr 3562, 8640), (Sum.inr 3572, 8640), (Sum.inr 3580, 4320), (Sum.inr 3605, 8640), (Sum.inr 3625, 4320), (Sum.inr 3974, 8640)]

theorem reindexCheck695 : Integer.Sparse.reindex keyMap MixedData.row695 = numericRow695 := by decide +kernel

theorem numericCheck695 (x : Master → ℝ) : Integer.Sparse.eval numericRow695 x =
    (4320 : ℝ) * reducedSource695 x := by
  norm_num [numericRow695, reducedSource695, Integer.Sparse.eval, Sparse.eval, nodeValue1635, nodeValue1636, nodeValue1642, nodeValue1713, nodeValue3375, nodeValue3376, nodeValue3388, nodeValue3502, nodeValue3503, nodeValue3539, nodeValue3557, nodeValue3558, nodeValue3562, nodeValue3572, nodeValue3580, nodeValue3605, nodeValue3625, nodeValue3974, nodeValue3984, nodeValue3991, nodeValue4026]
  ring

noncomputable def reducedSource696 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow696 : Integer.Sparse Master := [(Sum.inr 3074, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem reindexCheck696 : Integer.Sparse.reindex keyMap MixedData.row696 = numericRow696 := by decide +kernel

theorem numericCheck696 (x : Master → ℝ) : Integer.Sparse.eval numericRow696 x =
    (1 : ℝ) * reducedSource696 x := by
  norm_num [numericRow696, reducedSource696, Integer.Sparse.eval, Sparse.eval, nodeValue3074, nodeValue3875, nodeValue3974, nodeValue4008, nodeValue4010, nodeValue4091]

noncomputable def reducedSource697 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1387 x + ((2 : ℝ) * Sparse.eval nodeValue1403 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow697 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1387, 1), (Sum.inr 1403, 2), (Sum.inr 3074, 1), (Sum.inr 4091, -1)]

theorem reindexCheck697 : Integer.Sparse.reindex keyMap MixedData.row697 = numericRow697 := by decide +kernel

theorem numericCheck697 (x : Master → ℝ) : Integer.Sparse.eval numericRow697 x =
    (1 : ℝ) * reducedSource697 x := by
  norm_num [numericRow697, reducedSource697, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue1384, nodeValue1387, nodeValue1403, nodeValue3074, nodeValue4091]

noncomputable def reducedSource698 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow698 : Integer.Sparse Master := [(Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

theorem reindexCheck698 : Integer.Sparse.reindex keyMap MixedData.row698 = numericRow698 := by decide +kernel

theorem numericCheck698 (x : Master → ℝ) : Integer.Sparse.eval numericRow698 x =
    (1 : ℝ) * reducedSource698 x := by
  norm_num [numericRow698, reducedSource698, Integer.Sparse.eval, Sparse.eval, nodeValue2924, nodeValue2925, nodeValue2928, nodeValue2951, nodeValue3074, nodeValue3974, nodeValue4091]

noncomputable def reducedSource699 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow699 : Integer.Sparse Master := [(Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3074, 1), (Sum.inr 3091, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem reindexCheck699 : Integer.Sparse.reindex keyMap MixedData.row699 = numericRow699 := by decide +kernel

theorem numericCheck699 (x : Master → ℝ) : Integer.Sparse.eval numericRow699 x =
    (1 : ℝ) * reducedSource699 x := by
  norm_num [numericRow699, reducedSource699, Integer.Sparse.eval, Sparse.eval, nodeValue3068, nodeValue3069, nodeValue3074, nodeValue3091, nodeValue3875, nodeValue4091]

noncomputable def reducedSource700 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((2 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2583 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2749 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2752 x + ((2 : ℝ) * Sparse.eval nodeValue2756 x + ((2 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3104 x + ((1 : ℝ) * Sparse.eval nodeValue3105 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + 0)))))))))))))))))))

def numericRow700 : Integer.Sparse Master := [(Sum.inl 0, -197), (Sum.inl 5, 20), (Sum.inl 2, -230), (Sum.inl 35, 80), (Sum.inl 3, 80), (Sum.inl 55, -240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 27, -60), (Sum.inl 1, -145), (Sum.inr 2240, 4320), (Sum.inr 2241, 4320), (Sum.inr 2243, 4320), (Sum.inr 2250, 8640), (Sum.inr 2565, 8640), (Sum.inr 2573, 4320), (Sum.inr 2583, 4320), (Sum.inr 2747, 4320), (Sum.inr 2749, 4320), (Sum.inr 2750, 8640), (Sum.inr 2756, 8640), (Sum.inr 2757, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 8640), (Sum.inr 2773, 8640)]

theorem reindexCheck700 : Integer.Sparse.reindex keyMap MixedData.row700 = numericRow700 := by decide +kernel

theorem numericCheck700 (x : Master → ℝ) : Integer.Sparse.eval numericRow700 x =
    (4320 : ℝ) * reducedSource700 x := by
  norm_num [numericRow700, reducedSource700, Integer.Sparse.eval, Sparse.eval, nodeValue2240, nodeValue2241, nodeValue2243, nodeValue2250, nodeValue2565, nodeValue2573, nodeValue2583, nodeValue2747, nodeValue2749, nodeValue2750, nodeValue2752, nodeValue2756, nodeValue2757, nodeValue2763, nodeValue2764, nodeValue2766, nodeValue2773, nodeValue3104, nodeValue3105, nodeValue3109]
  ring

noncomputable def reducedSource701 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3489 x + ((1 : ℝ) * Sparse.eval nodeValue3496 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow701 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 3496, 1), (Sum.inr 3534, 2), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem reindexCheck701 : Integer.Sparse.reindex keyMap MixedData.row701 = numericRow701 := by decide +kernel

theorem numericCheck701 (x : Master → ℝ) : Integer.Sparse.eval numericRow701 x =
    (1 : ℝ) * reducedSource701 x := by
  norm_num [numericRow701, reducedSource701, Integer.Sparse.eval, Sparse.eval, nodeValue2923, nodeValue3489, nodeValue3496, nodeValue3534, nodeValue3571, nodeValue4083]

noncomputable def reducedSource702 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow702 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2243, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem reindexCheck702 : Integer.Sparse.reindex keyMap MixedData.row702 = numericRow702 := by decide +kernel

theorem numericCheck702 (x : Master → ℝ) : Integer.Sparse.eval numericRow702 x =
    (1 : ℝ) * reducedSource702 x := by
  norm_num [numericRow702, reducedSource702, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2089, nodeValue2105, nodeValue2243, nodeValue3571, nodeValue4083]

noncomputable def reducedSource703 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2923 x + ((2 : ℝ) * Sparse.eval nodeValue2926 x + ((1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow703 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 2926, 2), (Sum.inr 2950, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem reindexCheck703 : Integer.Sparse.reindex keyMap MixedData.row703 = numericRow703 := by decide +kernel

theorem numericCheck703 (x : Master → ℝ) : Integer.Sparse.eval numericRow703 x =
    (1 : ℝ) * reducedSource703 x := by
  norm_num [numericRow703, reducedSource703, Integer.Sparse.eval, Sparse.eval, nodeValue2923, nodeValue2926, nodeValue2950, nodeValue3073, nodeValue3571, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
