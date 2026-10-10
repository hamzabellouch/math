import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
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

noncomputable def reducedSource720 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2241 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2760 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + 0))))))))))))))))))))

def numericRow720 : Integer.Sparse Master := [(Sum.inl 0, -200), (Sum.inl 2, -200), (Sum.inl 3, -320), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -160), (Sum.inr 2241, 4320), (Sum.inr 2260, 8640), (Sum.inr 2275, 4320), (Sum.inr 2718, 8640), (Sum.inr 2721, 4320), (Sum.inr 2728, 4320), (Sum.inr 2747, 4320), (Sum.inr 2748, 4320), (Sum.inr 2750, 8640), (Sum.inr 2754, 4320), (Sum.inr 2760, 8640), (Sum.inr 2763, 8640), (Sum.inr 2764, 4320), (Sum.inr 2773, 8640), (Sum.inr 2782, 8640)]

theorem reindexCheck720 : Integer.Sparse.reindex keyMap MixedData.row720 = numericRow720 := by decide +kernel

theorem numericCheck720 (x : Master → ℝ) : Integer.Sparse.eval numericRow720 x =
    (4320 : ℝ) * reducedSource720 x := by
  norm_num [numericRow720, reducedSource720, Integer.Sparse.eval, Sparse.eval, nodeValue2241, nodeValue2260, nodeValue2263, nodeValue2275, nodeValue2718, nodeValue2721, nodeValue2728, nodeValue2747, nodeValue2748, nodeValue2750, nodeValue2754, nodeValue2760, nodeValue2763, nodeValue2764, nodeValue2766, nodeValue2773, nodeValue2782, nodeValue2785, nodeValue3085, nodeValue3109, nodeValue3120]
  ring

noncomputable def reducedSource721 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4589 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5100 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((2 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))

def numericRow721 : Integer.Sparse Master := [(Sum.inl 0, 29), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, 90), (Sum.inr 1235, -2160), (Sum.inr 2480, -4320), (Sum.inr 2483, -2160), (Sum.inr 2721, -4320), (Sum.inr 2723, -4320), (Sum.inr 2764, -2160), (Sum.inr 3292, -2160), (Sum.inr 3467, -4320), (Sum.inr 3477, -2160), (Sum.inr 3532, -4320), (Sum.inr 3544, -4320), (Sum.inr 3581, -2160), (Sum.inr 3849, -2160), (Sum.inr 3875, -2160), (Sum.inr 3901, -4320), (Sum.inr 4589, 8640), (Sum.inr 4590, 17280), (Sum.inr 4599, 8640), (Sum.inr 5185, 17280), (Sum.inr 5187, 8640), (Sum.inr 5197, 8640), (Sum.inr 5251, 17280), (Sum.inr 5281, 17280)]

theorem reindexCheck721 : Integer.Sparse.reindex keyMap MixedData.row721 = numericRow721 := by decide +kernel

theorem numericCheck721 (x : Master → ℝ) : Integer.Sparse.eval numericRow721 x =
    (8640 : ℝ) * reducedSource721 x := by
  norm_num [numericRow721, reducedSource721, Integer.Sparse.eval, Sparse.eval, nodeValue4589, nodeValue4590, nodeValue4599, nodeValue4601, nodeValue5073, nodeValue5076, nodeValue5100, nodeValue5185, nodeValue5187, nodeValue5197, nodeValue5250, nodeValue5251, nodeValue5257, nodeValue5259, nodeValue5273, nodeValue5281, nodeValue5290, nodeValue5408, nodeValue5431, nodeValue5433, nodeValue5440]
  ring

noncomputable def reducedSource722 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((2 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2986 x + ((2 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2999 x + ((2 : ℝ) * Sparse.eval nodeValue3064 x + ((2 : ℝ) * Sparse.eval nodeValue3065 x + ((2 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((2 : ℝ) * Sparse.eval nodeValue4033 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + ((1 : ℝ) * Sparse.eval nodeValue4038 x + 0))))))))))))))))))))

def numericRow722 : Integer.Sparse Master := [(Sum.inl 0, -129), (Sum.inl 5, -320), (Sum.inl 6, 35), (Sum.inl 2, 300), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 400), (Sum.inl 3, 1200), (Sum.inl 52, 160), (Sum.inl 12, 320), (Sum.inl 25, -120), (Sum.inl 26, 240), (Sum.inl 4, 560), (Sum.inl 1, -510), (Sum.inr 1212, 2160), (Sum.inr 1213, 4320), (Sum.inr 1233, 2160), (Sum.inr 2861, 2160), (Sum.inr 2862, 4320), (Sum.inr 2878, 2160), (Sum.inr 3064, 4320), (Sum.inr 3074, 4320)]

theorem reindexCheck722 : Integer.Sparse.reindex keyMap MixedData.row722 = numericRow722 := by decide +kernel

theorem numericCheck722 (x : Master → ℝ) : Integer.Sparse.eval numericRow722 x =
    (2160 : ℝ) * reducedSource722 x := by
  norm_num [numericRow722, reducedSource722, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue1213, nodeValue1233, nodeValue1265, nodeValue2861, nodeValue2862, nodeValue2878, nodeValue2986, nodeValue2987, nodeValue2999, nodeValue3064, nodeValue3065, nodeValue3074, nodeValue3087, nodeValue3088, nodeValue3099, nodeValue3111, nodeValue4026, nodeValue4033, nodeValue4036, nodeValue4038]
  ring

noncomputable def reducedSource723 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3469 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((2 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + 0))))))))))))))))))))

def numericRow723 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, -90), (Sum.inr 3288, 2160), (Sum.inr 3289, 2160), (Sum.inr 3290, 4320), (Sum.inr 3292, 2160), (Sum.inr 3467, 4320), (Sum.inr 3477, 2160), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3537, 2160), (Sum.inr 3539, 4320), (Sum.inr 3544, 4320), (Sum.inr 3569, 2160), (Sum.inr 3571, 4320), (Sum.inr 3581, 2160), (Sum.inr 3849, 2160)]

theorem reindexCheck723 : Integer.Sparse.reindex keyMap MixedData.row723 = numericRow723 := by decide +kernel

theorem numericCheck723 (x : Master → ℝ) : Integer.Sparse.eval numericRow723 x =
    (2160 : ℝ) * reducedSource723 x := by
  norm_num [numericRow723, reducedSource723, Integer.Sparse.eval, Sparse.eval, nodeValue3288, nodeValue3289, nodeValue3290, nodeValue3292, nodeValue3467, nodeValue3469, nodeValue3477, nodeValue3529, nodeValue3531, nodeValue3532, nodeValue3537, nodeValue3539, nodeValue3544, nodeValue3546, nodeValue3569, nodeValue3571, nodeValue3581, nodeValue3806, nodeValue3849, nodeValue3851, nodeValue3859]
  ring

noncomputable def reducedSource724 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1235 x + ((1 : ℝ) * Sparse.eval nodeValue2510 x + ((3 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow724 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 2721, 3), (Sum.inr 4091, -1)]

theorem reindexCheck724 : Integer.Sparse.reindex keyMap MixedData.row724 = numericRow724 := by decide +kernel

theorem numericCheck724 (x : Master → ℝ) : Integer.Sparse.eval numericRow724 x =
    (1 : ℝ) * reducedSource724 x := by
  norm_num [numericRow724, reducedSource724, Integer.Sparse.eval, Sparse.eval, nodeValue1235, nodeValue2510, nodeValue2721, nodeValue2741, nodeValue4091]

noncomputable def reducedSource725 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow725 : Integer.Sparse Master := [(Sum.inr 2615, 2), (Sum.inr 2617, 1), (Sum.inr 2631, 1), (Sum.inr 2721, 1), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem reindexCheck725 : Integer.Sparse.reindex keyMap MixedData.row725 = numericRow725 := by decide +kernel

theorem numericCheck725 (x : Master → ℝ) : Integer.Sparse.eval numericRow725 x =
    (1 : ℝ) * reducedSource725 x := by
  norm_num [numericRow725, reducedSource725, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue2617, nodeValue2631, nodeValue2721, nodeValue3875, nodeValue4091]

noncomputable def reducedSource726 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4996 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((1 : ℝ) * Sparse.eval nodeValue5013 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + 0))))))))))))))))))))

def numericRow726 : Integer.Sparse Master := [(Sum.inl 0, 458), (Sum.inl 6, 15), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -80), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 977, -8640), (Sum.inr 980, -4320), (Sum.inr 998, -4320), (Sum.inr 1039, -4320), (Sum.inr 1597, -8640), (Sum.inr 1600, -4320), (Sum.inr 1616, -4320), (Sum.inr 1706, -4320), (Sum.inr 2382, -8640), (Sum.inr 2383, -4320), (Sum.inr 2398, -4320), (Sum.inr 2553, -8640), (Sum.inr 2556, -4320), (Sum.inr 2694, -8640), (Sum.inr 2703, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -8640), (Sum.inr 2723, -8640), (Sum.inr 2739, -8640), (Sum.inr 3340, -8640), (Sum.inr 3341, -4320), (Sum.inr 3352, -4320), (Sum.inr 3493, -8640), (Sum.inr 3496, -4320), (Sum.inr 3514, -8640), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -8640), (Sum.inr 3534, -8640), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3622, -8640), (Sum.inr 3957, -8640), (Sum.inr 4046, -4320)]

theorem reindexCheck726 : Integer.Sparse.reindex keyMap MixedData.row726 = numericRow726 := by decide +kernel

theorem numericCheck726 (x : Master → ℝ) : Integer.Sparse.eval numericRow726 x =
    (17280 : ℝ) * reducedSource726 x := by
  norm_num [numericRow726, reducedSource726, Integer.Sparse.eval, Sparse.eval, nodeValue4396, nodeValue4399, nodeValue4417, nodeValue4456, nodeValue4996, nodeValue4998, nodeValue5013, nodeValue5134, nodeValue5137, nodeValue5167, nodeValue5241, nodeValue5247, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5472, nodeValue5482, nodeValue5489, nodeValue5490]
  ring

noncomputable def reducedSource727 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2383 x + ((1 : ℝ) * Sparse.eval nodeValue2398 x + ((2 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue4009 x + ((2 : ℝ) * Sparse.eval nodeValue4013 x + 0))))))))))))))))))))

def numericRow727 : Integer.Sparse Master := [(Sum.inl 0, -324), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, 30), (Sum.inr 977, 8640), (Sum.inr 980, 4320), (Sum.inr 998, 4320), (Sum.inr 1039, 4320), (Sum.inr 2382, 8640), (Sum.inr 2383, 4320), (Sum.inr 2398, 4320), (Sum.inr 2553, 8640), (Sum.inr 2556, 4320), (Sum.inr 2694, 8640), (Sum.inr 2703, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2739, 8640), (Sum.inr 3957, 4320)]

theorem reindexCheck727 : Integer.Sparse.reindex keyMap MixedData.row727 = numericRow727 := by decide +kernel

theorem numericCheck727 (x : Master → ℝ) : Integer.Sparse.eval numericRow727 x =
    (4320 : ℝ) * reducedSource727 x := by
  norm_num [numericRow727, reducedSource727, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue980, nodeValue998, nodeValue1039, nodeValue2382, nodeValue2383, nodeValue2398, nodeValue2553, nodeValue2556, nodeValue2593, nodeValue2694, nodeValue2703, nodeValue2721, nodeValue2722, nodeValue2723, nodeValue2739, nodeValue2766, nodeValue3957, nodeValue3992, nodeValue4009, nodeValue4013]
  ring

noncomputable def reducedSource728 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((3 : ℝ) * Sparse.eval nodeValue5256 x + ((4 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((3 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))

def numericRow728 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2020, -2880), (Sum.inr 2023, -1440), (Sum.inr 2202, -2880), (Sum.inr 2214, -1440), (Sum.inr 2671, -1440), (Sum.inr 2721, -5760), (Sum.inr 2739, -2880), (Sum.inr 2764, -1440), (Sum.inr 3390, -1440), (Sum.inr 3532, -5760), (Sum.inr 3534, -2880), (Sum.inr 3581, -1440), (Sum.inr 3622, -4320), (Sum.inr 5226, 11520), (Sum.inr 5231, 5760), (Sum.inr 5255, 11520), (Sum.inr 5263, 5760), (Sum.inr 5265, 17280)]

theorem reindexCheck728 : Integer.Sparse.reindex keyMap MixedData.row728 = numericRow728 := by decide +kernel

theorem numericCheck728 (x : Master → ℝ) : Integer.Sparse.eval numericRow728 x =
    (5760 : ℝ) * reducedSource728 x := by
  norm_num [numericRow728, reducedSource728, Integer.Sparse.eval, Sparse.eval, nodeValue4802, nodeValue4805, nodeValue4833, nodeValue4893, nodeValue5226, nodeValue5227, nodeValue5231, nodeValue5255, nodeValue5256, nodeValue5257, nodeValue5263, nodeValue5265, nodeValue5271, nodeValue5273, nodeValue5290, nodeValue5292, nodeValue5307]
  ring

noncomputable def reducedSource729 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + 0))))))))))))))))))))

def numericRow729 : Integer.Sparse Master := [(Sum.inl 0, -175), (Sum.inl 2, -135), (Sum.inl 3, 560), (Sum.inl 26, 320), (Sum.inl 4, 320), (Sum.inl 1, -380), (Sum.inr 2202, 8640), (Sum.inr 2214, 4320), (Sum.inr 2669, 8640), (Sum.inr 2671, 4320), (Sum.inr 2676, 4320), (Sum.inr 2718, 8640), (Sum.inr 2721, 8640), (Sum.inr 2728, 4320), (Sum.inr 2730, 8640), (Sum.inr 2739, 8640), (Sum.inr 2764, 4320), (Sum.inr 3037, 4320)]

theorem reindexCheck729 : Integer.Sparse.reindex keyMap MixedData.row729 = numericRow729 := by decide +kernel

theorem numericCheck729 (x : Master → ℝ) : Integer.Sparse.eval numericRow729 x =
    (4320 : ℝ) * reducedSource729 x := by
  norm_num [numericRow729, reducedSource729, Integer.Sparse.eval, Sparse.eval, nodeValue2202, nodeValue2204, nodeValue2214, nodeValue2263, nodeValue2669, nodeValue2671, nodeValue2676, nodeValue2718, nodeValue2720, nodeValue2721, nodeValue2728, nodeValue2730, nodeValue2739, nodeValue2741, nodeValue2764, nodeValue2766, nodeValue2785, nodeValue3037, nodeValue3085, nodeValue3087, nodeValue3100]
  ring

noncomputable def reducedSource730 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5160 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5164 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

def numericRow730 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 25), (Sum.inr 1294, -2160), (Sum.inr 2590, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 3305, -2160), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3564, -4320), (Sum.inr 3582, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 4616, 17280), (Sum.inr 4617, 8640), (Sum.inr 4620, 8640), (Sum.inr 5160, 17280), (Sum.inr 5164, 17280), (Sum.inr 5173, 17280), (Sum.inr 5276, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640)]

theorem reindexCheck730 : Integer.Sparse.reindex keyMap MixedData.row730 = numericRow730 := by decide +kernel

theorem numericCheck730 (x : Master → ℝ) : Integer.Sparse.eval numericRow730 x =
    (8640 : ℝ) * reducedSource730 x := by
  norm_num [numericRow730, reducedSource730, Integer.Sparse.eval, Sparse.eval, nodeValue4616, nodeValue4617, nodeValue4619, nodeValue4620, nodeValue5160, nodeValue5163, nodeValue5164, nodeValue5173, nodeValue5271, nodeValue5274, nodeValue5275, nodeValue5276, nodeValue5289, nodeValue5291, nodeValue5295, nodeValue5299, nodeValue5300, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5451]
  ring

noncomputable def reducedSource731 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2951 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((2 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

def numericRow731 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -30), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, 100), (Sum.inr 1291, 2880), (Sum.inr 1292, 1440), (Sum.inr 1295, 1440), (Sum.inr 2951, 2880), (Sum.inr 2952, 2880), (Sum.inr 2955, 2880), (Sum.inr 3051, 2880), (Sum.inr 3052, 1440), (Sum.inr 3055, 1440), (Sum.inr 3097, 2880), (Sum.inr 3098, 1440)]

theorem reindexCheck731 : Integer.Sparse.reindex keyMap MixedData.row731 = numericRow731 := by decide +kernel

theorem numericCheck731 (x : Master → ℝ) : Integer.Sparse.eval numericRow731 x =
    (1440 : ℝ) * reducedSource731 x := by
  norm_num [numericRow731, reducedSource731, Integer.Sparse.eval, Sparse.eval, nodeValue1291, nodeValue1292, nodeValue1295, nodeValue1302, nodeValue2951, nodeValue2952, nodeValue2955, nodeValue2961, nodeValue3051, nodeValue3052, nodeValue3055, nodeValue3097, nodeValue3098, nodeValue3103, nodeValue3109, nodeValue3110, nodeValue3112, nodeValue3862, nodeValue3987, nodeValue3993, nodeValue4001]
  ring

noncomputable def reducedSource732 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3558 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow732 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2744, 2160), (Sum.inr 2781, 2160), (Sum.inr 3303, 4320), (Sum.inr 3305, 2160), (Sum.inr 3306, 2160), (Sum.inr 3534, 4320), (Sum.inr 3548, 2160), (Sum.inr 3558, 4320), (Sum.inr 3564, 4320), (Sum.inr 3565, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3582, 2160), (Sum.inr 3584, 2160), (Sum.inr 3876, 4320)]

theorem reindexCheck732 : Integer.Sparse.reindex keyMap MixedData.row732 = numericRow732 := by decide +kernel

theorem numericCheck732 (x : Master → ℝ) : Integer.Sparse.eval numericRow732 x =
    (2160 : ℝ) * reducedSource732 x := by
  norm_num [numericRow732, reducedSource732, Integer.Sparse.eval, Sparse.eval, nodeValue2735, nodeValue2737, nodeValue2744, nodeValue2781, nodeValue3303, nodeValue3305, nodeValue3306, nodeValue3534, nodeValue3547, nodeValue3548, nodeValue3558, nodeValue3564, nodeValue3565, nodeValue3572, nodeValue3573, nodeValue3582, nodeValue3584, nodeValue3861, nodeValue3876, nodeValue3888, nodeValue3889]
  ring

noncomputable def reducedSource733 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4489 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4491 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5093 x + ((2 : ℝ) * Sparse.eval nodeValue5094 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))))))))))

def numericRow733 : Integer.Sparse Master := [(Sum.inl 0, 28), (Sum.inl 2, -7), (Sum.inl 3, 16), (Sum.inl 4, 48), (Sum.inl 1, -31), (Sum.inr 1073, -864), (Sum.inr 1074, -432), (Sum.inr 1075, -432), (Sum.inr 1087, -432), (Sum.inr 1648, -864), (Sum.inr 1650, -432), (Sum.inr 1653, -432), (Sum.inr 1739, -432), (Sum.inr 2503, -864), (Sum.inr 2504, -1728), (Sum.inr 2505, -864), (Sum.inr 2515, -864), (Sum.inr 2522, -432), (Sum.inr 2684, -864), (Sum.inr 2685, -432), (Sum.inr 2686, -432), (Sum.inr 2764, -864), (Sum.inr 2765, -432), (Sum.inr 2782, -864), (Sum.inr 2783, -864), (Sum.inr 3394, -864), (Sum.inr 3397, -432), (Sum.inr 3446, -864), (Sum.inr 3448, -864), (Sum.inr 3479, -864), (Sum.inr 3581, -864), (Sum.inr 3582, -432), (Sum.inr 3583, -864), (Sum.inr 3632, -432), (Sum.inr 3633, -432), (Sum.inr 3913, -432), (Sum.inr 3983, -1728)]

theorem reindexCheck733 : Integer.Sparse.reindex keyMap MixedData.row733 = numericRow733 := by decide +kernel

theorem numericCheck733 (x : Master → ℝ) : Integer.Sparse.eval numericRow733 x =
    (1728 : ℝ) * reducedSource733 x := by
  norm_num [numericRow733, reducedSource733, Integer.Sparse.eval, Sparse.eval, nodeValue4489, nodeValue4490, nodeValue4491, nodeValue4503, nodeValue5093, nodeValue5094, nodeValue5095, nodeValue5105, nodeValue5110, nodeValue5237, nodeValue5238, nodeValue5290, nodeValue5291, nodeValue5294, nodeValue5304, nodeValue5305, nodeValue5310, nodeValue5451, nodeValue5484, nodeValue5492, nodeValue5494]
  ring

noncomputable def reducedSource734 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2503 x + ((2 : ℝ) * Sparse.eval nodeValue2504 x + ((2 : ℝ) * Sparse.eval nodeValue2505 x + ((2 : ℝ) * Sparse.eval nodeValue2515 x + ((2 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + 0))))))))))))))))))))

def numericRow734 : Integer.Sparse Master := [(Sum.inl 0, -39), (Sum.inl 2, 20), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 1073, 2160), (Sum.inr 1074, 1080), (Sum.inr 1075, 1080), (Sum.inr 1087, 1080), (Sum.inr 2503, 2160), (Sum.inr 2504, 2160), (Sum.inr 2505, 2160), (Sum.inr 2515, 2160), (Sum.inr 2684, 2160), (Sum.inr 2685, 1080), (Sum.inr 2686, 1080), (Sum.inr 2764, 2160), (Sum.inr 2765, 1080), (Sum.inr 2782, 2160), (Sum.inr 2783, 1080), (Sum.inr 3913, 1080), (Sum.inr 3983, 2160)]

theorem reindexCheck734 : Integer.Sparse.reindex keyMap MixedData.row734 = numericRow734 := by decide +kernel

theorem numericCheck734 (x : Master → ℝ) : Integer.Sparse.eval numericRow734 x =
    (1080 : ℝ) * reducedSource734 x := by
  norm_num [numericRow734, reducedSource734, Integer.Sparse.eval, Sparse.eval, nodeValue1073, nodeValue1074, nodeValue1075, nodeValue1087, nodeValue2503, nodeValue2504, nodeValue2505, nodeValue2515, nodeValue2684, nodeValue2685, nodeValue2686, nodeValue2764, nodeValue2765, nodeValue2768, nodeValue2782, nodeValue2783, nodeValue2788, nodeValue3913, nodeValue3983, nodeValue4017, nodeValue4020]
  ring

noncomputable def reducedSource735 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((2 : ℝ) * Sparse.eval nodeValue5269 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((4 : ℝ) * Sparse.eval nodeValue5289 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))

def numericRow735 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 2107, -2160), (Sum.inr 2112, -1080), (Sum.inr 2116, -1080), (Sum.inr 2260, -2160), (Sum.inr 2287, -1080), (Sum.inr 2288, -1080), (Sum.inr 2739, -2160), (Sum.inr 2764, -2160), (Sum.inr 2782, -2160), (Sum.inr 3534, -2160), (Sum.inr 3581, -2160), (Sum.inr 3583, -2160), (Sum.inr 3623, -2160), (Sum.inr 5173, 8640), (Sum.inr 5175, 4320), (Sum.inr 5255, 8640), (Sum.inr 5269, 8640), (Sum.inr 5288, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640), (Sum.inr 5303, 4320)]

theorem reindexCheck735 : Integer.Sparse.reindex keyMap MixedData.row735 = numericRow735 := by decide +kernel

theorem numericCheck735 (x : Master → ℝ) : Integer.Sparse.eval numericRow735 x =
    (4320 : ℝ) * reducedSource735 x := by
  norm_num [numericRow735, reducedSource735, Integer.Sparse.eval, Sparse.eval, nodeValue4866, nodeValue4871, nodeValue4875, nodeValue4895, nodeValue5173, nodeValue5175, nodeValue5255, nodeValue5269, nodeValue5271, nodeValue5288, nodeValue5289, nodeValue5290, nodeValue5295, nodeValue5303, nodeValue5304, nodeValue5306, nodeValue5307]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
