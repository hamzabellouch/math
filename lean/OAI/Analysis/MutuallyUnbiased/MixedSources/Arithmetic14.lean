import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource224 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow224 : Integer.Sparse Master := [(Sum.inr 2714, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem reindexCheck224 : Integer.Sparse.reindex keyMap MixedData.row224 = numericRow224 := by decide +kernel

theorem numericCheck224 (x : Master → ℝ) : Integer.Sparse.eval numericRow224 x =
    (1 : ℝ) * reducedSource224 x := by
  norm_num [numericRow224, reducedSource224, Integer.Sparse.eval, Sparse.eval, nodeValue2714, nodeValue2716, nodeValue2724, nodeValue2732, nodeValue2758, nodeValue3814, nodeValue4092]

noncomputable def reducedSource225 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1218 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow225 : Integer.Sparse Master := [(Sum.inr 1218, 1), (Sum.inr 2486, 1), (Sum.inr 2544, 1), (Sum.inr 2619, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem reindexCheck225 : Integer.Sparse.reindex keyMap MixedData.row225 = numericRow225 := by decide +kernel

theorem numericCheck225 (x : Master → ℝ) : Integer.Sparse.eval numericRow225 x =
    (1 : ℝ) * reducedSource225 x := by
  norm_num [numericRow225, reducedSource225, Integer.Sparse.eval, Sparse.eval, nodeValue1218, nodeValue2486, nodeValue2544, nodeValue2619, nodeValue2716, nodeValue2724, nodeValue4092]

noncomputable def reducedSource226 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3431 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

def numericRow226 : Integer.Sparse Master := [(Sum.inl 0, -96), (Sum.inl 2, 50), (Sum.inl 3, -480), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 1, -390), (Sum.inr 1607, 8640), (Sum.inr 1608, 8640), (Sum.inr 1612, 8640), (Sum.inr 1619, 8640), (Sum.inr 1714, 8640), (Sum.inr 2534, 8640), (Sum.inr 2538, 8640), (Sum.inr 2588, 8640), (Sum.inr 2670, 8640), (Sum.inr 3346, 8640), (Sum.inr 3349, 8640), (Sum.inr 3355, 8640), (Sum.inr 3431, 8640), (Sum.inr 3434, 8640), (Sum.inr 3463, 8640), (Sum.inr 3503, 8640), (Sum.inr 3507, 8640), (Sum.inr 3517, 8640), (Sum.inr 3523, 8640), (Sum.inr 3539, 8640), (Sum.inr 3540, 8640), (Sum.inr 3543, 8640), (Sum.inr 3572, 8640), (Sum.inr 3606, 8640), (Sum.inr 3625, 8640), (Sum.inr 3848, 8640), (Sum.inr 3857, 8640), (Sum.inr 3884, 8640)]

theorem reindexCheck226 : Integer.Sparse.reindex keyMap MixedData.row226 = numericRow226 := by decide +kernel

theorem numericCheck226 (x : Master → ℝ) : Integer.Sparse.eval numericRow226 x =
    (8640 : ℝ) * reducedSource226 x := by
  norm_num [numericRow226, reducedSource226, Integer.Sparse.eval, Sparse.eval, nodeValue1607, nodeValue1608, nodeValue1612, nodeValue1619, nodeValue1714, nodeValue2534, nodeValue2538, nodeValue2588, nodeValue2670, nodeValue3346, nodeValue3349, nodeValue3355, nodeValue3431, nodeValue3434, nodeValue3463, nodeValue3503, nodeValue3507, nodeValue3517, nodeValue3523, nodeValue3539, nodeValue3540, nodeValue3543, nodeValue3572, nodeValue3606, nodeValue3625, nodeValue3848, nodeValue3857, nodeValue3858, nodeValue3884, nodeValue3997]
  ring

noncomputable def reducedSource227 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow227 : Integer.Sparse Master := [(Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3902, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem reindexCheck227 : Integer.Sparse.reindex keyMap MixedData.row227 = numericRow227 := by decide +kernel

theorem numericCheck227 (x : Master → ℝ) : Integer.Sparse.eval numericRow227 x =
    (1 : ℝ) * reducedSource227 x := by
  norm_num [numericRow227, reducedSource227, Integer.Sparse.eval, Sparse.eval, nodeValue3086, nodeValue3871, nodeValue3876, nodeValue3881, nodeValue3902, nodeValue3983, nodeValue4091]

noncomputable def reducedSource228 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue1400 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1425 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow228 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 1394, 1), (Sum.inr 1400, 1), (Sum.inr 1406, 1), (Sum.inr 1425, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem reindexCheck228 : Integer.Sparse.reindex keyMap MixedData.row228 = numericRow228 := by decide +kernel

theorem numericCheck228 (x : Master → ℝ) : Integer.Sparse.eval numericRow228 x =
    (1 : ℝ) * reducedSource228 x := by
  norm_num [numericRow228, reducedSource228, Integer.Sparse.eval, Sparse.eval, nodeValue1392, nodeValue1394, nodeValue1400, nodeValue1406, nodeValue1425, nodeValue3086, nodeValue4091]

noncomputable def reducedSource229 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow229 : Integer.Sparse Master := [(Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem reindexCheck229 : Integer.Sparse.reindex keyMap MixedData.row229 = numericRow229 := by decide +kernel

theorem numericCheck229 (x : Master → ℝ) : Integer.Sparse.eval numericRow229 x =
    (1 : ℝ) * reducedSource229 x := by
  norm_num [numericRow229, reducedSource229, Integer.Sparse.eval, Sparse.eval, nodeValue1406, nodeValue2954, nodeValue2984, nodeValue3077, nodeValue3086, nodeValue3097, nodeValue4091]

noncomputable def reducedSource230 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2949 x + ((1 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3014 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow230 : Integer.Sparse Master := [(Sum.inr 2624, 1), (Sum.inr 2949, 1), (Sum.inr 3013, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem reindexCheck230 : Integer.Sparse.reindex keyMap MixedData.row230 = numericRow230 := by decide +kernel

theorem numericCheck230 (x : Master → ℝ) : Integer.Sparse.eval numericRow230 x =
    (1 : ℝ) * reducedSource230 x := by
  norm_num [numericRow230, reducedSource230, Integer.Sparse.eval, Sparse.eval, nodeValue2624, nodeValue2949, nodeValue3013, nodeValue3014, nodeValue3086, nodeValue3881, nodeValue4091]

noncomputable def reducedSource231 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow231 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 2933, 1), (Sum.inr 3013, 1), (Sum.inr 3064, 1), (Sum.inr 3084, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem reindexCheck231 : Integer.Sparse.reindex keyMap MixedData.row231 = numericRow231 := by decide +kernel

theorem numericCheck231 (x : Master → ℝ) : Integer.Sparse.eval numericRow231 x =
    (1 : ℝ) * reducedSource231 x := by
  norm_num [numericRow231, reducedSource231, Integer.Sparse.eval, Sparse.eval, nodeValue1392, nodeValue2933, nodeValue3013, nodeValue3064, nodeValue3084, nodeValue3086, nodeValue4091]

noncomputable def reducedSource232 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2947 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2992 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow232 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2947, 1), (Sum.inr 2984, 1), (Sum.inr 2992, 1), (Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

theorem reindexCheck232 : Integer.Sparse.reindex keyMap MixedData.row232 = numericRow232 := by decide +kernel

theorem numericCheck232 (x : Master → ℝ) : Integer.Sparse.eval numericRow232 x =
    (1 : ℝ) * reducedSource232 x := by
  norm_num [numericRow232, reducedSource232, Integer.Sparse.eval, Sparse.eval, nodeValue2610, nodeValue2947, nodeValue2984, nodeValue2992, nodeValue3086, nodeValue3871, nodeValue4091]

noncomputable def reducedSource233 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1425 x + ((1 : ℝ) * Sparse.eval nodeValue2992 x + ((1 : ℝ) * Sparse.eval nodeValue3014 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow233 : Integer.Sparse Master := [(Sum.inr 1425, 1), (Sum.inr 2992, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 2), (Sum.inr 3108, 1), (Sum.inr 4091, -1)]

theorem reindexCheck233 : Integer.Sparse.reindex keyMap MixedData.row233 = numericRow233 := by decide +kernel

theorem numericCheck233 (x : Master → ℝ) : Integer.Sparse.eval numericRow233 x =
    (1 : ℝ) * reducedSource233 x := by
  norm_num [numericRow233, reducedSource233, Integer.Sparse.eval, Sparse.eval, nodeValue1425, nodeValue2992, nodeValue3014, nodeValue3086, nodeValue3108, nodeValue4091]

noncomputable def reducedSource234 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow234 : Integer.Sparse Master := [(Sum.inr 2618, 1), (Sum.inr 2933, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 3086, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem reindexCheck234 : Integer.Sparse.reindex keyMap MixedData.row234 = numericRow234 := by decide +kernel

theorem numericCheck234 (x : Master → ℝ) : Integer.Sparse.eval numericRow234 x =
    (1 : ℝ) * reducedSource234 x := by
  norm_num [numericRow234, reducedSource234, Integer.Sparse.eval, Sparse.eval, nodeValue2618, nodeValue2933, nodeValue2942, nodeValue2954, nodeValue3086, nodeValue3876, nodeValue4091]

noncomputable def reducedSource235 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1400 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2947 x + ((1 : ℝ) * Sparse.eval nodeValue2949 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow235 : Integer.Sparse Master := [(Sum.inr 1400, 1), (Sum.inr 2942, 1), (Sum.inr 2947, 1), (Sum.inr 2949, 1), (Sum.inr 2964, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem reindexCheck235 : Integer.Sparse.reindex keyMap MixedData.row235 = numericRow235 := by decide +kernel

theorem numericCheck235 (x : Master → ℝ) : Integer.Sparse.eval numericRow235 x =
    (1 : ℝ) * reducedSource235 x := by
  norm_num [numericRow235, reducedSource235, Integer.Sparse.eval, Sparse.eval, nodeValue1400, nodeValue2942, nodeValue2947, nodeValue2949, nodeValue2964, nodeValue3086, nodeValue4091]

noncomputable def reducedSource236 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2496 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2498 x + ((1 : ℝ) * Sparse.eval nodeValue2516 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3028 x + ((1 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3042 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3211 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))))))))))

def numericRow236 : Integer.Sparse Master := [(Sum.inl 0, -812), (Sum.inl 6, 20), (Sum.inl 2, 1100), (Sum.inl 3, -640), (Sum.inl 13, 320), (Sum.inl 52, -320), (Sum.inl 1, 980), (Sum.inr 2496, 17280), (Sum.inr 2497, 17280), (Sum.inr 2498, 17280), (Sum.inr 2516, 17280), (Sum.inr 2708, 17280), (Sum.inr 2719, 17280), (Sum.inr 2722, 17280), (Sum.inr 2729, 17280), (Sum.inr 2765, 17280), (Sum.inr 2777, 17280), (Sum.inr 3028, 17280), (Sum.inr 3035, 17280), (Sum.inr 3038, 17280), (Sum.inr 3042, 17280), (Sum.inr 3063, 17280), (Sum.inr 3064, 17280), (Sum.inr 3067, 17280), (Sum.inr 3086, 34560), (Sum.inr 3092, 17280), (Sum.inr 3098, 17280), (Sum.inr 3197, 17280), (Sum.inr 3198, 17280)]

theorem reindexCheck236 : Integer.Sparse.reindex keyMap MixedData.row236 = numericRow236 := by decide +kernel

theorem numericCheck236 (x : Master → ℝ) : Integer.Sparse.eval numericRow236 x =
    (17280 : ℝ) * reducedSource236 x := by
  norm_num [numericRow236, reducedSource236, Integer.Sparse.eval, Sparse.eval, nodeValue2496, nodeValue2497, nodeValue2498, nodeValue2516, nodeValue2708, nodeValue2719, nodeValue2722, nodeValue2729, nodeValue2765, nodeValue2777, nodeValue3028, nodeValue3035, nodeValue3038, nodeValue3042, nodeValue3063, nodeValue3064, nodeValue3067, nodeValue3080, nodeValue3086, nodeValue3088, nodeValue3092, nodeValue3098, nodeValue3101, nodeValue3110, nodeValue3121, nodeValue3197, nodeValue3198, nodeValue3211, nodeValue3225]
  ring

noncomputable def reducedSource237 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow237 : Integer.Sparse Master := [(Sum.inr 2588, 1), (Sum.inr 3502, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3540, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem reindexCheck237 : Integer.Sparse.reindex keyMap MixedData.row237 = numericRow237 := by decide +kernel

theorem numericCheck237 (x : Master → ℝ) : Integer.Sparse.eval numericRow237 x =
    (1 : ℝ) * reducedSource237 x := by
  norm_num [numericRow237, reducedSource237, Integer.Sparse.eval, Sparse.eval, nodeValue2588, nodeValue3502, nodeValue3506, nodeValue3533, nodeValue3540, nodeValue3582, nodeValue4084]

noncomputable def reducedSource238 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow238 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2054, 1), (Sum.inr 2278, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

theorem reindexCheck238 : Integer.Sparse.reindex keyMap MixedData.row238 = numericRow238 := by decide +kernel

theorem numericCheck238 (x : Master → ℝ) : Integer.Sparse.eval numericRow238 x =
    (1 : ℝ) * reducedSource238 x := by
  norm_num [numericRow238, reducedSource238, Integer.Sparse.eval, Sparse.eval, nodeValue2033, nodeValue2035, nodeValue2039, nodeValue2054, nodeValue2278, nodeValue3540, nodeValue4084]

noncomputable def reducedSource239 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow239 : Integer.Sparse Master := [(Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 3540, 2), (Sum.inr 3632, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck239 : Integer.Sparse.reindex keyMap MixedData.row239 = numericRow239 := by decide +kernel

theorem numericCheck239 (x : Master → ℝ) : Integer.Sparse.eval numericRow239 x =
    (1 : ℝ) * reducedSource239 x := by
  norm_num [numericRow239, reducedSource239, Integer.Sparse.eval, Sparse.eval, nodeValue2278, nodeValue2781, nodeValue3540, nodeValue3632, nodeValue3633, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
