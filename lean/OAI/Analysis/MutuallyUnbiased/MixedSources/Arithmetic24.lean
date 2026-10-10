import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource384 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2962 x + ((1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue2995 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow384 : Integer.Sparse Master := [(Sum.inr 2090, 1), (Sum.inr 2962, 1), (Sum.inr 2983, 1), (Sum.inr 2995, 1), (Sum.inr 3098, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem reindexCheck384 : Integer.Sparse.reindex keyMap MixedData.row384 = numericRow384 := by decide +kernel

theorem numericCheck384 (x : Master → ℝ) : Integer.Sparse.eval numericRow384 x =
    (1 : ℝ) * reducedSource384 x := by
  norm_num [numericRow384, reducedSource384, Integer.Sparse.eval, Sparse.eval, nodeValue2090, nodeValue2962, nodeValue2983, nodeValue2995, nodeValue3098, nodeValue3572, nodeValue4083]

noncomputable def reducedSource385 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1440 x + ((2 : ℝ) * Sparse.eval nodeValue2995 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow385 : Integer.Sparse Master := [(Sum.inr 1440, 1), (Sum.inr 2995, 2), (Sum.inr 3098, 2), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

theorem reindexCheck385 : Integer.Sparse.reindex keyMap MixedData.row385 = numericRow385 := by decide +kernel

theorem numericCheck385 (x : Master → ℝ) : Integer.Sparse.eval numericRow385 x =
    (1 : ℝ) * reducedSource385 x := by
  norm_num [numericRow385, reducedSource385, Integer.Sparse.eval, Sparse.eval, nodeValue1440, nodeValue2995, nodeValue3098, nodeValue3118, nodeValue4083]

noncomputable def reducedSource386 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2112 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow386 : Integer.Sparse Master := [(Sum.inr 2112, 1), (Sum.inr 2952, 2), (Sum.inr 2967, 1), (Sum.inr 3098, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem reindexCheck386 : Integer.Sparse.reindex keyMap MixedData.row386 = numericRow386 := by decide +kernel

theorem numericCheck386 (x : Master → ℝ) : Integer.Sparse.eval numericRow386 x =
    (1 : ℝ) * reducedSource386 x := by
  norm_num [numericRow386, reducedSource386, Integer.Sparse.eval, Sparse.eval, nodeValue2112, nodeValue2952, nodeValue2967, nodeValue3098, nodeValue3583, nodeValue4083]

noncomputable def reducedSource387 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1418 x + ((2 : ℝ) * Sparse.eval nodeValue2962 x + ((2 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow387 : Integer.Sparse Master := [(Sum.inr 1418, 1), (Sum.inr 2962, 2), (Sum.inr 2967, 2), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem reindexCheck387 : Integer.Sparse.reindex keyMap MixedData.row387 = numericRow387 := by decide +kernel

theorem numericCheck387 (x : Master → ℝ) : Integer.Sparse.eval numericRow387 x =
    (1 : ℝ) * reducedSource387 x := by
  norm_num [numericRow387, reducedSource387, Integer.Sparse.eval, Sparse.eval, nodeValue1418, nodeValue2962, nodeValue2967, nodeValue3098, nodeValue4083]

noncomputable def reducedSource388 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2516 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((2 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3063 x + ((2 : ℝ) * Sparse.eval nodeValue3072 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

def numericRow388 : Integer.Sparse Master := [(Sum.inl 0, -49), (Sum.inl 2, 80), (Sum.inl 3, -80), (Sum.inl 13, 80), (Sum.inl 1, 65), (Sum.inr 2516, 4320), (Sum.inr 2520, 2160), (Sum.inr 2521, 2160), (Sum.inr 2719, 4320), (Sum.inr 2737, 2160), (Sum.inr 2740, 2160), (Sum.inr 2783, 2160), (Sum.inr 2789, 2160), (Sum.inr 3035, 4320), (Sum.inr 3049, 2160), (Sum.inr 3052, 2160), (Sum.inr 3063, 4320), (Sum.inr 3072, 4320), (Sum.inr 3075, 4320), (Sum.inr 3086, 4320), (Sum.inr 3098, 4320), (Sum.inr 3158, 4320), (Sum.inr 3161, 2160)]

theorem reindexCheck388 : Integer.Sparse.reindex keyMap MixedData.row388 = numericRow388 := by decide +kernel

theorem numericCheck388 (x : Master → ℝ) : Integer.Sparse.eval numericRow388 x =
    (2160 : ℝ) * reducedSource388 x := by
  norm_num [numericRow388, reducedSource388, Integer.Sparse.eval, Sparse.eval, nodeValue2516, nodeValue2520, nodeValue2521, nodeValue2719, nodeValue2737, nodeValue2740, nodeValue2783, nodeValue2789, nodeValue3035, nodeValue3049, nodeValue3052, nodeValue3063, nodeValue3072, nodeValue3075, nodeValue3086, nodeValue3098, nodeValue3101, nodeValue3121, nodeValue3158, nodeValue3161, nodeValue3225]
  ring

noncomputable def reducedSource389 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow389 : Integer.Sparse Master := [(Sum.inr 1292, 1), (Sum.inr 2588, 2), (Sum.inr 2740, 1), (Sum.inr 2781, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

theorem reindexCheck389 : Integer.Sparse.reindex keyMap MixedData.row389 = numericRow389 := by decide +kernel

theorem numericCheck389 (x : Master → ℝ) : Integer.Sparse.eval numericRow389 x =
    (1 : ℝ) * reducedSource389 x := by
  norm_num [numericRow389, reducedSource389, Integer.Sparse.eval, Sparse.eval, nodeValue1292, nodeValue2588, nodeValue2740, nodeValue2781, nodeValue2783, nodeValue4084]

noncomputable def reducedSource390 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2132 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow390 : Integer.Sparse Master := [(Sum.inr 2132, 2), (Sum.inr 2134, 1), (Sum.inr 2138, 1), (Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

theorem reindexCheck390 : Integer.Sparse.reindex keyMap MixedData.row390 = numericRow390 := by decide +kernel

theorem numericCheck390 (x : Master → ℝ) : Integer.Sparse.eval numericRow390 x =
    (1 : ℝ) * reducedSource390 x := by
  norm_num [numericRow390, reducedSource390, Integer.Sparse.eval, Sparse.eval, nodeValue2132, nodeValue2134, nodeValue2138, nodeValue2278, nodeValue2781, nodeValue4084]

noncomputable def reducedSource391 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((2 : ℝ) * Sparse.eval nodeValue2909 x + ((2 : ℝ) * Sparse.eval nodeValue2910 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow391 : Integer.Sparse Master := [(Sum.inl 0, -124), (Sum.inl 3, 640), (Sum.inl 12, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -100), (Sum.inr 1189, 8640), (Sum.inr 1191, 4320), (Sum.inr 1192, 4320), (Sum.inr 1295, 4320), (Sum.inr 2393, 8640), (Sum.inr 2408, 4320), (Sum.inr 2734, 4320), (Sum.inr 2841, 8640), (Sum.inr 2842, 4320), (Sum.inr 2909, 8640), (Sum.inr 2910, 8640), (Sum.inr 2955, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3052, 4320), (Sum.inr 3584, 4320), (Sum.inr 3877, 8640)]

theorem reindexCheck391 : Integer.Sparse.reindex keyMap MixedData.row391 = numericRow391 := by decide +kernel

theorem numericCheck391 (x : Master → ℝ) : Integer.Sparse.eval numericRow391 x =
    (4320 : ℝ) * reducedSource391 x := by
  norm_num [numericRow391, reducedSource391, Integer.Sparse.eval, Sparse.eval, nodeValue1189, nodeValue1191, nodeValue1192, nodeValue1295, nodeValue2393, nodeValue2408, nodeValue2734, nodeValue2841, nodeValue2842, nodeValue2909, nodeValue2910, nodeValue2955, nodeValue3039, nodeValue3051, nodeValue3052, nodeValue3110, nodeValue3119, nodeValue3584, nodeValue3862, nodeValue3877, nodeValue3889]
  ring

noncomputable def reducedSource392 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3358 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3559 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow392 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 2405, 2160), (Sum.inr 2408, 1080), (Sum.inr 2409, 1080), (Sum.inr 2744, 1080), (Sum.inr 2841, 2160), (Sum.inr 2842, 1080), (Sum.inr 3055, 1080), (Sum.inr 3246, 2160), (Sum.inr 3247, 1080), (Sum.inr 3306, 1080), (Sum.inr 3358, 2160), (Sum.inr 3535, 2160), (Sum.inr 3548, 1080), (Sum.inr 3549, 1080), (Sum.inr 3559, 2160), (Sum.inr 3565, 2160), (Sum.inr 3573, 2160), (Sum.inr 3583, 1080), (Sum.inr 3877, 2160)]

theorem reindexCheck392 : Integer.Sparse.reindex keyMap MixedData.row392 = numericRow392 := by decide +kernel

theorem numericCheck392 (x : Master → ℝ) : Integer.Sparse.eval numericRow392 x =
    (1080 : ℝ) * reducedSource392 x := by
  norm_num [numericRow392, reducedSource392, Integer.Sparse.eval, Sparse.eval, nodeValue2405, nodeValue2408, nodeValue2409, nodeValue2744, nodeValue2841, nodeValue2842, nodeValue3055, nodeValue3246, nodeValue3247, nodeValue3306, nodeValue3358, nodeValue3535, nodeValue3548, nodeValue3549, nodeValue3559, nodeValue3565, nodeValue3573, nodeValue3583, nodeValue3862, nodeValue3877, nodeValue3889]
  ring

noncomputable def reducedSource393 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2774 x + ((2 : ℝ) * Sparse.eval nodeValue3854 x + ((2 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

def numericRow393 : Integer.Sparse Master := [(Sum.inr 2774, 2), (Sum.inr 3854, 2), (Sum.inr 3907, 2), (Sum.inr 4092, -1)]

theorem reindexCheck393 : Integer.Sparse.reindex keyMap MixedData.row393 = numericRow393 := by decide +kernel

theorem numericCheck393 (x : Master → ℝ) : Integer.Sparse.eval numericRow393 x =
    (1 : ℝ) * reducedSource393 x := by
  norm_num [numericRow393, reducedSource393, Integer.Sparse.eval, Sparse.eval, nodeValue2774, nodeValue3854, nodeValue3907, nodeValue4092]

noncomputable def reducedSource394 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow394 : Integer.Sparse Master := [(Sum.inr 1295, 1), (Sum.inr 2591, 2), (Sum.inr 2743, 1), (Sum.inr 2774, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem reindexCheck394 : Integer.Sparse.reindex keyMap MixedData.row394 = numericRow394 := by decide +kernel

theorem numericCheck394 (x : Master → ℝ) : Integer.Sparse.eval numericRow394 x =
    (1 : ℝ) * reducedSource394 x := by
  norm_num [numericRow394, reducedSource394, Integer.Sparse.eval, Sparse.eval, nodeValue1295, nodeValue2591, nodeValue2743, nodeValue2774, nodeValue2782, nodeValue4092]

noncomputable def reducedSource395 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((2 : ℝ) * Sparse.eval nodeValue2491 x + ((2 : ℝ) * Sparse.eval nodeValue2492 x + ((2 : ℝ) * Sparse.eval nodeValue2499 x + ((2 : ℝ) * Sparse.eval nodeValue2506 x + ((2 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + ((2 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0))))))))))))))))))))

def numericRow395 : Integer.Sparse Master := [(Sum.inl 0, -240), (Sum.inl 5, 80), (Sum.inl 2, -80), (Sum.inl 51, -960), (Sum.inl 3, 640), (Sum.inl 13, 320), (Sum.inl 12, 320), (Sum.inl 4, 320), (Sum.inl 1, 80), (Sum.inl 31, -960), (Sum.inr 1054, 17280), (Sum.inr 1055, 8640), (Sum.inr 1063, 8640), (Sum.inr 1076, 8640), (Sum.inr 2491, 17280), (Sum.inr 2492, 17280), (Sum.inr 2499, 17280), (Sum.inr 2506, 17280), (Sum.inr 2633, 17280), (Sum.inr 2635, 8640), (Sum.inr 2678, 17280), (Sum.inr 2680, 8640), (Sum.inr 2687, 8640), (Sum.inr 2773, 17280), (Sum.inr 2781, 8640), (Sum.inr 3881, 17280), (Sum.inr 3886, 8640)]

theorem reindexCheck395 : Integer.Sparse.reindex keyMap MixedData.row395 = numericRow395 := by decide +kernel

theorem numericCheck395 (x : Master → ℝ) : Integer.Sparse.eval numericRow395 x =
    (8640 : ℝ) * reducedSource395 x := by
  norm_num [numericRow395, reducedSource395, Integer.Sparse.eval, Sparse.eval, nodeValue1054, nodeValue1055, nodeValue1063, nodeValue1076, nodeValue2491, nodeValue2492, nodeValue2499, nodeValue2506, nodeValue2633, nodeValue2635, nodeValue2644, nodeValue2678, nodeValue2680, nodeValue2687, nodeValue2773, nodeValue2776, nodeValue2781, nodeValue3881, nodeValue3886, nodeValue3888, nodeValue4004]
  ring

noncomputable def reducedSource396 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1649 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3385 x + ((2 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((2 : ℝ) * Sparse.eval nodeValue3447 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + 0))))))))))))))))))))

def numericRow396 : Integer.Sparse Master := [(Sum.inl 0, -28), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inl 25, -240), (Sum.inl 4, 80), (Sum.inl 1, -15), (Sum.inr 1649, 4320), (Sum.inr 1651, 2160), (Sum.inr 1652, 2160), (Sum.inr 1740, 2160), (Sum.inr 2875, 4320), (Sum.inr 2888, 2160), (Sum.inr 3098, 2160), (Sum.inr 3385, 4320), (Sum.inr 3395, 4320), (Sum.inr 3396, 2160), (Sum.inr 3447, 4320), (Sum.inr 3480, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3579, 2160), (Sum.inr 3626, 2160), (Sum.inr 3631, 2160), (Sum.inr 3959, 4320), (Sum.inr 3963, 2160)]

theorem reindexCheck396 : Integer.Sparse.reindex keyMap MixedData.row396 = numericRow396 := by decide +kernel

theorem numericCheck396 (x : Master → ℝ) : Integer.Sparse.eval numericRow396 x =
    (2160 : ℝ) * reducedSource396 x := by
  norm_num [numericRow396, reducedSource396, Integer.Sparse.eval, Sparse.eval, nodeValue1649, nodeValue1651, nodeValue1652, nodeValue1740, nodeValue2875, nodeValue2888, nodeValue3098, nodeValue3385, nodeValue3395, nodeValue3396, nodeValue3447, nodeValue3480, nodeValue3573, nodeValue3578, nodeValue3579, nodeValue3626, nodeValue3631, nodeValue3959, nodeValue3963, nodeValue3987, nodeValue4030]
  ring

noncomputable def reducedSource397 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow397 : Integer.Sparse Master := [(Sum.inr 3055, 1), (Sum.inr 3884, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem reindexCheck397 : Integer.Sparse.reindex keyMap MixedData.row397 = numericRow397 := by decide +kernel

theorem numericCheck397 (x : Master → ℝ) : Integer.Sparse.eval numericRow397 x =
    (1 : ℝ) * reducedSource397 x := by
  norm_num [numericRow397, reducedSource397, Integer.Sparse.eval, Sparse.eval, nodeValue3055, nodeValue3884, nodeValue3886, nodeValue3913, nodeValue3963, nodeValue4092]

noncomputable def reducedSource398 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1437 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow398 : Integer.Sparse Master := [(Sum.inr 1368, 2), (Sum.inr 1373, 1), (Sum.inr 1375, 1), (Sum.inr 1437, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem reindexCheck398 : Integer.Sparse.reindex keyMap MixedData.row398 = numericRow398 := by decide +kernel

theorem numericCheck398 (x : Master → ℝ) : Integer.Sparse.eval numericRow398 x =
    (1 : ℝ) * reducedSource398 x := by
  norm_num [numericRow398, reducedSource398, Integer.Sparse.eval, Sparse.eval, nodeValue1368, nodeValue1373, nodeValue1375, nodeValue1437, nodeValue3055, nodeValue4092]

noncomputable def reducedSource399 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow399 : Integer.Sparse Master := [(Sum.inr 1368, 1), (Sum.inr 2882, 1), (Sum.inr 2975, 1), (Sum.inr 3044, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem reindexCheck399 : Integer.Sparse.reindex keyMap MixedData.row399 = numericRow399 := by decide +kernel

theorem numericCheck399 (x : Master → ℝ) : Integer.Sparse.eval numericRow399 x =
    (1 : ℝ) * reducedSource399 x := by
  norm_num [numericRow399, reducedSource399, Integer.Sparse.eval, Sparse.eval, nodeValue1368, nodeValue2882, nodeValue2975, nodeValue3044, nodeValue3051, nodeValue3055, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
