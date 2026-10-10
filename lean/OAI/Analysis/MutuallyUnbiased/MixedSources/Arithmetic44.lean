import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
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

noncomputable def reducedSource704 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow704 : Integer.Sparse Master := [(Sum.inr 2105, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 2), (Sum.inr 4083, -1)]

theorem reindexCheck704 : Integer.Sparse.reindex keyMap MixedData.row704 = numericRow704 := by decide +kernel

theorem numericCheck704 (x : Master → ℝ) : Integer.Sparse.eval numericRow704 x =
    (1 : ℝ) * reducedSource704 x := by
  norm_num [numericRow704, reducedSource704, Integer.Sparse.eval, Sparse.eval, nodeValue2105, nodeValue3073, nodeValue3571, nodeValue3581, nodeValue4083]

noncomputable def reducedSource705 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3489 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((2 : ℝ) * Sparse.eval nodeValue3551 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow705 : Integer.Sparse Master := [(Sum.inr 3550, 1), (Sum.inr 3551, 2), (Sum.inr 3571, 2), (Sum.inr 4083, -1)]

theorem reindexCheck705 : Integer.Sparse.reindex keyMap MixedData.row705 = numericRow705 := by decide +kernel

theorem numericCheck705 (x : Master → ℝ) : Integer.Sparse.eval numericRow705 x =
    (1 : ℝ) * reducedSource705 x := by
  norm_num [numericRow705, reducedSource705, Integer.Sparse.eval, Sparse.eval, nodeValue3489, nodeValue3550, nodeValue3551, nodeValue3571, nodeValue4083]

noncomputable def reducedSource706 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4581 x + ((2 : ℝ) * Sparse.eval nodeValue4601 x + ((6 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5202 x + ((6 : ℝ) * Sparse.eval nodeValue5284 x + ((6 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5447 x + ((3 : ℝ) * Sparse.eval nodeValue5452 x + 0)))))))

def numericRow706 : Integer.Sparse Master := [(Sum.inl 0, 117), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -170), (Sum.inr 1200, -2160), (Sum.inr 1235, -1440), (Sum.inr 2853, -4320), (Sum.inr 2880, -1440), (Sum.inr 3077, -4320), (Sum.inr 3281, -2160), (Sum.inr 3292, -1440), (Sum.inr 3617, -1440), (Sum.inr 3620, -4320), (Sum.inr 3622, -4320), (Sum.inr 3625, -4320), (Sum.inr 3909, -1440), (Sum.inr 4025, -1440)]

theorem reindexCheck706 : Integer.Sparse.reindex keyMap MixedData.row706 = numericRow706 := by decide +kernel

theorem numericCheck706 (x : Master → ℝ) : Integer.Sparse.eval numericRow706 x =
    (2880 : ℝ) * reducedSource706 x := by
  norm_num [numericRow706, reducedSource706, Integer.Sparse.eval, Sparse.eval, nodeValue4581, nodeValue4601, nodeValue5192, nodeValue5202, nodeValue5284, nodeValue5292, nodeValue5447, nodeValue5452]
  ring

noncomputable def reducedSource707 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1235 x + ((6 : ℝ) * Sparse.eval nodeValue2853 x + ((2 : ℝ) * Sparse.eval nodeValue2880 x + ((6 : ℝ) * Sparse.eval nodeValue3077 x + ((6 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue4025 x + ((3 : ℝ) * Sparse.eval nodeValue4039 x + 0)))))))

def numericRow707 : Integer.Sparse Master := [(Sum.inl 0, -82), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 95), (Sum.inr 1200, 2160), (Sum.inr 1235, 1440), (Sum.inr 2853, 4320), (Sum.inr 2880, 1440), (Sum.inr 3077, 4320), (Sum.inr 4025, 1440)]

theorem reindexCheck707 : Integer.Sparse.reindex keyMap MixedData.row707 = numericRow707 := by decide +kernel

theorem numericCheck707 (x : Master → ℝ) : Integer.Sparse.eval numericRow707 x =
    (720 : ℝ) * reducedSource707 x := by
  norm_num [numericRow707, reducedSource707, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue1235, nodeValue2853, nodeValue2880, nodeValue3077, nodeValue3100, nodeValue4025, nodeValue4039]
  ring

noncomputable def reducedSource708 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4885 x + ((3 : ℝ) * Sparse.eval nodeValue4887 x + ((3 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5273 x + ((6 : ℝ) * Sparse.eval nodeValue5281 x + ((6 : ℝ) * Sparse.eval nodeValue5286 x + ((6 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5301 x + 0)))))))

def numericRow708 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2243, -4320), (Sum.inr 2703, -2160), (Sum.inr 3053, -1440), (Sum.inr 3496, -2160), (Sum.inr 3619, -1440), (Sum.inr 3622, -4320), (Sum.inr 4885, 5760), (Sum.inr 5281, 17280), (Sum.inr 5286, 17280)]

theorem reindexCheck708 : Integer.Sparse.reindex keyMap MixedData.row708 = numericRow708 := by decide +kernel

theorem numericCheck708 (x : Master → ℝ) : Integer.Sparse.eval numericRow708 x =
    (2880 : ℝ) * reducedSource708 x := by
  norm_num [numericRow708, reducedSource708, Integer.Sparse.eval, Sparse.eval, nodeValue4885, nodeValue4887, nodeValue5247, nodeValue5273, nodeValue5281, nodeValue5286, nodeValue5292, nodeValue5301]
  ring

noncomputable def reducedSource709 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2741 x + ((6 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3053 x + ((6 : ℝ) * Sparse.eval nodeValue3074 x + ((6 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3226 x + 0)))))))

def numericRow709 : Integer.Sparse Master := [(Sum.inl 0, -60), (Sum.inl 2, -95), (Sum.inl 3, 80), (Sum.inl 13, 160), (Sum.inl 12, 40), (Sum.inl 1, -95), (Sum.inr 2703, 2160), (Sum.inr 3023, 4320), (Sum.inr 3053, 1440), (Sum.inr 3074, 4320), (Sum.inr 3221, 1440)]

theorem reindexCheck709 : Integer.Sparse.reindex keyMap MixedData.row709 = numericRow709 := by decide +kernel

theorem numericCheck709 (x : Master → ℝ) : Integer.Sparse.eval numericRow709 x =
    (720 : ℝ) * reducedSource709 x := by
  norm_num [numericRow709, reducedSource709, Integer.Sparse.eval, Sparse.eval, nodeValue2703, nodeValue2741, nodeValue3023, nodeValue3053, nodeValue3074, nodeValue3100, nodeValue3221, nodeValue3226]
  ring

noncomputable def reducedSource710 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4600 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0))))))))))))))))))))

def numericRow710 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 1293, -1080), (Sum.inr 2589, -1080), (Sum.inr 2721, -1080), (Sum.inr 2723, -2160), (Sum.inr 2764, -2160), (Sum.inr 3304, -1080), (Sum.inr 3532, -1080), (Sum.inr 3544, -2160), (Sum.inr 3563, -1080), (Sum.inr 3581, -2160), (Sum.inr 3849, -1080), (Sum.inr 3875, -1080), (Sum.inr 3885, -2160), (Sum.inr 3910, -2160), (Sum.inr 4599, 4320), (Sum.inr 4600, 4320), (Sum.inr 4603, 8640), (Sum.inr 5145, 8640), (Sum.inr 5150, 4320), (Sum.inr 5197, 4320), (Sum.inr 5199, 8640), (Sum.inr 5205, 4320), (Sum.inr 5270, 8640), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640)]

theorem reindexCheck710 : Integer.Sparse.reindex keyMap MixedData.row710 = numericRow710 := by decide +kernel

theorem numericCheck710 (x : Master → ℝ) : Integer.Sparse.eval numericRow710 x =
    (4320 : ℝ) * reducedSource710 x := by
  norm_num [numericRow710, reducedSource710, Integer.Sparse.eval, Sparse.eval, nodeValue4599, nodeValue4600, nodeValue4603, nodeValue4618, nodeValue5145, nodeValue5150, nodeValue5162, nodeValue5197, nodeValue5199, nodeValue5205, nodeValue5257, nodeValue5259, nodeValue5270, nodeValue5273, nodeValue5281, nodeValue5282, nodeValue5290, nodeValue5431, nodeValue5440, nodeValue5448, nodeValue5450]
  ring

noncomputable def reducedSource711 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((2 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2957 x + ((2 : ℝ) * Sparse.eval nodeValue3074 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3099 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + ((1 : ℝ) * Sparse.eval nodeValue4026 x + ((1 : ℝ) * Sparse.eval nodeValue4028 x + ((2 : ℝ) * Sparse.eval nodeValue4029 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))

def numericRow711 : Integer.Sparse Master := [(Sum.inl 0, -75), (Sum.inl 2, 85), (Sum.inl 3, 240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 1233, 1440), (Sum.inr 1234, 1440), (Sum.inr 1237, 2880), (Sum.inr 2878, 1440), (Sum.inr 2879, 1440), (Sum.inr 2882, 2880), (Sum.inr 2923, 1440), (Sum.inr 2925, 2880), (Sum.inr 3074, 2880), (Sum.inr 3075, 2880), (Sum.inr 3078, 2880)]

theorem reindexCheck711 : Integer.Sparse.reindex keyMap MixedData.row711 = numericRow711 := by decide +kernel

theorem numericCheck711 (x : Master → ℝ) : Integer.Sparse.eval numericRow711 x =
    (1440 : ℝ) * reducedSource711 x := by
  norm_num [numericRow711, reducedSource711, Integer.Sparse.eval, Sparse.eval, nodeValue1233, nodeValue1234, nodeValue1237, nodeValue1298, nodeValue2878, nodeValue2879, nodeValue2882, nodeValue2923, nodeValue2925, nodeValue2957, nodeValue3074, nodeValue3075, nodeValue3078, nodeValue3087, nodeValue3088, nodeValue3099, nodeValue3111, nodeValue4026, nodeValue4028, nodeValue4029, nodeValue4036]
  ring

noncomputable def reducedSource712 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((2 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((2 : ℝ) * Sparse.eval nodeValue3580 x + ((2 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((2 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

def numericRow712 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 50), (Sum.inr 2700, 1080), (Sum.inr 2702, 1080), (Sum.inr 2706, 1080), (Sum.inr 2738, 2160), (Sum.inr 3289, 1080), (Sum.inr 3294, 2160), (Sum.inr 3304, 1080), (Sum.inr 3532, 1080), (Sum.inr 3544, 2160), (Sum.inr 3562, 2160), (Sum.inr 3563, 1080), (Sum.inr 3569, 1080), (Sum.inr 3571, 2160), (Sum.inr 3578, 2160), (Sum.inr 3580, 2160), (Sum.inr 3581, 2160), (Sum.inr 3875, 1080), (Sum.inr 3885, 1080)]

theorem reindexCheck712 : Integer.Sparse.reindex keyMap MixedData.row712 = numericRow712 := by decide +kernel

theorem numericCheck712 (x : Master → ℝ) : Integer.Sparse.eval numericRow712 x =
    (1080 : ℝ) * reducedSource712 x := by
  norm_num [numericRow712, reducedSource712, Integer.Sparse.eval, Sparse.eval, nodeValue2700, nodeValue2702, nodeValue2706, nodeValue2738, nodeValue3289, nodeValue3294, nodeValue3304, nodeValue3532, nodeValue3544, nodeValue3546, nodeValue3562, nodeValue3563, nodeValue3569, nodeValue3571, nodeValue3578, nodeValue3580, nodeValue3581, nodeValue3859, nodeValue3875, nodeValue3885, nodeValue3887]
  ring

noncomputable def reducedSource713 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3904 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow713 : Integer.Sparse Master := [(Sum.inr 2764, 1), (Sum.inr 3849, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 2), (Sum.inr 4091, -1)]

theorem reindexCheck713 : Integer.Sparse.reindex keyMap MixedData.row713 = numericRow713 := by decide +kernel

theorem numericCheck713 (x : Master → ℝ) : Integer.Sparse.eval numericRow713 x =
    (1 : ℝ) * reducedSource713 x := by
  norm_num [numericRow713, reducedSource713, Integer.Sparse.eval, Sparse.eval, nodeValue2764, nodeValue3849, nodeValue3885, nodeValue3904, nodeValue3910, nodeValue4091]

noncomputable def reducedSource714 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1293 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow714 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 1262, 2), (Sum.inr 1270, 1), (Sum.inr 1293, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem reindexCheck714 : Integer.Sparse.reindex keyMap MixedData.row714 = numericRow714 := by decide +kernel

theorem numericCheck714 (x : Master → ℝ) : Integer.Sparse.eval numericRow714 x =
    (1 : ℝ) * reducedSource714 x := by
  norm_num [numericRow714, reducedSource714, Integer.Sparse.eval, Sparse.eval, nodeValue1260, nodeValue1262, nodeValue1270, nodeValue1293, nodeValue2764, nodeValue4091]

noncomputable def reducedSource715 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1293 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue2764 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow715 : Integer.Sparse Master := [(Sum.inr 1293, 1), (Sum.inr 2589, 1), (Sum.inr 2764, 3), (Sum.inr 4091, -1)]

theorem reindexCheck715 : Integer.Sparse.reindex keyMap MixedData.row715 = numericRow715 := by decide +kernel

theorem numericCheck715 (x : Master → ℝ) : Integer.Sparse.eval numericRow715 x =
    (1 : ℝ) * reducedSource715 x := by
  norm_num [numericRow715, reducedSource715, Integer.Sparse.eval, Sparse.eval, nodeValue1293, nodeValue2589, nodeValue2741, nodeValue2764, nodeValue4091]

noncomputable def reducedSource716 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2631 x + ((2 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow716 : Integer.Sparse Master := [(Sum.inr 2631, 1), (Sum.inr 2633, 2), (Sum.inr 2641, 1), (Sum.inr 2764, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem reindexCheck716 : Integer.Sparse.reindex keyMap MixedData.row716 = numericRow716 := by decide +kernel

theorem numericCheck716 (x : Master → ℝ) : Integer.Sparse.eval numericRow716 x =
    (1 : ℝ) * reducedSource716 x := by
  norm_num [numericRow716, reducedSource716, Integer.Sparse.eval, Sparse.eval, nodeValue2631, nodeValue2633, nodeValue2641, nodeValue2764, nodeValue3885, nodeValue4091]

noncomputable def reducedSource717 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5093 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

def numericRow717 : Integer.Sparse Master := [(Sum.inl 0, 380), (Sum.inl 6, -5), (Sum.inl 2, -65), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, -320), (Sum.inl 1, -500), (Sum.inr 1034, -4320), (Sum.inr 1035, -8640), (Sum.inr 1044, -4320), (Sum.inr 1073, -4320), (Sum.inr 1644, -4320), (Sum.inr 1645, -8640), (Sum.inr 1648, -4320), (Sum.inr 1737, -4320), (Sum.inr 2477, -8640), (Sum.inr 2483, -4320), (Sum.inr 2503, -4320), (Sum.inr 2589, -4320), (Sum.inr 2590, -8640), (Sum.inr 2671, -4320), (Sum.inr 2672, -8640), (Sum.inr 2684, -4320), (Sum.inr 2764, -8640), (Sum.inr 2765, -8640), (Sum.inr 2782, -8640), (Sum.inr 3390, -4320), (Sum.inr 3391, -8640), (Sum.inr 3394, -4320), (Sum.inr 3444, -8640), (Sum.inr 3446, -4320), (Sum.inr 3477, -4320), (Sum.inr 3563, -4320), (Sum.inr 3564, -8640), (Sum.inr 3581, -8640), (Sum.inr 3582, -8640), (Sum.inr 3583, -8640), (Sum.inr 3613, -4320), (Sum.inr 3632, -8640), (Sum.inr 3910, -4320), (Sum.inr 4010, -4320)]

theorem reindexCheck717 : Integer.Sparse.reindex keyMap MixedData.row717 = numericRow717 := by decide +kernel

theorem numericCheck717 (x : Master → ℝ) : Integer.Sparse.eval numericRow717 x =
    (17280 : ℝ) * reducedSource717 x := by
  norm_num [numericRow717, reducedSource717, Integer.Sparse.eval, Sparse.eval, nodeValue4451, nodeValue4452, nodeValue4461, nodeValue4489, nodeValue5070, nodeValue5076, nodeValue5093, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5227, nodeValue5228, nodeValue5237, nodeValue5290, nodeValue5291, nodeValue5294, nodeValue5304, nodeValue5450, nodeValue5481, nodeValue5485, nodeValue5492]
  ring

noncomputable def reducedSource718 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1034 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((2 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2503 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4017 x + 0))))))))))))))))))))

def numericRow718 : Integer.Sparse Master := [(Sum.inl 0, -254), (Sum.inl 6, 5), (Sum.inl 2, 55), (Sum.inl 7, -80), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 340), (Sum.inr 1034, 4320), (Sum.inr 1035, 8640), (Sum.inr 1044, 4320), (Sum.inr 1073, 4320), (Sum.inr 2477, 8640), (Sum.inr 2483, 4320), (Sum.inr 2503, 4320), (Sum.inr 2589, 4320), (Sum.inr 2590, 8640), (Sum.inr 2671, 4320), (Sum.inr 2672, 8640), (Sum.inr 2684, 4320), (Sum.inr 2764, 8640), (Sum.inr 2765, 8640), (Sum.inr 2782, 8640), (Sum.inr 3910, 4320)]

theorem reindexCheck718 : Integer.Sparse.reindex keyMap MixedData.row718 = numericRow718 := by decide +kernel

theorem numericCheck718 (x : Master → ℝ) : Integer.Sparse.eval numericRow718 x =
    (4320 : ℝ) * reducedSource718 x := by
  norm_num [numericRow718, reducedSource718, Integer.Sparse.eval, Sparse.eval, nodeValue1034, nodeValue1035, nodeValue1044, nodeValue1073, nodeValue2477, nodeValue2483, nodeValue2503, nodeValue2589, nodeValue2590, nodeValue2599, nodeValue2671, nodeValue2672, nodeValue2684, nodeValue2764, nodeValue2765, nodeValue2768, nodeValue2782, nodeValue3910, nodeValue3979, nodeValue3998, nodeValue4017]
  ring

noncomputable def reducedSource719 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5288 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((2 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0))))))))))))))))))))

def numericRow719 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 10), (Sum.inl 1, 15), (Sum.inr 2105, -360), (Sum.inr 2107, -720), (Sum.inr 2110, -360), (Sum.inr 2241, -360), (Sum.inr 2260, -720), (Sum.inr 2275, -360), (Sum.inr 2721, -360), (Sum.inr 2739, -720), (Sum.inr 2764, -360), (Sum.inr 2782, -720), (Sum.inr 3532, -360), (Sum.inr 3534, -720), (Sum.inr 3581, -360), (Sum.inr 3583, -720), (Sum.inr 3622, -720), (Sum.inr 3623, -360), (Sum.inr 5255, 2880), (Sum.inr 5263, 1440), (Sum.inr 5270, 1440), (Sum.inr 5278, 1440), (Sum.inr 5279, 1440), (Sum.inr 5281, 2880), (Sum.inr 5288, 2880), (Sum.inr 5289, 2880), (Sum.inr 5299, 2880)]

theorem reindexCheck719 : Integer.Sparse.reindex keyMap MixedData.row719 = numericRow719 := by decide +kernel

theorem numericCheck719 (x : Master → ℝ) : Integer.Sparse.eval numericRow719 x =
    (1440 : ℝ) * reducedSource719 x := by
  norm_num [numericRow719, reducedSource719, Integer.Sparse.eval, Sparse.eval, nodeValue4864, nodeValue4866, nodeValue4869, nodeValue4893, nodeValue5255, nodeValue5256, nodeValue5257, nodeValue5263, nodeValue5270, nodeValue5271, nodeValue5278, nodeValue5279, nodeValue5281, nodeValue5288, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5299, nodeValue5304, nodeValue5306, nodeValue5307]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
