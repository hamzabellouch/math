import OAI.Analysis.MutuallyUnbiased.MixedData.Source5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
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

noncomputable def reducedSource640 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow640 : Integer.Sparse Master := [(Sum.inr 1291, 1), (Sum.inr 2587, 1), (Sum.inr 2739, 1), (Sum.inr 2763, 1), (Sum.inr 2773, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem reindexCheck640 : Integer.Sparse.reindex keyMap MixedData.row640 = numericRow640 := by decide +kernel

theorem numericCheck640 (x : Master → ℝ) : Integer.Sparse.eval numericRow640 x =
    (1 : ℝ) * reducedSource640 x := by
  norm_num [numericRow640, reducedSource640, Integer.Sparse.eval, Sparse.eval, nodeValue1291, nodeValue2587, nodeValue2739, nodeValue2763, nodeValue2773, nodeValue2782, nodeValue4092]

noncomputable def reducedSource641 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow641 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2632, 1), (Sum.inr 2634, 1), (Sum.inr 2639, 1), (Sum.inr 2763, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem reindexCheck641 : Integer.Sparse.reindex keyMap MixedData.row641 = numericRow641 := by decide +kernel

theorem numericCheck641 (x : Master → ℝ) : Integer.Sparse.eval numericRow641 x =
    (1 : ℝ) * reducedSource641 x := by
  norm_num [numericRow641, reducedSource641, Integer.Sparse.eval, Sparse.eval, nodeValue2630, nodeValue2632, nodeValue2634, nodeValue2639, nodeValue2763, nodeValue3884, nodeValue4092]

noncomputable def reducedSource642 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4449 x + ((1 : ℝ) * Sparse.eval nodeValue4450 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4487 x + ((1 : ℝ) * Sparse.eval nodeValue5069 x + ((1 : ℝ) * Sparse.eval nodeValue5071 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5092 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))))))))))

def numericRow642 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2954, -4320), (Sum.inr 3077, -4320), (Sum.inr 3606, -4320), (Sum.inr 3625, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3983, -17280), (Sum.inr 4010, -4320), (Sum.inr 4449, 17280), (Sum.inr 4450, 17280), (Sum.inr 4453, 17280), (Sum.inr 4459, 17280), (Sum.inr 4487, 17280), (Sum.inr 5069, 17280), (Sum.inr 5071, 17280), (Sum.inr 5074, 17280), (Sum.inr 5092, 17280), (Sum.inr 5140, 17280), (Sum.inr 5160, 17280), (Sum.inr 5161, 34560), (Sum.inr 5164, 17280), (Sum.inr 5226, 17280), (Sum.inr 5229, 17280), (Sum.inr 5236, 17280), (Sum.inr 5255, 17280), (Sum.inr 5260, 17280), (Sum.inr 5269, 17280), (Sum.inr 5281, 17280), (Sum.inr 5282, 17280), (Sum.inr 5289, 17280), (Sum.inr 5480, 17280)]

theorem reindexCheck642 : Integer.Sparse.reindex keyMap MixedData.row642 = numericRow642 := by decide +kernel

theorem numericCheck642 (x : Master → ℝ) : Integer.Sparse.eval numericRow642 x =
    (17280 : ℝ) * reducedSource642 x := by
  norm_num [numericRow642, reducedSource642, Integer.Sparse.eval, Sparse.eval, nodeValue4449, nodeValue4450, nodeValue4453, nodeValue4459, nodeValue4487, nodeValue5069, nodeValue5071, nodeValue5074, nodeValue5092, nodeValue5140, nodeValue5160, nodeValue5161, nodeValue5164, nodeValue5170, nodeValue5226, nodeValue5229, nodeValue5236, nodeValue5255, nodeValue5260, nodeValue5269, nodeValue5281, nodeValue5282, nodeValue5284, nodeValue5289, nodeValue5438, nodeValue5480, nodeValue5484, nodeValue5485]
  ring

noncomputable def reducedSource643 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1071 x + ((1 : ℝ) * Sparse.eval nodeValue2476 x + ((1 : ℝ) * Sparse.eval nodeValue2478 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2501 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

def numericRow643 : Integer.Sparse Master := [(Sum.inl 0, -98), (Sum.inl 5, -20), (Sum.inl 6, 5), (Sum.inl 2, 45), (Sum.inl 7, -80), (Sum.inl 35, -80), (Sum.inl 3, -400), (Sum.inl 13, -160), (Sum.inl 12, -160), (Sum.inl 26, -80), (Sum.inl 4, -160), (Sum.inl 1, -30), (Sum.inr 1032, 4320), (Sum.inr 1033, 4320), (Sum.inr 1036, 4320), (Sum.inr 1042, 4320), (Sum.inr 1071, 4320), (Sum.inr 2476, 4320), (Sum.inr 2478, 4320), (Sum.inr 2481, 4320), (Sum.inr 2501, 4320), (Sum.inr 2587, 4320), (Sum.inr 2588, 4320), (Sum.inr 2591, 4320), (Sum.inr 2669, 4320), (Sum.inr 2670, 4320), (Sum.inr 2673, 4320), (Sum.inr 2682, 4320), (Sum.inr 2718, 4320), (Sum.inr 2719, 4320), (Sum.inr 2724, 4320), (Sum.inr 2736, 4320), (Sum.inr 2750, 4320), (Sum.inr 2751, 4320), (Sum.inr 2763, 4320), (Sum.inr 3857, 4320), (Sum.inr 3978, 4320), (Sum.inr 3983, 4320)]

theorem reindexCheck643 : Integer.Sparse.reindex keyMap MixedData.row643 = numericRow643 := by decide +kernel

theorem numericCheck643 (x : Master → ℝ) : Integer.Sparse.eval numericRow643 x =
    (4320 : ℝ) * reducedSource643 x := by
  norm_num [numericRow643, reducedSource643, Integer.Sparse.eval, Sparse.eval, nodeValue1032, nodeValue1033, nodeValue1036, nodeValue1042, nodeValue1071, nodeValue2476, nodeValue2478, nodeValue2481, nodeValue2501, nodeValue2587, nodeValue2588, nodeValue2591, nodeValue2596, nodeValue2669, nodeValue2670, nodeValue2673, nodeValue2682, nodeValue2718, nodeValue2719, nodeValue2724, nodeValue2736, nodeValue2750, nodeValue2751, nodeValue2753, nodeValue2763, nodeValue3857, nodeValue3978, nodeValue3983, nodeValue3997, nodeValue3998]
  ring

noncomputable def reducedSource644 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1636 x + ((1 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1641 x + ((1 : ℝ) * Sparse.eval nodeValue1646 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3380 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3442 x + ((1 : ℝ) * Sparse.eval nodeValue3445 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

def numericRow644 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, 20), (Sum.inl 3, -480), (Sum.inl 12, -80), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, 120), (Sum.inr 1636, 4320), (Sum.inr 1637, 4320), (Sum.inr 1641, 4320), (Sum.inr 1646, 4320), (Sum.inr 1714, 4320), (Sum.inr 2550, 4320), (Sum.inr 2560, 4320), (Sum.inr 2588, 4320), (Sum.inr 2719, 4320), (Sum.inr 3376, 4320), (Sum.inr 3380, 4320), (Sum.inr 3392, 4320), (Sum.inr 3442, 4320), (Sum.inr 3445, 4320), (Sum.inr 3463, 4320), (Sum.inr 3503, 4320), (Sum.inr 3507, 4320), (Sum.inr 3540, 4320), (Sum.inr 3558, 4320), (Sum.inr 3565, 4320), (Sum.inr 3571, 4320), (Sum.inr 3572, 4320), (Sum.inr 3580, 4320), (Sum.inr 3606, 4320), (Sum.inr 3625, 4320), (Sum.inr 3978, 4320), (Sum.inr 3983, 4320)]

theorem reindexCheck644 : Integer.Sparse.reindex keyMap MixedData.row644 = numericRow644 := by decide +kernel

theorem numericCheck644 (x : Master → ℝ) : Integer.Sparse.eval numericRow644 x =
    (4320 : ℝ) * reducedSource644 x := by
  norm_num [numericRow644, reducedSource644, Integer.Sparse.eval, Sparse.eval, nodeValue1636, nodeValue1637, nodeValue1641, nodeValue1646, nodeValue1714, nodeValue2550, nodeValue2560, nodeValue2588, nodeValue2719, nodeValue3376, nodeValue3380, nodeValue3392, nodeValue3442, nodeValue3445, nodeValue3463, nodeValue3503, nodeValue3507, nodeValue3540, nodeValue3558, nodeValue3565, nodeValue3571, nodeValue3572, nodeValue3580, nodeValue3606, nodeValue3625, nodeValue3978, nodeValue3983, nodeValue3984, nodeValue3993, nodeValue3997]
  ring

noncomputable def reducedSource645 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4010 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow645 : Integer.Sparse Master := [(Sum.inr 3097, 1), (Sum.inr 3876, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem reindexCheck645 : Integer.Sparse.reindex keyMap MixedData.row645 = numericRow645 := by decide +kernel

theorem numericCheck645 (x : Master → ℝ) : Integer.Sparse.eval numericRow645 x =
    (1 : ℝ) * reducedSource645 x := by
  norm_num [numericRow645, reducedSource645, Integer.Sparse.eval, Sparse.eval, nodeValue3097, nodeValue3876, nodeValue3978, nodeValue3983, nodeValue4010, nodeValue4091]

noncomputable def reducedSource646 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1403 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow646 : Integer.Sparse Master := [(Sum.inr 1403, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3084, 1), (Sum.inr 3091, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem reindexCheck646 : Integer.Sparse.reindex keyMap MixedData.row646 = numericRow646 := by decide +kernel

theorem numericCheck646 (x : Master → ℝ) : Integer.Sparse.eval numericRow646 x =
    (1 : ℝ) * reducedSource646 x := by
  norm_num [numericRow646, reducedSource646, Integer.Sparse.eval, Sparse.eval, nodeValue1403, nodeValue2951, nodeValue3074, nodeValue3084, nodeValue3091, nodeValue3097, nodeValue4091]

noncomputable def reducedSource647 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow647 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 2964, 1), (Sum.inr 3097, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem reindexCheck647 : Integer.Sparse.reindex keyMap MixedData.row647 = numericRow647 := by decide +kernel

theorem numericCheck647 (x : Master → ℝ) : Integer.Sparse.eval numericRow647 x =
    (1 : ℝ) * reducedSource647 x := by
  norm_num [numericRow647, reducedSource647, Integer.Sparse.eval, Sparse.eval, nodeValue2951, nodeValue2954, nodeValue2955, nodeValue2964, nodeValue3097, nodeValue3983, nodeValue4091]

noncomputable def reducedSource648 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow648 : Integer.Sparse Master := [(Sum.inr 2942, 1), (Sum.inr 3091, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 3115, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem reindexCheck648 : Integer.Sparse.reindex keyMap MixedData.row648 = numericRow648 := by decide +kernel

theorem numericCheck648 (x : Master → ℝ) : Integer.Sparse.eval numericRow648 x =
    (1 : ℝ) * reducedSource648 x := by
  norm_num [numericRow648, reducedSource648, Integer.Sparse.eval, Sparse.eval, nodeValue2942, nodeValue3091, nodeValue3092, nodeValue3097, nodeValue3115, nodeValue3876, nodeValue4091]

noncomputable def reducedSource649 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2583 x + ((1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2717 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2749 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2760 x + ((1 : ℝ) * Sparse.eval nodeValue2762 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2772 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))))))))))

def numericRow649 : Integer.Sparse Master := [(Sum.inl 0, -290), (Sum.inl 2, -270), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -340), (Sum.inr 2240, 8640), (Sum.inr 2259, 8640), (Sum.inr 2260, 8640), (Sum.inr 2262, 8640), (Sum.inr 2274, 8640), (Sum.inr 2583, 8640), (Sum.inr 2584, 8640), (Sum.inr 2585, 8640), (Sum.inr 2600, 8640), (Sum.inr 2717, 8640), (Sum.inr 2718, 8640), (Sum.inr 2727, 8640), (Sum.inr 2749, 8640), (Sum.inr 2750, 8640), (Sum.inr 2760, 8640), (Sum.inr 2762, 8640), (Sum.inr 2763, 17280), (Sum.inr 2764, 8640), (Sum.inr 2772, 8640), (Sum.inr 2773, 8640), (Sum.inr 2781, 8640), (Sum.inr 2782, 8640), (Sum.inr 3084, 8640), (Sum.inr 3108, 8640)]

theorem reindexCheck649 : Integer.Sparse.reindex keyMap MixedData.row649 = numericRow649 := by decide +kernel

theorem numericCheck649 (x : Master → ℝ) : Integer.Sparse.eval numericRow649 x =
    (8640 : ℝ) * reducedSource649 x := by
  norm_num [numericRow649, reducedSource649, Integer.Sparse.eval, Sparse.eval, nodeValue2240, nodeValue2259, nodeValue2260, nodeValue2262, nodeValue2274, nodeValue2583, nodeValue2584, nodeValue2585, nodeValue2600, nodeValue2717, nodeValue2718, nodeValue2720, nodeValue2727, nodeValue2749, nodeValue2750, nodeValue2760, nodeValue2762, nodeValue2763, nodeValue2764, nodeValue2766, nodeValue2772, nodeValue2773, nodeValue2781, nodeValue2782, nodeValue2784, nodeValue3084, nodeValue3108, nodeValue3109, nodeValue3119]
  ring

noncomputable def reducedSource650 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow650 : Integer.Sparse Master := [(Sum.inr 2952, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3534, 1), (Sum.inr 3572, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem reindexCheck650 : Integer.Sparse.reindex keyMap MixedData.row650 = numericRow650 := by decide +kernel

theorem numericCheck650 (x : Master → ℝ) : Integer.Sparse.eval numericRow650 x =
    (1 : ℝ) * reducedSource650 x := by
  norm_num [numericRow650, reducedSource650, Integer.Sparse.eval, Sparse.eval, nodeValue2952, nodeValue3503, nodeValue3507, nodeValue3534, nodeValue3572, nodeValue3583, nodeValue4083]

noncomputable def reducedSource651 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow651 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2950, 1), (Sum.inr 3550, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

theorem reindexCheck651 : Integer.Sparse.reindex keyMap MixedData.row651 = numericRow651 := by decide +kernel

theorem numericCheck651 (x : Master → ℝ) : Integer.Sparse.eval numericRow651 x =
    (1 : ℝ) * reducedSource651 x := by
  norm_num [numericRow651, reducedSource651, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2950, nodeValue3550, nodeValue3571, nodeValue3572, nodeValue4083]

noncomputable def reducedSource652 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow652 : Integer.Sparse Master := [(Sum.inr 2094, 1), (Sum.inr 2956, 1), (Sum.inr 3500, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck652 : Integer.Sparse.reindex keyMap MixedData.row652 = numericRow652 := by decide +kernel

theorem numericCheck652 (x : Master → ℝ) : Integer.Sparse.eval numericRow652 x =
    (1 : ℝ) * reducedSource652 x := by
  norm_num [numericRow652, reducedSource652, Integer.Sparse.eval, Sparse.eval, nodeValue2094, nodeValue2956, nodeValue3500, nodeValue3552, nodeValue3572, nodeValue3573, nodeValue4083]

noncomputable def reducedSource653 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2950 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2956 x + ((1 : ℝ) * Sparse.eval nodeValue2962 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow653 : Integer.Sparse Master := [(Sum.inr 2950, 1), (Sum.inr 2952, 1), (Sum.inr 2956, 1), (Sum.inr 2962, 1), (Sum.inr 3096, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem reindexCheck653 : Integer.Sparse.reindex keyMap MixedData.row653 = numericRow653 := by decide +kernel

theorem numericCheck653 (x : Master → ℝ) : Integer.Sparse.eval numericRow653 x =
    (1 : ℝ) * reducedSource653 x := by
  norm_num [numericRow653, reducedSource653, Integer.Sparse.eval, Sparse.eval, nodeValue2950, nodeValue2952, nodeValue2956, nodeValue2962, nodeValue3096, nodeValue3572, nodeValue4083]

noncomputable def reducedSource654 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow654 : Integer.Sparse Master := [(Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 3503, 1), (Sum.inr 3572, 1), (Sum.inr 3581, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem reindexCheck654 : Integer.Sparse.reindex keyMap MixedData.row654 = numericRow654 := by decide +kernel

theorem numericCheck654 (x : Master → ℝ) : Integer.Sparse.eval numericRow654 x =
    (1 : ℝ) * reducedSource654 x := by
  norm_num [numericRow654, reducedSource654, Integer.Sparse.eval, Sparse.eval, nodeValue2107, nodeValue3096, nodeValue3503, nodeValue3572, nodeValue3581, nodeValue3583, nodeValue4083]

noncomputable def reducedSource655 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2995 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3550 x + ((1 : ℝ) * Sparse.eval nodeValue3552 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow655 : Integer.Sparse Master := [(Sum.inr 2995, 1), (Sum.inr 3507, 1), (Sum.inr 3550, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

theorem reindexCheck655 : Integer.Sparse.reindex keyMap MixedData.row655 = numericRow655 := by decide +kernel

theorem numericCheck655 (x : Master → ℝ) : Integer.Sparse.eval numericRow655 x =
    (1 : ℝ) * reducedSource655 x := by
  norm_num [numericRow655, reducedSource655, Integer.Sparse.eval, Sparse.eval, nodeValue2995, nodeValue3507, nodeValue3550, nodeValue3552, nodeValue3572, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
