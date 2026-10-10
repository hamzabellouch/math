import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource592 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3286 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3527 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + 0))))))))))))))))))))

def numericRow592 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 2, -15), (Sum.inl 3, 480), (Sum.inl 13, 240), (Sum.inl 12, 320), (Sum.inl 1, -75), (Sum.inr 3285, 8640), (Sum.inr 3286, 4320), (Sum.inr 3288, 4320), (Sum.inr 3289, 4320), (Sum.inr 3459, 4320), (Sum.inr 3460, 4320), (Sum.inr 3463, 8640), (Sum.inr 3524, 4320), (Sum.inr 3526, 4320), (Sum.inr 3527, 8640), (Sum.inr 3528, 8640), (Sum.inr 3533, 8640), (Sum.inr 3534, 8640), (Sum.inr 3540, 8640), (Sum.inr 3566, 4320), (Sum.inr 3567, 4320), (Sum.inr 3572, 8640), (Sum.inr 3800, 4320), (Sum.inr 3846, 4320)]

theorem reindexCheck592 : Integer.Sparse.reindex keyMap MixedData.row592 = numericRow592 := by decide +kernel

theorem numericCheck592 (x : Master → ℝ) : Integer.Sparse.eval numericRow592 x =
    (4320 : ℝ) * reducedSource592 x := by
  norm_num [numericRow592, reducedSource592, Integer.Sparse.eval, Sparse.eval, nodeValue3285, nodeValue3286, nodeValue3288, nodeValue3289, nodeValue3459, nodeValue3460, nodeValue3463, nodeValue3524, nodeValue3526, nodeValue3527, nodeValue3528, nodeValue3533, nodeValue3534, nodeValue3540, nodeValue3566, nodeValue3567, nodeValue3572, nodeValue3800, nodeValue3846, nodeValue3847, nodeValue3852]; ring

noncomputable def reducedSource593 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3903 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow593 : Integer.Sparse Master := [(Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3874, 1), (Sum.inr 3903, 2), (Sum.inr 4092, -1)]

theorem reindexCheck593 : Integer.Sparse.reindex keyMap MixedData.row593 = numericRow593 := by decide +kernel

theorem numericCheck593 (x : Master → ℝ) : Integer.Sparse.eval numericRow593 x =
    (1 : ℝ) * reducedSource593 x := by
  norm_num [numericRow593, reducedSource593, Integer.Sparse.eval, Sparse.eval, nodeValue2720, nodeValue3805, nodeValue3812, nodeValue3874, nodeValue3903, nodeValue4092]

noncomputable def reducedSource594 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1212 x + ((2 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow594 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1214, 2), (Sum.inr 1233, 1), (Sum.inr 1259, 1), (Sum.inr 4092, -1)]

theorem reindexCheck594 : Integer.Sparse.reindex keyMap MixedData.row594 = numericRow594 := by decide +kernel

theorem numericCheck594 (x : Master → ℝ) : Integer.Sparse.eval numericRow594 x =
    (1 : ℝ) * reducedSource594 x := by
  norm_num [numericRow594, reducedSource594, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue1214, nodeValue1233, nodeValue1259, nodeValue2720, nodeValue4092]

noncomputable def reducedSource595 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1259 x + ((1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2757 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow595 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 2630, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 2), (Sum.inr 4092, -1)]

theorem reindexCheck595 : Integer.Sparse.reindex keyMap MixedData.row595 = numericRow595 := by decide +kernel

theorem numericCheck595 (x : Master → ℝ) : Integer.Sparse.eval numericRow595 x =
    (1 : ℝ) * reducedSource595 x := by
  norm_num [numericRow595, reducedSource595, Integer.Sparse.eval, Sparse.eval, nodeValue1259, nodeValue2630, nodeValue2720, nodeValue2757, nodeValue2763, nodeValue4092]

noncomputable def reducedSource596 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow596 : Integer.Sparse Master := [(Sum.inr 2479, 1), (Sum.inr 2481, 2), (Sum.inr 2508, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

theorem reindexCheck596 : Integer.Sparse.reindex keyMap MixedData.row596 = numericRow596 := by decide +kernel

theorem numericCheck596 (x : Master → ℝ) : Integer.Sparse.eval numericRow596 x =
    (1 : ℝ) * reducedSource596 x := by
  norm_num [numericRow596, reducedSource596, Integer.Sparse.eval, Sparse.eval, nodeValue2479, nodeValue2481, nodeValue2508, nodeValue2720, nodeValue3805, nodeValue4092]

noncomputable def reducedSource597 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1233 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow597 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 2739, 2), (Sum.inr 4092, -1)]

theorem reindexCheck597 : Integer.Sparse.reindex keyMap MixedData.row597 = numericRow597 := by decide +kernel

theorem numericCheck597 (x : Master → ℝ) : Integer.Sparse.eval numericRow597 x =
    (1 : ℝ) * reducedSource597 x := by
  norm_num [numericRow597, reducedSource597, Integer.Sparse.eval, Sparse.eval, nodeValue1233, nodeValue2508, nodeValue2720, nodeValue2730, nodeValue2739, nodeValue4092]

noncomputable def reducedSource598 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2614 x + ((2 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow598 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 2616, 2), (Sum.inr 2630, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem reindexCheck598 : Integer.Sparse.reindex keyMap MixedData.row598 = numericRow598 := by decide +kernel

theorem numericCheck598 (x : Master → ℝ) : Integer.Sparse.eval numericRow598 x =
    (1 : ℝ) * reducedSource598 x := by
  norm_num [numericRow598, reducedSource598, Integer.Sparse.eval, Sparse.eval, nodeValue2614, nodeValue2616, nodeValue2630, nodeValue2720, nodeValue3874, nodeValue4092]

noncomputable def reducedSource599 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5066 x + ((2 : ℝ) * Sparse.eval nodeValue5077 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5230 x + ((4 : ℝ) * Sparse.eval nodeValue5255 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5262 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))

def numericRow599 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 2020, -1728), (Sum.inr 2202, -1728), (Sum.inr 2244, -864), (Sum.inr 2262, -864), (Sum.inr 2721, -2592), (Sum.inr 2739, -1728), (Sum.inr 2764, -864), (Sum.inr 3532, -2592), (Sum.inr 3534, -1728), (Sum.inr 3581, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 4792, 3456), (Sum.inr 4795, 3456), (Sum.inr 5066, 3456), (Sum.inr 5077, 6912), (Sum.inr 5226, 6912), (Sum.inr 5230, 3456), (Sum.inr 5255, 13824), (Sum.inr 5262, 6912), (Sum.inr 5263, 3456), (Sum.inr 5265, 3456), (Sum.inr 5270, 3456), (Sum.inr 5289, 6912)]

theorem reindexCheck599 : Integer.Sparse.reindex keyMap MixedData.row599 = numericRow599 := by decide +kernel

theorem numericCheck599 (x : Master → ℝ) : Integer.Sparse.eval numericRow599 x =
    (3456 : ℝ) * reducedSource599 x := by
  norm_num [numericRow599, reducedSource599, Integer.Sparse.eval, Sparse.eval, nodeValue4792, nodeValue4795, nodeValue4802, nodeValue4888, nodeValue5066, nodeValue5077, nodeValue5226, nodeValue5230, nodeValue5255, nodeValue5257, nodeValue5262, nodeValue5263, nodeValue5265, nodeValue5270, nodeValue5271, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5306]; ring

noncomputable def reducedSource600 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2675 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2721 x + ((2 : ℝ) * Sparse.eval nodeValue2727 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3099 x + 0))))))))))))))))))))

def numericRow600 : Integer.Sparse Master := [(Sum.inl 0, -41), (Sum.inl 2, -25), (Sum.inl 3, 80), (Sum.inl 1, -140), (Sum.inr 2201, 1440), (Sum.inr 2202, 2880), (Sum.inr 2213, 1440), (Sum.inr 2262, 1440), (Sum.inr 2668, 1440), (Sum.inr 2669, 2880), (Sum.inr 2675, 1440), (Sum.inr 2717, 2880), (Sum.inr 2718, 2880), (Sum.inr 2721, 2880), (Sum.inr 2727, 2880), (Sum.inr 2730, 1440), (Sum.inr 2738, 1440), (Sum.inr 2739, 2880), (Sum.inr 2763, 2880), (Sum.inr 3036, 1440), (Sum.inr 3084, 2880)]

theorem reindexCheck600 : Integer.Sparse.reindex keyMap MixedData.row600 = numericRow600 := by decide +kernel

theorem numericCheck600 (x : Master → ℝ) : Integer.Sparse.eval numericRow600 x =
    (1440 : ℝ) * reducedSource600 x := by
  norm_num [numericRow600, reducedSource600, Integer.Sparse.eval, Sparse.eval, nodeValue2201, nodeValue2202, nodeValue2213, nodeValue2262, nodeValue2668, nodeValue2669, nodeValue2675, nodeValue2717, nodeValue2718, nodeValue2721, nodeValue2727, nodeValue2730, nodeValue2738, nodeValue2739, nodeValue2763, nodeValue2766, nodeValue2784, nodeValue3036, nodeValue3084, nodeValue3087, nodeValue3099]; ring

noncomputable def reducedSource601 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2472 x + ((2 : ℝ) * Sparse.eval nodeValue2484 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue3034 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3041 x + ((2 : ℝ) * Sparse.eval nodeValue3084 x + ((2 : ℝ) * Sparse.eval nodeValue3087 x + ((2 : ℝ) * Sparse.eval nodeValue3091 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

def numericRow601 : Integer.Sparse Master := [(Sum.inl 0, -588), (Sum.inl 5, -400), (Sum.inl 6, 60), (Sum.inl 2, -330), (Sum.inl 35, 320), (Sum.inl 8, 320), (Sum.inl 3, 1920), (Sum.inl 13, 480), (Sum.inl 52, 320), (Sum.inl 56, -960), (Sum.inl 26, 640), (Sum.inl 4, 640), (Sum.inl 1, -1570), (Sum.inr 2471, 8640), (Sum.inr 2472, 8640), (Sum.inr 2484, 17280), (Sum.inr 2718, 17280), (Sum.inr 2721, 8640), (Sum.inr 2728, 8640), (Sum.inr 2754, 8640), (Sum.inr 2764, 8640), (Sum.inr 3034, 17280), (Sum.inr 3037, 8640), (Sum.inr 3041, 8640), (Sum.inr 3084, 17280), (Sum.inr 3091, 17280), (Sum.inr 3097, 17280), (Sum.inr 3199, 8640)]

theorem reindexCheck601 : Integer.Sparse.reindex keyMap MixedData.row601 = numericRow601 := by decide +kernel

theorem numericCheck601 (x : Master → ℝ) : Integer.Sparse.eval numericRow601 x =
    (8640 : ℝ) * reducedSource601 x := by
  norm_num [numericRow601, reducedSource601, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue2472, nodeValue2484, nodeValue2718, nodeValue2721, nodeValue2728, nodeValue2754, nodeValue2764, nodeValue3034, nodeValue3037, nodeValue3041, nodeValue3084, nodeValue3087, nodeValue3091, nodeValue3097, nodeValue3100, nodeValue3109, nodeValue3120, nodeValue3199, nodeValue3204, nodeValue3227]; ring

noncomputable def reducedSource602 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow602 : Integer.Sparse Master := [(Sum.inr 3503, 2), (Sum.inr 3505, 1), (Sum.inr 3532, 1), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

theorem reindexCheck602 : Integer.Sparse.reindex keyMap MixedData.row602 = numericRow602 := by decide +kernel

theorem numericCheck602 (x : Master → ℝ) : Integer.Sparse.eval numericRow602 x =
    (1 : ℝ) * reducedSource602 x := by
  norm_num [numericRow602, reducedSource602, Integer.Sparse.eval, Sparse.eval, nodeValue3503, nodeValue3505, nodeValue3525, nodeValue3532, nodeValue3581, nodeValue4083]

noncomputable def reducedSource603 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2980 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((2 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow603 : Integer.Sparse Master := [(Sum.inr 2980, 1), (Sum.inr 3373, 1), (Sum.inr 3376, 2), (Sum.inr 3505, 1), (Sum.inr 4083, -1)]

theorem reindexCheck603 : Integer.Sparse.reindex keyMap MixedData.row603 = numericRow603 := by decide +kernel

theorem numericCheck603 (x : Master → ℝ) : Integer.Sparse.eval numericRow603 x =
    (1 : ℝ) * reducedSource603 x := by
  norm_num [numericRow603, reducedSource603, Integer.Sparse.eval, Sparse.eval, nodeValue2980, nodeValue3373, nodeValue3376, nodeValue3505, nodeValue3525, nodeValue4083]

noncomputable def reducedSource604 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2012 x + ((1 : ℝ) * Sparse.eval nodeValue3373 x + ((2 : ℝ) * Sparse.eval nodeValue3500 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow604 : Integer.Sparse Master := [(Sum.inr 2012, 1), (Sum.inr 3373, 1), (Sum.inr 3500, 2), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem reindexCheck604 : Integer.Sparse.reindex keyMap MixedData.row604 = numericRow604 := by decide +kernel

theorem numericCheck604 (x : Master → ℝ) : Integer.Sparse.eval numericRow604 x =
    (1 : ℝ) * reducedSource604 x := by
  norm_num [numericRow604, reducedSource604, Integer.Sparse.eval, Sparse.eval, nodeValue2012, nodeValue3373, nodeValue3500, nodeValue3525, nodeValue3526, nodeValue4083]

noncomputable def reducedSource605 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3532 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow605 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 3503, 1), (Sum.inr 3532, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

theorem reindexCheck605 : Integer.Sparse.reindex keyMap MixedData.row605 = numericRow605 := by decide +kernel

theorem numericCheck605 (x : Master → ℝ) : Integer.Sparse.eval numericRow605 x =
    (1 : ℝ) * reducedSource605 x := by
  norm_num [numericRow605, reducedSource605, Integer.Sparse.eval, Sparse.eval, nodeValue2020, nodeValue3376, nodeValue3503, nodeValue3525, nodeValue3532, nodeValue3534, nodeValue4083]

noncomputable def reducedSource606 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3500 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow606 : Integer.Sparse Master := [(Sum.inr 2983, 1), (Sum.inr 3500, 1), (Sum.inr 3503, 2), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem reindexCheck606 : Integer.Sparse.reindex keyMap MixedData.row606 = numericRow606 := by decide +kernel

theorem numericCheck606 (x : Master → ℝ) : Integer.Sparse.eval numericRow606 x =
    (1 : ℝ) * reducedSource606 x := by
  norm_num [numericRow606, reducedSource606, Integer.Sparse.eval, Sparse.eval, nodeValue2983, nodeValue3500, nodeValue3503, nodeValue3525, nodeValue3572, nodeValue4083]

noncomputable def reducedSource607 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2836 x + ((2 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + 0))))))))))))))))))))

def numericRow607 : Integer.Sparse Master := [(Sum.inl 0, -185), (Sum.inl 5, 20), (Sum.inl 6, -10), (Sum.inl 2, -5), (Sum.inl 35, 80), (Sum.inl 3, 320), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 4, 160), (Sum.inl 1, 270), (Sum.inr 1178, 8640), (Sum.inr 1180, 4320), (Sum.inr 1183, 4320), (Sum.inr 1260, 4320), (Sum.inr 2833, 8640), (Sum.inr 2834, 4320), (Sum.inr 2836, 4320), (Sum.inr 2974, 8640), (Sum.inr 2976, 4320), (Sum.inr 3016, 8640), (Sum.inr 3023, 4320), (Sum.inr 3038, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3526, 4320), (Sum.inr 3801, 4320)]

theorem reindexCheck607 : Integer.Sparse.reindex keyMap MixedData.row607 = numericRow607 := by decide +kernel

theorem numericCheck607 (x : Master → ℝ) : Integer.Sparse.eval numericRow607 x =
    (4320 : ℝ) * reducedSource607 x := by
  norm_num [numericRow607, reducedSource607, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue1180, nodeValue1183, nodeValue1260, nodeValue2833, nodeValue2834, nodeValue2836, nodeValue2974, nodeValue2976, nodeValue2996, nodeValue3016, nodeValue3023, nodeValue3038, nodeValue3039, nodeValue3051, nodeValue3085, nodeValue3109, nodeValue3526, nodeValue3801, nodeValue3847, nodeValue3853]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
