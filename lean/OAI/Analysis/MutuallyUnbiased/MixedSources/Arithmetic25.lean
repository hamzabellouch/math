import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource400 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2871 x + ((1 : ℝ) * Sparse.eval nodeValue2975 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow400 : Integer.Sparse Master := [(Sum.inr 2639, 1), (Sum.inr 2871, 1), (Sum.inr 2975, 1), (Sum.inr 2979, 1), (Sum.inr 3055, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem reindexCheck400 : Integer.Sparse.reindex keyMap MixedData.row400 = numericRow400 := by decide +kernel

theorem numericCheck400 (x : Master → ℝ) : Integer.Sparse.eval numericRow400 x =
    (1 : ℝ) * reducedSource400 x := by
  norm_num [numericRow400, reducedSource400, Integer.Sparse.eval, Sparse.eval, nodeValue2639, nodeValue2871, nodeValue2975, nodeValue2979, nodeValue3055, nodeValue3884, nodeValue4092]

noncomputable def reducedSource401 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2882 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow401 : Integer.Sparse Master := [(Sum.inr 2882, 2), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 3055, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

theorem reindexCheck401 : Integer.Sparse.reindex keyMap MixedData.row401 = numericRow401 := by decide +kernel

theorem numericCheck401 (x : Master → ℝ) : Integer.Sparse.eval numericRow401 x =
    (1 : ℝ) * reducedSource401 x := by
  norm_num [numericRow401, reducedSource401, Integer.Sparse.eval, Sparse.eval, nodeValue2882, nodeValue2886, nodeValue2889, nodeValue3055, nodeValue3963, nodeValue4092]

noncomputable def reducedSource402 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow402 : Integer.Sparse Master := [(Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem reindexCheck402 : Integer.Sparse.reindex keyMap MixedData.row402 = numericRow402 := by decide +kernel

theorem numericCheck402 (x : Master → ℝ) : Integer.Sparse.eval numericRow402 x =
    (1 : ℝ) * reducedSource402 x := by
  norm_num [numericRow402, reducedSource402, Integer.Sparse.eval, Sparse.eval, nodeValue1375, nodeValue2889, nodeValue2979, nodeValue3054, nodeValue3055, nodeValue4092]

noncomputable def reducedSource403 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow403 : Integer.Sparse Master := [(Sum.inr 2643, 1), (Sum.inr 3044, 2), (Sum.inr 3046, 1), (Sum.inr 3055, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

theorem reindexCheck403 : Integer.Sparse.reindex keyMap MixedData.row403 = numericRow403 := by decide +kernel

theorem numericCheck403 (x : Master → ℝ) : Integer.Sparse.eval numericRow403 x =
    (1 : ℝ) * reducedSource403 x := by
  norm_num [numericRow403, reducedSource403, Integer.Sparse.eval, Sparse.eval, nodeValue2643, nodeValue3044, nodeValue3046, nodeValue3055, nodeValue3886, nodeValue4092]

noncomputable def reducedSource404 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((2 : ℝ) * Sparse.eval nodeValue2629 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((2 : ℝ) * Sparse.eval nodeValue2729 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3117 x + 0))))))))))))))))))))

def numericRow404 : Integer.Sparse Master := [(Sum.inl 0, -138), (Sum.inl 2, 160), (Sum.inl 3, 320), (Sum.inl 13, 160), (Sum.inl 55, -480), (Sum.inl 12, 160), (Sum.inl 27, -120), (Sum.inl 1, 130), (Sum.inr 2129, 8640), (Sum.inr 2130, 4320), (Sum.inr 2138, 4320), (Sum.inr 2251, 8640), (Sum.inr 2276, 4320), (Sum.inr 2278, 4320), (Sum.inr 2282, 4320), (Sum.inr 2629, 8640), (Sum.inr 2643, 4320), (Sum.inr 2713, 8640), (Sum.inr 2729, 8640), (Sum.inr 2731, 8640), (Sum.inr 2751, 8640), (Sum.inr 2758, 8640), (Sum.inr 2765, 4320), (Sum.inr 2771, 4320), (Sum.inr 3092, 8640)]

theorem reindexCheck404 : Integer.Sparse.reindex keyMap MixedData.row404 = numericRow404 := by decide +kernel

theorem numericCheck404 (x : Master → ℝ) : Integer.Sparse.eval numericRow404 x =
    (4320 : ℝ) * reducedSource404 x := by
  norm_num [numericRow404, reducedSource404, Integer.Sparse.eval, Sparse.eval, nodeValue2129, nodeValue2130, nodeValue2138, nodeValue2251, nodeValue2276, nodeValue2278, nodeValue2282, nodeValue2629, nodeValue2643, nodeValue2713, nodeValue2729, nodeValue2731, nodeValue2751, nodeValue2758, nodeValue2765, nodeValue2767, nodeValue2771, nodeValue2776, nodeValue3092, nodeValue3110, nodeValue3117]
  ring

noncomputable def reducedSource405 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow405 : Integer.Sparse Master := [(Sum.inr 2888, 1), (Sum.inr 3392, 2), (Sum.inr 3397, 1), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck405 : Integer.Sparse.reindex keyMap MixedData.row405 = numericRow405 := by decide +kernel

theorem numericCheck405 (x : Master → ℝ) : Integer.Sparse.eval numericRow405 x =
    (1 : ℝ) * reducedSource405 x := by
  norm_num [numericRow405, reducedSource405, Integer.Sparse.eval, Sparse.eval, nodeValue2888, nodeValue3392, nodeValue3397, nodeValue3548, nodeValue3584, nodeValue4084]

noncomputable def reducedSource406 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow406 : Integer.Sparse Master := [(Sum.inr 2108, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 2266, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck406 : Integer.Sparse.reindex keyMap MixedData.row406 = numericRow406 := by decide +kernel

theorem numericCheck406 (x : Master → ℝ) : Integer.Sparse.eval numericRow406 x =
    (1 : ℝ) * reducedSource406 x := by
  norm_num [numericRow406, reducedSource406, Integer.Sparse.eval, Sparse.eval, nodeValue2108, nodeValue2113, nodeValue2115, nodeValue2266, nodeValue3584, nodeValue4084]

noncomputable def reducedSource407 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow407 : Integer.Sparse Master := [(Sum.inr 2108, 1), (Sum.inr 2883, 1), (Sum.inr 3504, 1), (Sum.inr 3577, 1), (Sum.inr 3580, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck407 : Integer.Sparse.reindex keyMap MixedData.row407 = numericRow407 := by decide +kernel

theorem numericCheck407 (x : Master → ℝ) : Integer.Sparse.eval numericRow407 x =
    (1 : ℝ) * reducedSource407 x := by
  norm_num [numericRow407, reducedSource407, Integer.Sparse.eval, Sparse.eval, nodeValue2108, nodeValue2883, nodeValue3504, nodeValue3577, nodeValue3580, nodeValue3584, nodeValue4084]

noncomputable def reducedSource408 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((2 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow408 : Integer.Sparse Master := [(Sum.inr 2113, 1), (Sum.inr 2887, 1), (Sum.inr 3157, 2), (Sum.inr 3161, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck408 : Integer.Sparse.reindex keyMap MixedData.row408 = numericRow408 := by decide +kernel

theorem numericCheck408 (x : Master → ℝ) : Integer.Sparse.eval numericRow408 x =
    (1 : ℝ) * reducedSource408 x := by
  norm_num [numericRow408, reducedSource408, Integer.Sparse.eval, Sparse.eval, nodeValue2113, nodeValue2887, nodeValue3157, nodeValue3161, nodeValue3584, nodeValue4084]

noncomputable def reducedSource409 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2883 x + ((1 : ℝ) * Sparse.eval nodeValue2887 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow409 : Integer.Sparse Master := [(Sum.inr 2883, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 3056, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck409 : Integer.Sparse.reindex keyMap MixedData.row409 = numericRow409 := by decide +kernel

theorem numericCheck409 (x : Master → ℝ) : Integer.Sparse.eval numericRow409 x =
    (1 : ℝ) * reducedSource409 x := by
  norm_num [numericRow409, reducedSource409, Integer.Sparse.eval, Sparse.eval, nodeValue2883, nodeValue2887, nodeValue2888, nodeValue3056, nodeValue3584, nodeValue4084]

noncomputable def reducedSource410 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((2 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow410 : Integer.Sparse Master := [(Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 3506, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck410 : Integer.Sparse.reindex keyMap MixedData.row410 = numericRow410 := by decide +kernel

theorem numericCheck410 (x : Master → ℝ) : Integer.Sparse.eval numericRow410 x =
    (1 : ℝ) * reducedSource410 x := by
  norm_num [numericRow410, reducedSource410, Integer.Sparse.eval, Sparse.eval, nodeValue2115, nodeValue3056, nodeValue3506, nodeValue3582, nodeValue3584, nodeValue4084]

noncomputable def reducedSource411 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue5086 x + ((2 : ℝ) * Sparse.eval nodeValue5087 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

def numericRow411 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 25), (Sum.inr 2519, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 3486, -2160), (Sum.inr 3624, -4320), (Sum.inr 3631, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 4475, 17280), (Sum.inr 4476, 8640), (Sum.inr 4480, 8640), (Sum.inr 4500, 8640), (Sum.inr 5086, 17280), (Sum.inr 5087, 17280), (Sum.inr 5090, 17280), (Sum.inr 5103, 17280), (Sum.inr 5267, 17280), (Sum.inr 5268, 8640), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640)]

theorem reindexCheck411 : Integer.Sparse.reindex keyMap MixedData.row411 = numericRow411 := by decide +kernel

theorem numericCheck411 (x : Master → ℝ) : Integer.Sparse.eval numericRow411 x =
    (8640 : ℝ) * reducedSource411 x := by
  norm_num [numericRow411, reducedSource411, Integer.Sparse.eval, Sparse.eval, nodeValue4475, nodeValue4476, nodeValue4480, nodeValue4500, nodeValue5086, nodeValue5087, nodeValue5090, nodeValue5103, nodeValue5109, nodeValue5204, nodeValue5207, nodeValue5267, nodeValue5268, nodeValue5276, nodeValue5295, nodeValue5299, nodeValue5300, nodeValue5411, nodeValue5413, nodeValue5443, nodeValue5451]
  ring

noncomputable def reducedSource412 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2494 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((2 : ℝ) * Sparse.eval nodeValue2499 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4006 x + 0))))))))))))))))))))

def numericRow412 : Integer.Sparse Master := [(Sum.inl 0, -55), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 95), (Sum.inr 1058, 2160), (Sum.inr 1059, 1080), (Sum.inr 1063, 1080), (Sum.inr 1084, 1080), (Sum.inr 2494, 2160), (Sum.inr 2495, 2160), (Sum.inr 2499, 2160), (Sum.inr 2513, 2160), (Sum.inr 2732, 2160), (Sum.inr 2734, 1080), (Sum.inr 2744, 1080), (Sum.inr 2773, 2160), (Sum.inr 2774, 1080), (Sum.inr 2781, 1080)]

theorem reindexCheck412 : Integer.Sparse.reindex keyMap MixedData.row412 = numericRow412 := by decide +kernel

theorem numericCheck412 (x : Master → ℝ) : Integer.Sparse.eval numericRow412 x =
    (1080 : ℝ) * reducedSource412 x := by
  norm_num [numericRow412, reducedSource412, Integer.Sparse.eval, Sparse.eval, nodeValue1058, nodeValue1059, nodeValue1063, nodeValue1084, nodeValue2494, nodeValue2495, nodeValue2499, nodeValue2513, nodeValue2638, nodeValue2640, nodeValue2644, nodeValue2732, nodeValue2734, nodeValue2744, nodeValue2773, nodeValue2774, nodeValue2781, nodeValue3883, nodeValue3888, nodeValue3889, nodeValue4006]
  ring

noncomputable def reducedSource413 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))

def numericRow413 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 1715, 4320), (Sum.inr 1716, 2160), (Sum.inr 1729, 2160), (Sum.inr 1740, 2160), (Sum.inr 3024, 4320), (Sum.inr 3052, 2160), (Sum.inr 3098, 2160), (Sum.inr 3464, 4320), (Sum.inr 3472, 4320), (Sum.inr 3480, 4320), (Sum.inr 3486, 2160), (Sum.inr 3541, 4320), (Sum.inr 3549, 2160), (Sum.inr 3573, 4320), (Sum.inr 3584, 2160), (Sum.inr 3624, 4320), (Sum.inr 3631, 2160), (Sum.inr 3809, 4320)]

theorem reindexCheck413 : Integer.Sparse.reindex keyMap MixedData.row413 = numericRow413 := by decide +kernel

theorem numericCheck413 (x : Master → ℝ) : Integer.Sparse.eval numericRow413 x =
    (2160 : ℝ) * reducedSource413 x := by
  norm_num [numericRow413, reducedSource413, Integer.Sparse.eval, Sparse.eval, nodeValue1715, nodeValue1716, nodeValue1729, nodeValue1740, nodeValue3024, nodeValue3052, nodeValue3098, nodeValue3464, nodeValue3472, nodeValue3480, nodeValue3486, nodeValue3541, nodeValue3549, nodeValue3573, nodeValue3584, nodeValue3624, nodeValue3631, nodeValue3809, nodeValue3817, nodeValue3862, nodeValue3987]
  ring

noncomputable def reducedSource414 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow414 : Integer.Sparse Master := [(Sum.inr 3054, 1), (Sum.inr 3813, 2), (Sum.inr 3907, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem reindexCheck414 : Integer.Sparse.reindex keyMap MixedData.row414 = numericRow414 := by decide +kernel

theorem numericCheck414 (x : Master → ℝ) : Integer.Sparse.eval numericRow414 x =
    (1 : ℝ) * reducedSource414 x := by
  norm_num [numericRow414, reducedSource414, Integer.Sparse.eval, Sparse.eval, nodeValue3054, nodeValue3813, nodeValue3817, nodeValue3907, nodeValue3913, nodeValue4092]

noncomputable def reducedSource415 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow415 : Integer.Sparse Master := [(Sum.inr 1367, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1436, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem reindexCheck415 : Integer.Sparse.reindex keyMap MixedData.row415 = numericRow415 := by decide +kernel

theorem numericCheck415 (x : Master → ℝ) : Integer.Sparse.eval numericRow415 x =
    (1 : ℝ) * reducedSource415 x := by
  norm_num [numericRow415, reducedSource415, Integer.Sparse.eval, Sparse.eval, nodeValue1367, nodeValue1372, nodeValue1375, nodeValue1436, nodeValue3054, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
