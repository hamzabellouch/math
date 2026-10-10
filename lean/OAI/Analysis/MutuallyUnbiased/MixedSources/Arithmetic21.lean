import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource336 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow336 : Integer.Sparse Master := [(Sum.inr 3488, 1), (Sum.inr 3493, 1), (Sum.inr 3533, 2), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

theorem reindexCheck336 : Integer.Sparse.reindex keyMap MixedData.row336 = numericRow336 := by decide +kernel

theorem numericCheck336 (x : Master → ℝ) : Integer.Sparse.eval numericRow336 x =
    (1 : ℝ) * reducedSource336 x := by
  norm_num [numericRow336, reducedSource336, Integer.Sparse.eval, Sparse.eval, nodeValue2552, nodeValue3488, nodeValue3493, nodeValue3533, nodeValue3539, nodeValue4084]

noncomputable def reducedSource337 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2033 x + ((2 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow337 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2034, 2), (Sum.inr 2051, 1), (Sum.inr 2277, 1), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

theorem reindexCheck337 : Integer.Sparse.reindex keyMap MixedData.row337 = numericRow337 := by decide +kernel

theorem numericCheck337 (x : Master → ℝ) : Integer.Sparse.eval numericRow337 x =
    (1 : ℝ) * reducedSource337 x := by
  norm_num [numericRow337, reducedSource337, Integer.Sparse.eval, Sparse.eval, nodeValue2033, nodeValue2034, nodeValue2051, nodeValue2277, nodeValue3539, nodeValue4084]

noncomputable def reducedSource338 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow338 : Integer.Sparse Master := [(Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 3539, 1), (Sum.inr 3625, 1), (Sum.inr 3632, 2), (Sum.inr 4084, -1)]

theorem reindexCheck338 : Integer.Sparse.reindex keyMap MixedData.row338 = numericRow338 := by decide +kernel

theorem numericCheck338 (x : Master → ℝ) : Integer.Sparse.eval numericRow338 x =
    (1 : ℝ) * reducedSource338 x := by
  norm_num [numericRow338, reducedSource338, Integer.Sparse.eval, Sparse.eval, nodeValue2277, nodeValue2738, nodeValue3539, nodeValue3625, nodeValue3632, nodeValue4084]

noncomputable def reducedSource339 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5170 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((3 : ℝ) * Sparse.eval nodeValue5302 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))

def numericRow339 : Integer.Sparse Master := [(Sum.inl 0, 61), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, 80), (Sum.inl 1, 390), (Sum.inr 1294, -2160), (Sum.inr 1297, -720), (Sum.inr 2112, -2160), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2289, -720), (Sum.inr 2294, -720), (Sum.inr 2954, -4320), (Sum.inr 3054, -2160), (Sum.inr 3305, -2160), (Sum.inr 3311, -720), (Sum.inr 3606, -4320), (Sum.inr 3614, -2160), (Sum.inr 3623, -2160), (Sum.inr 3626, -2160), (Sum.inr 3907, -2160)]

theorem reindexCheck339 : Integer.Sparse.reindex keyMap MixedData.row339 = numericRow339 := by decide +kernel

theorem numericCheck339 (x : Master → ℝ) : Integer.Sparse.eval numericRow339 x =
    (2880 : ℝ) * reducedSource339 x := by
  norm_num [numericRow339, reducedSource339, Integer.Sparse.eval, Sparse.eval, nodeValue4619, nodeValue4621, nodeValue4627, nodeValue4871, nodeValue4899, nodeValue5170, nodeValue5176, nodeValue5302, nodeValue5306, nodeValue5308, nodeValue5443, nodeValue5455, nodeValue5456]
  ring

noncomputable def reducedSource340 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((6 : ℝ) * Sparse.eval nodeValue2954 x + ((3 : ℝ) * Sparse.eval nodeValue2968 x + ((3 : ℝ) * Sparse.eval nodeValue3054 x + ((3 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((3 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))

def numericRow340 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1294, 720), (Sum.inr 1297, 240), (Sum.inr 2112, 720), (Sum.inr 2281, 240), (Sum.inr 2954, 1440), (Sum.inr 3054, 720)]

theorem reindexCheck340 : Integer.Sparse.reindex keyMap MixedData.row340 = numericRow340 := by decide +kernel

theorem numericCheck340 (x : Master → ℝ) : Integer.Sparse.eval numericRow340 x =
    (240 : ℝ) * reducedSource340 x := by
  norm_num [numericRow340, reducedSource340, Integer.Sparse.eval, Sparse.eval, nodeValue1294, nodeValue1297, nodeValue1311, nodeValue2112, nodeValue2281, nodeValue2954, nodeValue2968, nodeValue3054, nodeValue3120, nodeValue3124, nodeValue3889, nodeValue3916, nodeValue4019]
  ring

noncomputable def reducedSource341 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue5105 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((3 : ℝ) * Sparse.eval nodeValue5110 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((3 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((3 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))

def numericRow341 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 1087, -2160), (Sum.inr 1091, -720), (Sum.inr 1094, -720), (Sum.inr 1739, -2160), (Sum.inr 1741, -720), (Sum.inr 1756, -720), (Sum.inr 2515, -4320), (Sum.inr 2519, -2160), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2782, -2160), (Sum.inr 2783, -1440), (Sum.inr 3479, -4320), (Sum.inr 3486, -2160), (Sum.inr 3583, -2160), (Sum.inr 3632, -2160), (Sum.inr 3634, -720), (Sum.inr 3913, -2160)]

theorem reindexCheck341 : Integer.Sparse.reindex keyMap MixedData.row341 = numericRow341 := by decide +kernel

theorem numericCheck341 (x : Master → ℝ) : Integer.Sparse.eval numericRow341 x =
    (2880 : ℝ) * reducedSource341 x := by
  norm_num [numericRow341, reducedSource341, Integer.Sparse.eval, Sparse.eval, nodeValue4503, nodeValue4507, nodeValue4510, nodeValue5105, nodeValue5109, nodeValue5110, nodeValue5294, nodeValue5296, nodeValue5304, nodeValue5305, nodeValue5451, nodeValue5455, nodeValue5494]
  ring

noncomputable def reducedSource342 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((6 : ℝ) * Sparse.eval nodeValue2515 x + ((3 : ℝ) * Sparse.eval nodeValue2519 x + ((3 : ℝ) * Sparse.eval nodeValue2522 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((3 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + 0))))))))))))

def numericRow342 : Integer.Sparse Master := [(Sum.inl 0, -5), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 8), (Sum.inr 1087, 216), (Sum.inr 1091, 72), (Sum.inr 1094, 72), (Sum.inr 2515, 432), (Sum.inr 2519, 216), (Sum.inr 2522, 216), (Sum.inr 2782, 216), (Sum.inr 2783, 72)]

theorem reindexCheck342 : Integer.Sparse.reindex keyMap MixedData.row342 = numericRow342 := by decide +kernel

theorem numericCheck342 (x : Master → ℝ) : Integer.Sparse.eval numericRow342 x =
    (72 : ℝ) * reducedSource342 x := by
  norm_num [numericRow342, reducedSource342, Integer.Sparse.eval, Sparse.eval, nodeValue1087, nodeValue1091, nodeValue1094, nodeValue2515, nodeValue2519, nodeValue2522, nodeValue2768, nodeValue2770, nodeValue2782, nodeValue2783, nodeValue3987, nodeValue4019, nodeValue4020]
  ring

noncomputable def reducedSource343 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((6 : ℝ) * Sparse.eval nodeValue5260 x + ((3 : ℝ) * Sparse.eval nodeValue5275 x + ((3 : ℝ) * Sparse.eval nodeValue5276 x + ((3 : ℝ) * Sparse.eval nodeValue5291 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((3 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

def numericRow343 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2281, -720), (Sum.inr 2294, -720), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 2783, -1440), (Sum.inr 3548, -2160), (Sum.inr 3582, -2160), (Sum.inr 3632, -2160), (Sum.inr 5260, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640), (Sum.inr 5311, 2880)]

theorem reindexCheck343 : Integer.Sparse.reindex keyMap MixedData.row343 = numericRow343 := by decide +kernel

theorem numericCheck343 (x : Master → ℝ) : Integer.Sparse.eval numericRow343 x =
    (2880 : ℝ) * reducedSource343 x := by
  norm_num [numericRow343, reducedSource343, Integer.Sparse.eval, Sparse.eval, nodeValue4896, nodeValue4899, nodeValue4901, nodeValue5260, nodeValue5275, nodeValue5276, nodeValue5291, nodeValue5294, nodeValue5295, nodeValue5305, nodeValue5308, nodeValue5309, nodeValue5311]
  ring

noncomputable def reducedSource344 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((6 : ℝ) * Sparse.eval nodeValue2724 x + ((3 : ℝ) * Sparse.eval nodeValue2743 x + ((3 : ℝ) * Sparse.eval nodeValue2744 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((3 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((3 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))

def numericRow344 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2266, 1080), (Sum.inr 2294, 360), (Sum.inr 2724, 2160), (Sum.inr 2743, 1080), (Sum.inr 2744, 1080), (Sum.inr 2769, 1080), (Sum.inr 2789, 360)]

theorem reindexCheck344 : Integer.Sparse.reindex keyMap MixedData.row344 = numericRow344 := by decide +kernel

theorem numericCheck344 (x : Master → ℝ) : Integer.Sparse.eval numericRow344 x =
    (360 : ℝ) * reducedSource344 x := by
  norm_num [numericRow344, reducedSource344, Integer.Sparse.eval, Sparse.eval, nodeValue2266, nodeValue2293, nodeValue2294, nodeValue2724, nodeValue2743, nodeValue2744, nodeValue2768, nodeValue2769, nodeValue2787, nodeValue2789, nodeValue3103, nodeValue3124, nodeValue3125]
  ring

noncomputable def reducedSource345 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2765 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((6 : ℝ) * Sparse.eval nodeValue3086 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((3 : ℝ) * Sparse.eval nodeValue3101 x + ((3 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((3 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))

def numericRow345 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2765, 720), (Sum.inr 2777, 720), (Sum.inr 2783, 240), (Sum.inr 2789, 240), (Sum.inr 3086, 1440), (Sum.inr 3098, 720)]

theorem reindexCheck345 : Integer.Sparse.reindex keyMap MixedData.row345 = numericRow345 := by decide +kernel

theorem numericCheck345 (x : Master → ℝ) : Integer.Sparse.eval numericRow345 x =
    (240 : ℝ) * reducedSource345 x := by
  norm_num [numericRow345, reducedSource345, Integer.Sparse.eval, Sparse.eval, nodeValue2765, nodeValue2777, nodeValue2778, nodeValue2783, nodeValue2786, nodeValue2789, nodeValue3086, nodeValue3098, nodeValue3101, nodeValue3110, nodeValue3123, nodeValue3225, nodeValue3231]
  ring

noncomputable def reducedSource346 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow346 : Integer.Sparse Master := [(Sum.inr 2783, 1), (Sum.inr 3582, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck346 : Integer.Sparse.reindex keyMap MixedData.row346 = numericRow346 := by decide +kernel

theorem numericCheck346 (x : Master → ℝ) : Integer.Sparse.eval numericRow346 x =
    (1 : ℝ) * reducedSource346 x := by
  norm_num [numericRow346, reducedSource346, Integer.Sparse.eval, Sparse.eval, nodeValue2783, nodeValue3582, nodeValue3629, nodeValue3633, nodeValue4084]

noncomputable def reducedSource347 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3629 x + ((3 : ℝ) * Sparse.eval nodeValue3632 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow347 : Integer.Sparse Master := [(Sum.inr 3632, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck347 : Integer.Sparse.reindex keyMap MixedData.row347 = numericRow347 := by decide +kernel

theorem numericCheck347 (x : Master → ℝ) : Integer.Sparse.eval numericRow347 x =
    (1 : ℝ) * reducedSource347 x := by
  norm_num [numericRow347, reducedSource347, Integer.Sparse.eval, Sparse.eval, nodeValue3629, nodeValue3632, nodeValue3633, nodeValue3635, nodeValue4084]

noncomputable def reducedSource348 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2293 x + ((3 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow348 : Integer.Sparse Master := [(Sum.inr 3548, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck348 : Integer.Sparse.reindex keyMap MixedData.row348 = numericRow348 := by decide +kernel

theorem numericCheck348 (x : Master → ℝ) : Integer.Sparse.eval numericRow348 x =
    (1 : ℝ) * reducedSource348 x := by
  norm_num [numericRow348, reducedSource348, Integer.Sparse.eval, Sparse.eval, nodeValue2293, nodeValue3548, nodeValue3633, nodeValue3635, nodeValue4084]

noncomputable def reducedSource349 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1088 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue1093 x + ((6 : ℝ) * Sparse.eval nodeValue2516 x + ((3 : ℝ) * Sparse.eval nodeValue2520 x + ((3 : ℝ) * Sparse.eval nodeValue2521 x + ((3 : ℝ) * Sparse.eval nodeValue2761 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

def numericRow349 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, -25), (Sum.inr 1088, 2160), (Sum.inr 1092, 720), (Sum.inr 1093, 720), (Sum.inr 2516, 4320), (Sum.inr 2520, 2160), (Sum.inr 2521, 2160), (Sum.inr 2761, 2160), (Sum.inr 2777, 2160), (Sum.inr 2780, 720), (Sum.inr 2783, 720), (Sum.inr 3098, 2160)]

theorem reindexCheck349 : Integer.Sparse.reindex keyMap MixedData.row349 = numericRow349 := by decide +kernel

theorem numericCheck349 (x : Master → ℝ) : Integer.Sparse.eval numericRow349 x =
    (720 : ℝ) * reducedSource349 x := by
  norm_num [numericRow349, reducedSource349, Integer.Sparse.eval, Sparse.eval, nodeValue1088, nodeValue1092, nodeValue1093, nodeValue2516, nodeValue2520, nodeValue2521, nodeValue2761, nodeValue2777, nodeValue2778, nodeValue2780, nodeValue2783, nodeValue3098, nodeValue3121]
  ring

noncomputable def reducedSource350 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1303 x + ((1 : ℝ) * Sparse.eval nodeValue1309 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow350 : Integer.Sparse Master := [(Sum.inr 1303, 3), (Sum.inr 1309, 1), (Sum.inr 1310, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem reindexCheck350 : Integer.Sparse.reindex keyMap MixedData.row350 = numericRow350 := by decide +kernel

theorem numericCheck350 (x : Master → ℝ) : Integer.Sparse.eval numericRow350 x =
    (1 : ℝ) * reducedSource350 x := by
  norm_num [numericRow350, reducedSource350, Integer.Sparse.eval, Sparse.eval, nodeValue1303, nodeValue1309, nodeValue1310, nodeValue2789, nodeValue4084]

noncomputable def reducedSource351 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1303 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((2 : ℝ) * Sparse.eval nodeValue2597 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow351 : Integer.Sparse Master := [(Sum.inr 1303, 1), (Sum.inr 2134, 1), (Sum.inr 2597, 2), (Sum.inr 2781, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem reindexCheck351 : Integer.Sparse.reindex keyMap MixedData.row351 = numericRow351 := by decide +kernel

theorem numericCheck351 (x : Master → ℝ) : Integer.Sparse.eval numericRow351 x =
    (1 : ℝ) * reducedSource351 x := by
  norm_num [numericRow351, reducedSource351, Integer.Sparse.eval, Sparse.eval, nodeValue1303, nodeValue2134, nodeValue2597, nodeValue2781, nodeValue2789, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
