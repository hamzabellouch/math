import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1936 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1704 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1721 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3465 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3587 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((2 : ℝ) * Sparse.eval nodeValue3592 x + ((1 : ℝ) * Sparse.eval nodeValue3617 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((2 : ℝ) * Sparse.eval nodeValue3621 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3952 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((1 : ℝ) * Sparse.eval nodeValue3962 x + 0))))))))))))))))))))

def numericRow1936 : Integer.Sparse Master := [(Sum.inr 1703, 1), (Sum.inr 1704, 1), (Sum.inr 1709, 1), (Sum.inr 1721, 2), (Sum.inr 3458, 1), (Sum.inr 3461, 1), (Sum.inr 3465, 2), (Sum.inr 3529, 2), (Sum.inr 3530, 2), (Sum.inr 3535, 2), (Sum.inr 3542, 2), (Sum.inr 3587, 1), (Sum.inr 3588, 1), (Sum.inr 3592, 2), (Sum.inr 3617, 1), (Sum.inr 3619, 1), (Sum.inr 3621, 2), (Sum.inr 3952, 1), (Sum.inr 3961, 2)]

theorem reindexCheck1936 : Integer.Sparse.reindex keyMap MixedData.row1936 = numericRow1936 := by decide +kernel

theorem numericCheck1936 (x : Master → ℝ) : Integer.Sparse.eval numericRow1936 x =
    (1 : ℝ) * reducedSource1936 x := by
  norm_num [numericRow1936, reducedSource1936, Integer.Sparse.eval, Sparse.eval, nodeValue1703, nodeValue1704, nodeValue1709, nodeValue1721, nodeValue3458, nodeValue3461, nodeValue3465, nodeValue3529, nodeValue3530, nodeValue3535, nodeValue3542, nodeValue3587, nodeValue3588, nodeValue3592, nodeValue3617, nodeValue3619, nodeValue3621, nodeValue3774, nodeValue3952, nodeValue3961, nodeValue3962]

noncomputable def reducedSource1937 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5197 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow1937 : Integer.Sparse Master := [(Sum.inr 2434, -1), (Sum.inr 2519, -1), (Sum.inr 2807, -1), (Sum.inr 2813, -1), (Sum.inr 2817, -1), (Sum.inr 2881, -1), (Sum.inr 2889, -1), (Sum.inr 3054, -1), (Sum.inr 3457, -1), (Sum.inr 3486, -1), (Sum.inr 3590, -1), (Sum.inr 3591, -1), (Sum.inr 3595, -1), (Sum.inr 3624, -1), (Sum.inr 3626, -1), (Sum.inr 3631, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3845, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4366, 4), (Sum.inr 4367, 4), (Sum.inr 4368, 4), (Sum.inr 4372, 4), (Sum.inr 4475, 4), (Sum.inr 5034, 4), (Sum.inr 5042, 4), (Sum.inr 5044, 4), (Sum.inr 5086, 4), (Sum.inr 5139, 4), (Sum.inr 5187, 4), (Sum.inr 5188, 4), (Sum.inr 5197, 4), (Sum.inr 5198, 4), (Sum.inr 5199, 4), (Sum.inr 5267, 4), (Sum.inr 5299, 4)]

theorem reindexCheck1937 : Integer.Sparse.reindex keyMap MixedData.row1937 = numericRow1937 := by decide +kernel

theorem numericCheck1937 (x : Master → ℝ) : Integer.Sparse.eval numericRow1937 x =
    (4 : ℝ) * reducedSource1937 x := by
  norm_num [numericRow1937, reducedSource1937, Integer.Sparse.eval, Sparse.eval, nodeValue4366, nodeValue4367, nodeValue4368, nodeValue4372, nodeValue4475, nodeValue4971, nodeValue4972, nodeValue4973, nodeValue4977, nodeValue5034, nodeValue5042, nodeValue5044, nodeValue5086, nodeValue5109, nodeValue5139, nodeValue5187, nodeValue5188, nodeValue5197, nodeValue5198, nodeValue5199, nodeValue5204, nodeValue5207, nodeValue5267, nodeValue5299, nodeValue5302, nodeValue5367, nodeValue5395, nodeValue5413, nodeValue5428, nodeValue5473]
  ring

noncomputable def reducedSource1938 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1711 x + ((1 : ℝ) * Sparse.eval nodeValue1712 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3590 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + 0)))))))))))))))))))))))))))))

def numericRow1938 : Integer.Sparse Master := [(Sum.inr 1711, 1), (Sum.inr 1712, 1), (Sum.inr 1715, 1), (Sum.inr 1720, 1), (Sum.inr 1734, 1), (Sum.inr 3451, 1), (Sum.inr 3457, 1), (Sum.inr 3462, 1), (Sum.inr 3464, 1), (Sum.inr 3474, 1), (Sum.inr 3486, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3569, 1), (Sum.inr 3570, 1), (Sum.inr 3573, 1), (Sum.inr 3578, 1), (Sum.inr 3590, 1), (Sum.inr 3591, 1), (Sum.inr 3595, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3631, 1), (Sum.inr 3794, 1), (Sum.inr 3845, 1), (Sum.inr 3958, 1)]

theorem reindexCheck1938 : Integer.Sparse.reindex keyMap MixedData.row1938 = numericRow1938 := by decide +kernel

theorem numericCheck1938 (x : Master → ℝ) : Integer.Sparse.eval numericRow1938 x =
    (1 : ℝ) * reducedSource1938 x := by
  norm_num [numericRow1938, reducedSource1938, Integer.Sparse.eval, Sparse.eval, nodeValue1711, nodeValue1712, nodeValue1715, nodeValue1720, nodeValue1734, nodeValue3451, nodeValue3457, nodeValue3462, nodeValue3464, nodeValue3474, nodeValue3486, nodeValue3523, nodeValue3537, nodeValue3538, nodeValue3541, nodeValue3569, nodeValue3570, nodeValue3573, nodeValue3578, nodeValue3590, nodeValue3591, nodeValue3595, nodeValue3624, nodeValue3626, nodeValue3631, nodeValue3766, nodeValue3794, nodeValue3817, nodeValue3845, nodeValue3958]

noncomputable def reducedSource1939 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1970 x + ((1 : ℝ) * Sparse.eval nodeValue2806 x + ((2 : ℝ) * Sparse.eval nodeValue2812 x + ((1 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue3498 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1939 : Integer.Sparse Master := [(Sum.inr 1970, 1), (Sum.inr 2806, 1), (Sum.inr 2812, 2), (Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1939 : Integer.Sparse.reindex keyMap MixedData.row1939 = numericRow1939 := by decide +kernel

theorem numericCheck1939 (x : Master → ℝ) : Integer.Sparse.eval numericRow1939 x =
    (1 : ℝ) * reducedSource1939 x := by
  norm_num [numericRow1939, reducedSource1939, Integer.Sparse.eval, Sparse.eval, nodeValue1970, nodeValue2806, nodeValue2812, nodeValue2879, nodeValue3498, nodeValue4084]

noncomputable def reducedSource1940 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((2 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0)))))

def numericRow1940 : Integer.Sparse Master := [(Sum.inr 2607, 1), (Sum.inr 3067, 1), (Sum.inr 3751, 1), (Sum.inr 3866, 2), (Sum.inr 3867, 1), (Sum.inr 4087, -1)]

theorem reindexCheck1940 : Integer.Sparse.reindex keyMap MixedData.row1940 = numericRow1940 := by decide +kernel

theorem numericCheck1940 (x : Master → ℝ) : Integer.Sparse.eval numericRow1940 x =
    (1 : ℝ) * reducedSource1940 x := by
  norm_num [numericRow1940, reducedSource1940, Integer.Sparse.eval, Sparse.eval, nodeValue2607, nodeValue3067, nodeValue3751, nodeValue3866, nodeValue3867, nodeValue4087]

noncomputable def reducedSource1941 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4548 x + ((1 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((1 : ℝ) * Sparse.eval nodeValue5116 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + 0)))))))))))))))))))))))))))))

def numericRow1941 : Integer.Sparse Master := [(Sum.inr 1294, -1), (Sum.inr 2482, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3564, -1), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 3732, -1), (Sum.inr 3786, -1), (Sum.inr 3799, -1), (Sum.inr 3811, -1), (Sum.inr 3850, -2), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 4545, 4), (Sum.inr 4547, 4), (Sum.inr 4548, 4), (Sum.inr 4556, 4), (Sum.inr 4963, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 4976, 4), (Sum.inr 5041, 4), (Sum.inr 5112, 4), (Sum.inr 5116, 4), (Sum.inr 5144, 4), (Sum.inr 5147, 4), (Sum.inr 5151, 4), (Sum.inr 5160, 4), (Sum.inr 5164, 4), (Sum.inr 5173, 4)]

theorem reindexCheck1941 : Integer.Sparse.reindex keyMap MixedData.row1941 = numericRow1941 := by decide +kernel

theorem numericCheck1941 (x : Master → ℝ) : Integer.Sparse.eval numericRow1941 x =
    (4 : ℝ) * reducedSource1941 x := by
  norm_num [numericRow1941, reducedSource1941, Integer.Sparse.eval, Sparse.eval, nodeValue4545, nodeValue4547, nodeValue4548, nodeValue4556, nodeValue4619, nodeValue4963, nodeValue4965, nodeValue4966, nodeValue4976, nodeValue5041, nodeValue5075, nodeValue5112, nodeValue5116, nodeValue5134, nodeValue5141, nodeValue5144, nodeValue5147, nodeValue5151, nodeValue5160, nodeValue5163, nodeValue5164, nodeValue5173, nodeValue5274, nodeValue5291, nodeValue5304, nodeValue5384, nodeValue5400, nodeValue5409, nodeValue5432, nodeValue5438]
  ring

noncomputable def reducedSource1942 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2655 x + ((1 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue2659 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3271 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + 0)))))))))))))))))))))))))))))

def numericRow1942 : Integer.Sparse Master := [(Sum.inr 2655, 1), (Sum.inr 2657, 1), (Sum.inr 2659, 1), (Sum.inr 2681, 1), (Sum.inr 2735, 1), (Sum.inr 3259, 1), (Sum.inr 3266, 1), (Sum.inr 3271, 1), (Sum.inr 3305, 1), (Sum.inr 3458, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3582, 1), (Sum.inr 3583, 1), (Sum.inr 3799, 1), (Sum.inr 3811, 1), (Sum.inr 3850, 1), (Sum.inr 3876, 1)]

theorem reindexCheck1942 : Integer.Sparse.reindex keyMap MixedData.row1942 = numericRow1942 := by decide +kernel

theorem numericCheck1942 (x : Master → ℝ) : Integer.Sparse.eval numericRow1942 x =
    (1 : ℝ) * reducedSource1942 x := by
  norm_num [numericRow1942, reducedSource1942, Integer.Sparse.eval, Sparse.eval, nodeValue2655, nodeValue2657, nodeValue2659, nodeValue2681, nodeValue2735, nodeValue3259, nodeValue3266, nodeValue3271, nodeValue3305, nodeValue3458, nodeValue3468, nodeValue3475, nodeValue3514, nodeValue3522, nodeValue3530, nodeValue3547, nodeValue3553, nodeValue3555, nodeValue3556, nodeValue3557, nodeValue3558, nodeValue3564, nodeValue3565, nodeValue3582, nodeValue3583, nodeValue3799, nodeValue3807, nodeValue3811, nodeValue3850, nodeValue3876]

noncomputable def reducedSource1943 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1943 : Integer.Sparse Master := [(Sum.inr 2353, 1), (Sum.inr 2355, 1), (Sum.inr 2356, 1), (Sum.inr 2362, 1), (Sum.inr 2590, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1943 : Integer.Sparse.reindex keyMap MixedData.row1943 = numericRow1943 := by decide +kernel

theorem numericCheck1943 (x : Master → ℝ) : Integer.Sparse.eval numericRow1943 x =
    (1 : ℝ) * reducedSource1943 x := by
  norm_num [numericRow1943, reducedSource1943, Integer.Sparse.eval, Sparse.eval, nodeValue2353, nodeValue2355, nodeValue2356, nodeValue2362, nodeValue2590, nodeValue3732, nodeValue4092]

noncomputable def reducedSource1944 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4339 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4721 x + ((1 : ℝ) * Sparse.eval nodeValue4726 x + ((1 : ℝ) * Sparse.eval nodeValue4744 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4937 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5032 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((1 : ℝ) * Sparse.eval nodeValue5125 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))))))))))

def numericRow1944 : Integer.Sparse Master := [(Sum.inl 0, 152), (Sum.inl 5, -40), (Sum.inl 6, -5), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -30), (Sum.inr 915, -4320), (Sum.inr 916, -4320), (Sum.inr 917, -4320), (Sum.inr 932, -4320), (Sum.inr 1035, -4320), (Sum.inr 1632, -4320), (Sum.inr 1633, -4320), (Sum.inr 1634, -4320), (Sum.inr 1645, -4320), (Sum.inr 1681, -4320), (Sum.inr 1875, -4320), (Sum.inr 1880, -4320), (Sum.inr 1905, -4320), (Sum.inr 1917, -4320), (Sum.inr 1924, -4320), (Sum.inr 1938, -4320), (Sum.inr 2109, -4320), (Sum.inr 2261, -4320), (Sum.inr 2328, -4320), (Sum.inr 2329, -4320), (Sum.inr 2341, -4320), (Sum.inr 2424, -4320), (Sum.inr 2431, -4320), (Sum.inr 2477, -4320), (Sum.inr 2536, -4320), (Sum.inr 2539, -4320), (Sum.inr 2589, -4320), (Sum.inr 2590, -8640), (Sum.inr 2672, -4320), (Sum.inr 2764, -4320), (Sum.inr 2765, -4320), (Sum.inr 3370, -4320), (Sum.inr 3372, -4320), (Sum.inr 3391, -4320), (Sum.inr 3401, -4320), (Sum.inr 3402, -4320), (Sum.inr 3417, -4320), (Sum.inr 3440, -4320), (Sum.inr 3444, -4320), (Sum.inr 3453, -4320), (Sum.inr 3563, -4320), (Sum.inr 3564, -8640), (Sum.inr 3581, -4320), (Sum.inr 3582, -4320), (Sum.inr 3613, -4320), (Sum.inr 3614, -4320), (Sum.inr 3787, -4320), (Sum.inr 3790, -4320), (Sum.inr 3804, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3815, -4320), (Sum.inr 3913, -4320), (Sum.inr 4010, -4320)]

theorem reindexCheck1944 : Integer.Sparse.reindex keyMap MixedData.row1944 = numericRow1944 := by decide +kernel

theorem numericCheck1944 (x : Master → ℝ) : Integer.Sparse.eval numericRow1944 x =
    (17280 : ℝ) * reducedSource1944 x := by
  norm_num [numericRow1944, reducedSource1944, Integer.Sparse.eval, Sparse.eval, nodeValue4337, nodeValue4338, nodeValue4339, nodeValue4354, nodeValue4452, nodeValue4721, nodeValue4726, nodeValue4744, nodeValue4868, nodeValue4936, nodeValue4937, nodeValue4949, nodeValue5032, nodeValue5038, nodeValue5070, nodeValue5123, nodeValue5125, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5176, nodeValue5228, nodeValue5290, nodeValue5291, nodeValue5401, nodeValue5404, nodeValue5411, nodeValue5451, nodeValue5485]
  ring

noncomputable def reducedSource1945 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4527 x + ((2 : ℝ) * Sparse.eval nodeValue4530 x + ((1 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((2 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + 0))))))))))))))))))))

def numericRow1945 : Integer.Sparse Master := [(Sum.inr 1240, -1), (Sum.inr 2429, -1), (Sum.inr 2432, -2), (Sum.inr 2556, -2), (Sum.inr 2589, -1), (Sum.inr 2723, -2), (Sum.inr 3299, -1), (Sum.inr 3455, -1), (Sum.inr 3456, -2), (Sum.inr 3521, -2), (Sum.inr 3544, -2), (Sum.inr 3563, -1), (Sum.inr 3721, -1), (Sum.inr 3836, -1), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 4527, 4), (Sum.inr 4530, 8), (Sum.inr 4542, 4), (Sum.inr 4956, 4), (Sum.inr 4958, 8), (Sum.inr 4964, 4), (Sum.inr 5128, 8), (Sum.inr 5145, 8)]

theorem reindexCheck1945 : Integer.Sparse.reindex keyMap MixedData.row1945 = numericRow1945 := by decide +kernel

theorem numericCheck1945 (x : Master → ℝ) : Integer.Sparse.eval numericRow1945 x =
    (4 : ℝ) * reducedSource1945 x := by
  norm_num [numericRow1945, reducedSource1945, Integer.Sparse.eval, Sparse.eval, nodeValue4527, nodeValue4530, nodeValue4542, nodeValue4606, nodeValue4956, nodeValue4958, nodeValue4964, nodeValue5037, nodeValue5039, nodeValue5104, nodeValue5128, nodeValue5130, nodeValue5137, nodeValue5145, nodeValue5162, nodeValue5259, nodeValue5273, nodeValue5380, nodeValue5396, nodeValue5424, nodeValue5427]
  ring

noncomputable def reducedSource1946 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3257 x + ((2 : ℝ) * Sparse.eval nodeValue3261 x + ((1 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((2 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3511 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3521 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((2 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3836 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + 0))))))))))))))))))))

def numericRow1946 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3299, 1), (Sum.inr 3455, 1), (Sum.inr 3456, 2), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3519, 2), (Sum.inr 3521, 2), (Sum.inr 3544, 2), (Sum.inr 3554, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3836, 1), (Sum.inr 3843, 2)]

theorem reindexCheck1946 : Integer.Sparse.reindex keyMap MixedData.row1946 = numericRow1946 := by decide +kernel

theorem numericCheck1946 (x : Master → ℝ) : Integer.Sparse.eval numericRow1946 x =
    (1 : ℝ) * reducedSource1946 x := by
  norm_num [numericRow1946, reducedSource1946, Integer.Sparse.eval, Sparse.eval, nodeValue3255, nodeValue3257, nodeValue3261, nodeValue3299, nodeValue3455, nodeValue3456, nodeValue3483, nodeValue3510, nodeValue3511, nodeValue3519, nodeValue3520, nodeValue3521, nodeValue3544, nodeValue3546, nodeValue3554, nodeValue3562, nodeValue3563, nodeValue3798, nodeValue3836, nodeValue3843, nodeValue3844]

noncomputable def reducedSource1947 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2349 x + ((2 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue2354 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1947 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2351, 2), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1947 : Integer.Sparse.reindex keyMap MixedData.row1947 = numericRow1947 := by decide +kernel

theorem numericCheck1947 (x : Master → ℝ) : Integer.Sparse.eval numericRow1947 x =
    (1 : ℝ) * reducedSource1947 x := by
  norm_num [numericRow1947, reducedSource1947, Integer.Sparse.eval, Sparse.eval, nodeValue2349, nodeValue2351, nodeValue2354, nodeValue2556, nodeValue3721, nodeValue4091]

noncomputable def reducedSource1948 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4322 x + ((2 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((2 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((2 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))

def numericRow1948 : Integer.Sparse Master := [(Sum.inl 0, 322), (Sum.inl 6, 5), (Sum.inl 2, -45), (Sum.inl 7, -80), (Sum.inl 3, -240), (Sum.inl 4, -160), (Sum.inr 900, -4320), (Sum.inr 901, -8640), (Sum.inr 922, -4320), (Sum.inr 980, -4320), (Sum.inr 1588, -4320), (Sum.inr 1589, -8640), (Sum.inr 1616, -4320), (Sum.inr 1673, -4320), (Sum.inr 2317, -4320), (Sum.inr 2318, -8640), (Sum.inr 2332, -4320), (Sum.inr 2371, -4320), (Sum.inr 2372, -8640), (Sum.inr 2383, -4320), (Sum.inr 2482, -8640), (Sum.inr 2553, -8640), (Sum.inr 2561, -8640), (Sum.inr 2721, -4320), (Sum.inr 2723, -8640), (Sum.inr 3335, -4320), (Sum.inr 3336, -8640), (Sum.inr 3352, -4320), (Sum.inr 3399, -4320), (Sum.inr 3400, -8640), (Sum.inr 3410, -4320), (Sum.inr 3468, -8640), (Sum.inr 3514, -8640), (Sum.inr 3522, -8640), (Sum.inr 3532, -4320), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3607, -8640), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 4046, -4320), (Sum.inr 4047, -8640)]

theorem reindexCheck1948 : Integer.Sparse.reindex keyMap MixedData.row1948 = numericRow1948 := by decide +kernel

theorem numericCheck1948 (x : Master → ℝ) : Integer.Sparse.eval numericRow1948 x =
    (17280 : ℝ) * reducedSource1948 x := by
  norm_num [numericRow1948, reducedSource1948, Integer.Sparse.eval, Sparse.eval, nodeValue4322, nodeValue4323, nodeValue4344, nodeValue4399, nodeValue4927, nodeValue4928, nodeValue4941, nodeValue4986, nodeValue4987, nodeValue4998, nodeValue5075, nodeValue5134, nodeValue5141, nodeValue5167, nodeValue5169, nodeValue5257, nodeValue5259, nodeValue5460, nodeValue5469, nodeValue5482, nodeValue5483]
  ring

noncomputable def reducedSource1949 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + 0)))))))))))))))))))))))))))))

def numericRow1949 : Integer.Sparse Master := [(Sum.inr 1236, -1), (Sum.inr 2425, -1), (Sum.inr 2428, -1), (Sum.inr 2431, -1), (Sum.inr 2482, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2722, -1), (Sum.inr 2739, -1), (Sum.inr 3293, -1), (Sum.inr 3449, -1), (Sum.inr 3450, -1), (Sum.inr 3453, -1), (Sum.inr 3468, -1), (Sum.inr 3522, -1), (Sum.inr 3533, -1), (Sum.inr 3534, -1), (Sum.inr 3564, -1), (Sum.inr 3719, -1), (Sum.inr 3795, -1), (Sum.inr 3837, -2), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 4528, 4), (Sum.inr 4529, 4), (Sum.inr 4533, 4), (Sum.inr 4545, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4963, 4), (Sum.inr 5129, 4), (Sum.inr 5138, 4), (Sum.inr 5144, 4), (Sum.inr 5160, 4)]

theorem reindexCheck1949 : Integer.Sparse.reindex keyMap MixedData.row1949 = numericRow1949 := by decide +kernel

theorem numericCheck1949 (x : Master → ℝ) : Integer.Sparse.eval numericRow1949 x =
    (4 : ℝ) * reducedSource1949 x := by
  norm_num [numericRow1949, reducedSource1949, Integer.Sparse.eval, Sparse.eval, nodeValue4528, nodeValue4529, nodeValue4533, nodeValue4545, nodeValue4602, nodeValue4954, nodeValue4955, nodeValue4957, nodeValue4963, nodeValue5033, nodeValue5036, nodeValue5038, nodeValue5075, nodeValue5101, nodeValue5127, nodeValue5129, nodeValue5135, nodeValue5138, nodeValue5141, nodeValue5144, nodeValue5160, nodeValue5163, nodeValue5258, nodeValue5271, nodeValue5274, nodeValue5378, nodeValue5394, nodeValue5409, nodeValue5423, nodeValue5424]
  ring

noncomputable def reducedSource1950 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3449 x + ((1 : ℝ) * Sparse.eval nodeValue3450 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + 0)))))))))))))))))))))))))))))

def numericRow1950 : Integer.Sparse Master := [(Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3267, 1), (Sum.inr 3293, 1), (Sum.inr 3449, 1), (Sum.inr 3450, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3468, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3522, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3553, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3564, 1), (Sum.inr 3795, 1), (Sum.inr 3837, 1), (Sum.inr 3838, 1)]

theorem reindexCheck1950 : Integer.Sparse.reindex keyMap MixedData.row1950 = numericRow1950 := by decide +kernel

theorem numericCheck1950 (x : Master → ℝ) : Integer.Sparse.eval numericRow1950 x =
    (1 : ℝ) * reducedSource1950 x := by
  norm_num [numericRow1950, reducedSource1950, Integer.Sparse.eval, Sparse.eval, nodeValue3258, nodeValue3259, nodeValue3260, nodeValue3267, nodeValue3293, nodeValue3449, nodeValue3450, nodeValue3452, nodeValue3453, nodeValue3468, nodeValue3470, nodeValue3508, nodeValue3509, nodeValue3513, nodeValue3515, nodeValue3516, nodeValue3517, nodeValue3522, nodeValue3533, nodeValue3534, nodeValue3547, nodeValue3553, nodeValue3557, nodeValue3558, nodeValue3564, nodeValue3793, nodeValue3795, nodeValue3807, nodeValue3837, nodeValue3838]

noncomputable def reducedSource1951 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1951 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2348, 1), (Sum.inr 2350, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1951 : Integer.Sparse.reindex keyMap MixedData.row1951 = numericRow1951 := by decide +kernel

theorem numericCheck1951 (x : Master → ℝ) : Integer.Sparse.eval numericRow1951 x =
    (1 : ℝ) * reducedSource1951 x := by
  norm_num [numericRow1951, reducedSource1951, Integer.Sparse.eval, Sparse.eval, nodeValue2347, nodeValue2348, nodeValue2350, nodeValue2353, nodeValue2553, nodeValue3719, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
