import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
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

noncomputable def reducedSource1808 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2799 x + ((2 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1808 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 2802, 2), (Sum.inr 2818, 1), (Sum.inr 2868, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1808 : Integer.Sparse.reindex keyMap MixedData.row1808 = numericRow1808 := by decide +kernel

theorem numericCheck1808 (x : Master → ℝ) : Integer.Sparse.eval numericRow1808 x =
    (1 : ℝ) * reducedSource1808 x := by
  norm_num [numericRow1808, reducedSource1808, Integer.Sparse.eval, Sparse.eval, nodeValue2799, nodeValue2802, nodeValue2818, nodeValue2868, nodeValue3694, nodeValue4091]

noncomputable def reducedSource1809 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2849 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1809 : Integer.Sparse Master := [(Sum.inr 1322, 1), (Sum.inr 2818, 1), (Sum.inr 2849, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 2), (Sum.inr 4091, -1)]

theorem reindexCheck1809 : Integer.Sparse.reindex keyMap MixedData.row1809 = numericRow1809 := by decide +kernel

theorem numericCheck1809 (x : Master → ℝ) : Integer.Sparse.eval numericRow1809 x =
    (1 : ℝ) * reducedSource1809 x := by
  norm_num [numericRow1809, reducedSource1809, Integer.Sparse.eval, Sparse.eval, nodeValue1322, nodeValue2818, nodeValue2849, nodeValue2868, nodeValue2884, nodeValue4091]

noncomputable def reducedSource1810 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue2812 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1810 : Integer.Sparse Master := [(Sum.inr 1819, 1), (Sum.inr 2812, 2), (Sum.inr 2821, 1), (Sum.inr 2888, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1810 : Integer.Sparse.reindex keyMap MixedData.row1810 = numericRow1810 := by decide +kernel

theorem numericCheck1810 (x : Master → ℝ) : Integer.Sparse.eval numericRow1810 x =
    (1 : ℝ) * reducedSource1810 x := by
  norm_num [numericRow1810, reducedSource1810, Integer.Sparse.eval, Sparse.eval, nodeValue1819, nodeValue2812, nodeValue2821, nodeValue2888, nodeValue3397, nodeValue4084]

noncomputable def reducedSource1811 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4965 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5044 x + ((2 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))))))))))

def numericRow1811 : Integer.Sparse Master := [(Sum.inr 2345, -1), (Sum.inr 2519, -1), (Sum.inr 2813, -2), (Sum.inr 2820, -1), (Sum.inr 2881, -2), (Sum.inr 3054, -1), (Sum.inr 3423, -1), (Sum.inr 3486, -1), (Sum.inr 3595, -2), (Sum.inr 3596, -1), (Sum.inr 3624, -2), (Sum.inr 3626, -1), (Sum.inr 3705, -2), (Sum.inr 3767, -2), (Sum.inr 3963, -2), (Sum.inr 4372, 8), (Sum.inr 4373, 4), (Sum.inr 4374, 4), (Sum.inr 4480, 4), (Sum.inr 4944, 8), (Sum.inr 4965, 8), (Sum.inr 5044, 8), (Sum.inr 5090, 8), (Sum.inr 5199, 8), (Sum.inr 5201, 4), (Sum.inr 5300, 4)]

theorem reindexCheck1811 : Integer.Sparse.reindex keyMap MixedData.row1811 = numericRow1811 := by decide +kernel

theorem numericCheck1811 (x : Master → ℝ) : Integer.Sparse.eval numericRow1811 x =
    (4 : ℝ) * reducedSource1811 x := by
  norm_num [numericRow1811, reducedSource1811, Integer.Sparse.eval, Sparse.eval, nodeValue4372, nodeValue4373, nodeValue4374, nodeValue4480, nodeValue4944, nodeValue4953, nodeValue4965, nodeValue4977, nodeValue4979, nodeValue5044, nodeValue5090, nodeValue5109, nodeValue5199, nodeValue5201, nodeValue5204, nodeValue5300, nodeValue5302, nodeValue5368, nodeValue5371, nodeValue5413, nodeValue5475]; ring

noncomputable def reducedSource1812 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3474 x + ((2 : ℝ) * Sparse.eval nodeValue3475 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((2 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((2 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((2 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + 0))))))))))))))))))))

def numericRow1812 : Integer.Sparse Master := [(Sum.inr 1734, 2), (Sum.inr 1735, 1), (Sum.inr 1740, 1), (Sum.inr 1748, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3474, 2), (Sum.inr 3475, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3584, 1), (Sum.inr 3595, 2), (Sum.inr 3596, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3767, 2), (Sum.inr 3963, 1)]

theorem reindexCheck1812 : Integer.Sparse.reindex keyMap MixedData.row1812 = numericRow1812 := by decide +kernel

theorem numericCheck1812 (x : Master → ℝ) : Integer.Sparse.eval numericRow1812 x =
    (1 : ℝ) * reducedSource1812 x := by
  norm_num [numericRow1812, reducedSource1812, Integer.Sparse.eval, Sparse.eval, nodeValue1734, nodeValue1735, nodeValue1740, nodeValue1748, nodeValue3413, nodeValue3423, nodeValue3474, nodeValue3475, nodeValue3480, nodeValue3486, nodeValue3578, nodeValue3579, nodeValue3584, nodeValue3595, nodeValue3596, nodeValue3624, nodeValue3626, nodeValue3767, nodeValue3775, nodeValue3817, nodeValue3963]

noncomputable def reducedSource1813 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2813 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue3707 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1813 : Integer.Sparse Master := [(Sum.inr 2345, 1), (Sum.inr 2813, 2), (Sum.inr 2820, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1813 : Integer.Sparse.reindex keyMap MixedData.row1813 = numericRow1813 := by decide +kernel

theorem numericCheck1813 (x : Master → ℝ) : Integer.Sparse.eval numericRow1813 x =
    (1 : ℝ) * reducedSource1813 x := by
  norm_num [numericRow1813, reducedSource1813, Integer.Sparse.eval, Sparse.eval, nodeValue2345, nodeValue2813, nodeValue2820, nodeValue2889, nodeValue3707, nodeValue4092]

noncomputable def reducedSource1814 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue3679 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3695 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1814 : Integer.Sparse Master := [(Sum.inr 2533, 1), (Sum.inr 3679, 1), (Sum.inr 3681, 1), (Sum.inr 3695, 1), (Sum.inr 3795, 1), (Sum.inr 3832, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1814 : Integer.Sparse.reindex keyMap MixedData.row1814 = numericRow1814 := by decide +kernel

theorem numericCheck1814 (x : Master → ℝ) : Integer.Sparse.eval numericRow1814 x =
    (1 : ℝ) * reducedSource1814 x := by
  norm_num [numericRow1814, reducedSource1814, Integer.Sparse.eval, Sparse.eval, nodeValue2533, nodeValue3679, nodeValue3681, nodeValue3695, nodeValue3795, nodeValue3832, nodeValue4088]

noncomputable def reducedSource1815 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4929 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((1 : ℝ) * Sparse.eval nodeValue4959 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + 0)))))))))))))))))))))))))))))

def numericRow1815 : Integer.Sparse Master := [(Sum.inr 1246, -1), (Sum.inr 2334, -1), (Sum.inr 2428, -1), (Sum.inr 2434, -1), (Sum.inr 2482, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2743, -1), (Sum.inr 3301, -1), (Sum.inr 3411, -1), (Sum.inr 3450, -1), (Sum.inr 3457, -1), (Sum.inr 3468, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3548, -1), (Sum.inr 3564, -1), (Sum.inr 3689, -1), (Sum.inr 3693, -1), (Sum.inr 3757, -1), (Sum.inr 3770, -1), (Sum.inr 3845, -2), (Sum.inr 4533, 4), (Sum.inr 4534, 4), (Sum.inr 4535, 4), (Sum.inr 4556, 4), (Sum.inr 4934, 4), (Sum.inr 4955, 4), (Sum.inr 4956, 4), (Sum.inr 4959, 4), (Sum.inr 4966, 4), (Sum.inr 5112, 4), (Sum.inr 5139, 4), (Sum.inr 5164, 4)]

theorem reindexCheck1815 : Integer.Sparse.reindex keyMap MixedData.row1815 = numericRow1815 := by decide +kernel

theorem numericCheck1815 (x : Master → ℝ) : Integer.Sparse.eval numericRow1815 x =
    (4 : ℝ) * reducedSource1815 x := by
  norm_num [numericRow1815, reducedSource1815, Integer.Sparse.eval, Sparse.eval, nodeValue4533, nodeValue4534, nodeValue4535, nodeValue4556, nodeValue4612, nodeValue4929, nodeValue4934, nodeValue4943, nodeValue4955, nodeValue4956, nodeValue4959, nodeValue4966, nodeValue4972, nodeValue5036, nodeValue5075, nodeValue5111, nodeValue5112, nodeValue5134, nodeValue5135, nodeValue5139, nodeValue5141, nodeValue5163, nodeValue5164, nodeValue5274, nodeValue5275, nodeValue5351, nodeValue5355, nodeValue5367, nodeValue5409, nodeValue5428]; ring

noncomputable def reducedSource1816 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2358 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2823 x + ((1 : ℝ) * Sparse.eval nodeValue2828 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((1 : ℝ) * Sparse.eval nodeValue2903 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((1 : ℝ) * Sparse.eval nodeValue2961 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3728 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3941 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + 0)))))))))))))))))))))))))))))

def numericRow1816 : Integer.Sparse Master := [(Sum.inl 0, -99), (Sum.inl 5, -80), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, 130), (Sum.inr 1117, 1080), (Sum.inr 1119, 1080), (Sum.inr 1120, 1080), (Sum.inr 1141, 1080), (Sum.inr 2349, 1080), (Sum.inr 2352, 1080), (Sum.inr 2618, 1080), (Sum.inr 2801, 1080), (Sum.inr 2802, 1080), (Sum.inr 2819, 1080), (Sum.inr 2898, 1080), (Sum.inr 2955, 1080)]

theorem reindexCheck1816 : Integer.Sparse.reindex keyMap MixedData.row1816 = numericRow1816 := by decide +kernel

theorem numericCheck1816 (x : Master → ℝ) : Integer.Sparse.eval numericRow1816 x =
    (1080 : ℝ) * reducedSource1816 x := by
  norm_num [numericRow1816, reducedSource1816, Integer.Sparse.eval, Sparse.eval, nodeValue1117, nodeValue1119, nodeValue1120, nodeValue1141, nodeValue1274, nodeValue2349, nodeValue2352, nodeValue2358, nodeValue2618, nodeValue2801, nodeValue2802, nodeValue2819, nodeValue2823, nodeValue2828, nodeValue2898, nodeValue2903, nodeValue2934, nodeValue2937, nodeValue2939, nodeValue2943, nodeValue2955, nodeValue2961, nodeValue3006, nodeValue3110, nodeValue3112, nodeValue3728, nodeValue3937, nodeValue3941, nodeValue4003, nodeValue4035]; ring

noncomputable def reducedSource1817 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3271 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3450 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((1 : ℝ) * Sparse.eval nodeValue3512 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + 0)))))))))))))))))))))))))))))

def numericRow1817 : Integer.Sparse Master := [(Sum.inr 3267, 1), (Sum.inr 3268, 1), (Sum.inr 3271, 1), (Sum.inr 3272, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3450, 1), (Sum.inr 3457, 1), (Sum.inr 3468, 1), (Sum.inr 3508, 1), (Sum.inr 3510, 1), (Sum.inr 3512, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3548, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3757, 1), (Sum.inr 3770, 1), (Sum.inr 3845, 1)]

theorem reindexCheck1817 : Integer.Sparse.reindex keyMap MixedData.row1817 = numericRow1817 := by decide +kernel

theorem numericCheck1817 (x : Master → ℝ) : Integer.Sparse.eval numericRow1817 x =
    (1 : ℝ) * reducedSource1817 x := by
  norm_num [numericRow1817, reducedSource1817, Integer.Sparse.eval, Sparse.eval, nodeValue3267, nodeValue3268, nodeValue3271, nodeValue3272, nodeValue3301, nodeValue3403, nodeValue3411, nodeValue3415, nodeValue3450, nodeValue3457, nodeValue3468, nodeValue3485, nodeValue3508, nodeValue3510, nodeValue3512, nodeValue3514, nodeValue3515, nodeValue3522, nodeValue3523, nodeValue3547, nodeValue3548, nodeValue3555, nodeValue3556, nodeValue3564, nodeValue3565, nodeValue3757, nodeValue3766, nodeValue3770, nodeValue3807, nodeValue3845]

noncomputable def reducedSource1818 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1818 : Integer.Sparse Master := [(Sum.inr 2325, 1), (Sum.inr 2348, 1), (Sum.inr 2352, 1), (Sum.inr 2356, 1), (Sum.inr 2561, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1818 : Integer.Sparse.reindex keyMap MixedData.row1818 = numericRow1818 := by decide +kernel

theorem numericCheck1818 (x : Master → ℝ) : Integer.Sparse.eval numericRow1818 x =
    (1 : ℝ) * reducedSource1818 x := by
  norm_num [numericRow1818, reducedSource1818, Integer.Sparse.eval, Sparse.eval, nodeValue2325, nodeValue2348, nodeValue2352, nodeValue2356, nodeValue2561, nodeValue3693, nodeValue4092]

noncomputable def reducedSource1819 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1819 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 2348, 1), (Sum.inr 2428, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1819 : Integer.Sparse.reindex keyMap MixedData.row1819 = numericRow1819 := by decide +kernel

theorem numericCheck1819 (x : Master → ℝ) : Integer.Sparse.eval numericRow1819 x =
    (1 : ℝ) * reducedSource1819 x := by
  norm_num [numericRow1819, reducedSource1819, Integer.Sparse.eval, Sparse.eval, nodeValue1149, nodeValue2348, nodeValue2428, nodeValue2553, nodeValue2554, nodeValue2561, nodeValue4092]

noncomputable def reducedSource1820 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2319 x + ((1 : ℝ) * Sparse.eval nodeValue2524 x + ((1 : ℝ) * Sparse.eval nodeValue2525 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1820 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 2), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1820 : Integer.Sparse.reindex keyMap MixedData.row1820 = numericRow1820 := by decide +kernel

theorem numericCheck1820 (x : Master → ℝ) : Integer.Sparse.eval numericRow1820 x =
    (1 : ℝ) * reducedSource1820 x := by
  norm_num [numericRow1820, reducedSource1820, Integer.Sparse.eval, Sparse.eval, nodeValue2319, nodeValue2524, nodeValue2525, nodeValue2561, nodeValue3689, nodeValue4092]

noncomputable def reducedSource1821 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue2525 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1821 : Integer.Sparse Master := [(Sum.inr 1160, 1), (Sum.inr 2356, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 1), (Sum.inr 2590, 1), (Sum.inr 2591, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1821 : Integer.Sparse.reindex keyMap MixedData.row1821 = numericRow1821 := by decide +kernel

theorem numericCheck1821 (x : Master → ℝ) : Integer.Sparse.eval numericRow1821 x =
    (1 : ℝ) * reducedSource1821 x := by
  norm_num [numericRow1821, reducedSource1821, Integer.Sparse.eval, Sparse.eval, nodeValue1160, nodeValue2356, nodeValue2525, nodeValue2561, nodeValue2590, nodeValue2591, nodeValue4092]

noncomputable def reducedSource1822 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4325 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4902 x + ((1 : ℝ) * Sparse.eval nodeValue4907 x + ((1 : ℝ) * Sparse.eval nodeValue4913 x + ((1 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue5003 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

def numericRow1822 : Integer.Sparse Master := [(Sum.inl 0, 199), (Sum.inl 6, -10), (Sum.inl 2, 80), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, 75), (Sum.inr 901, -4320), (Sum.inr 902, -4320), (Sum.inr 903, -4320), (Sum.inr 927, -4320), (Sum.inr 985, -4320), (Sum.inr 1589, -4320), (Sum.inr 1590, -4320), (Sum.inr 1591, -4320), (Sum.inr 1618, -4320), (Sum.inr 1675, -4320), (Sum.inr 1760, -4320), (Sum.inr 1766, -4320), (Sum.inr 1773, -4320), (Sum.inr 1836, -4320), (Sum.inr 1841, -4320), (Sum.inr 1850, -4320), (Sum.inr 2022, -4320), (Sum.inr 2203, -4320), (Sum.inr 2295, -4320), (Sum.inr 2300, -4320), (Sum.inr 2306, -4320), (Sum.inr 2318, -4320), (Sum.inr 2337, -4320), (Sum.inr 2372, -4320), (Sum.inr 2388, -4320), (Sum.inr 2428, -4320), (Sum.inr 2452, -4320), (Sum.inr 2482, -4320), (Sum.inr 2553, -4320), (Sum.inr 2556, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 3315, -4320), (Sum.inr 3318, -4320), (Sum.inr 3325, -4320), (Sum.inr 3336, -4320), (Sum.inr 3354, -4320), (Sum.inr 3400, -4320), (Sum.inr 3412, -4320), (Sum.inr 3433, -4320), (Sum.inr 3450, -4320), (Sum.inr 3468, -4320), (Sum.inr 3514, -4320), (Sum.inr 3521, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3705, -4320), (Sum.inr 3764, -4320), (Sum.inr 3767, -4320), (Sum.inr 3773, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320)]

theorem reindexCheck1822 : Integer.Sparse.reindex keyMap MixedData.row1822 = numericRow1822 := by decide +kernel

theorem numericCheck1822 (x : Master → ℝ) : Integer.Sparse.eval numericRow1822 x =
    (17280 : ℝ) * reducedSource1822 x := by
  norm_num [numericRow1822, reducedSource1822, Integer.Sparse.eval, Sparse.eval, nodeValue4323, nodeValue4324, nodeValue4325, nodeValue4349, nodeValue4404, nodeValue4631, nodeValue4637, nodeValue4644, nodeValue4804, nodeValue4902, nodeValue4907, nodeValue4913, nodeValue4928, nodeValue4946, nodeValue4987, nodeValue5003, nodeValue5036, nodeValue5050, nodeValue5075, nodeValue5134, nodeValue5137, nodeValue5168, nodeValue5169, nodeValue5258, nodeValue5259, nodeValue5352, nodeValue5356, nodeValue5368, nodeValue5434, nodeValue5483]; ring

noncomputable def reducedSource1823 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2541 x + ((1 : ℝ) * Sparse.eval nodeValue3646 x + ((2 : ℝ) * Sparse.eval nodeValue3650 x + ((2 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))

def numericRow1823 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 3646, 1), (Sum.inr 3757, 2), (Sum.inr 4088, -1)]

theorem reindexCheck1823 : Integer.Sparse.reindex keyMap MixedData.row1823 = numericRow1823 := by decide +kernel

theorem numericCheck1823 (x : Master → ℝ) : Integer.Sparse.eval numericRow1823 x =
    (1 : ℝ) * reducedSource1823 x := by
  norm_num [numericRow1823, reducedSource1823, Integer.Sparse.eval, Sparse.eval, nodeValue2541, nodeValue3646, nodeValue3650, nodeValue3757, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
