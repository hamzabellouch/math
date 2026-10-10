import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
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

noncomputable def reducedSource1776 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((2 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1776 : Integer.Sparse Master := [(Sum.inr 1152, 1), (Sum.inr 2351, 1), (Sum.inr 2432, 1), (Sum.inr 2556, 2), (Sum.inr 4091, -1)]

theorem reindexCheck1776 : Integer.Sparse.reindex keyMap MixedData.row1776 = numericRow1776 := by decide +kernel

theorem numericCheck1776 (x : Master → ℝ) : Integer.Sparse.eval numericRow1776 x =
    (1 : ℝ) * reducedSource1776 x := by
  norm_num [numericRow1776, reducedSource1776, Integer.Sparse.eval, Sparse.eval, nodeValue1152, nodeValue2351, nodeValue2432, nodeValue2546, nodeValue2556, nodeValue4091]

noncomputable def reducedSource1777 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2002 x + ((1 : ℝ) * Sparse.eval nodeValue2044 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1777 : Integer.Sparse Master := [(Sum.inr 1997, 2), (Sum.inr 2002, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1777 : Integer.Sparse.reindex keyMap MixedData.row1777 = numericRow1777 := by decide +kernel

theorem numericCheck1777 (x : Master → ℝ) : Integer.Sparse.eval numericRow1777 x =
    (1 : ℝ) * reducedSource1777 x := by
  norm_num [numericRow1777, reducedSource1777, Integer.Sparse.eval, Sparse.eval, nodeValue1997, nodeValue2002, nodeValue2044, nodeValue2225, nodeValue3520, nodeValue4082]

noncomputable def reducedSource1778 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3616 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1778 : Integer.Sparse Master := [(Sum.inr 3482, 1), (Sum.inr 3522, 2), (Sum.inr 3542, 1), (Sum.inr 3616, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1778 : Integer.Sparse.reindex keyMap MixedData.row1778 = numericRow1778 := by decide +kernel

theorem numericCheck1778 (x : Master → ℝ) : Integer.Sparse.eval numericRow1778 x =
    (1 : ℝ) * reducedSource1778 x := by
  norm_num [numericRow1778, reducedSource1778, Integer.Sparse.eval, Sparse.eval, nodeValue3482, nodeValue3520, nodeValue3522, nodeValue3542, nodeValue3616, nodeValue4082]

noncomputable def reducedSource1779 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3683 x + ((1 : ℝ) * Sparse.eval nodeValue3696 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))))

def numericRow1779 : Integer.Sparse Master := [(Sum.inr 2905, 1), (Sum.inr 3680, 1), (Sum.inr 3683, 1), (Sum.inr 3696, 1), (Sum.inr 3796, 1), (Sum.inr 3873, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1779 : Integer.Sparse.reindex keyMap MixedData.row1779 = numericRow1779 := by decide +kernel

theorem numericCheck1779 (x : Master → ℝ) : Integer.Sparse.eval numericRow1779 x =
    (1 : ℝ) * reducedSource1779 x := by
  norm_num [numericRow1779, reducedSource1779, Integer.Sparse.eval, Sparse.eval, nodeValue2905, nodeValue3680, nodeValue3683, nodeValue3696, nodeValue3796, nodeValue3873, nodeValue4090]

noncomputable def reducedSource1780 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5114 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

def numericRow1780 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 5, 20), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 290), (Sum.inr 1138, -1440), (Sum.inr 1143, -720), (Sum.inr 1145, -720), (Sum.inr 1812, -1440), (Sum.inr 1819, -720), (Sum.inr 2112, -720), (Sum.inr 2165, -1440), (Sum.inr 2167, -720), (Sum.inr 2169, -720), (Sum.inr 2287, -720), (Sum.inr 2815, -1440), (Sum.inr 2817, -1440), (Sum.inr 2820, -720), (Sum.inr 2896, -1440), (Sum.inr 2954, -1440), (Sum.inr 3270, -1440), (Sum.inr 3277, -720), (Sum.inr 3311, -720), (Sum.inr 3588, -1440), (Sum.inr 3591, -1440), (Sum.inr 3596, -720), (Sum.inr 3597, -1440), (Sum.inr 3603, -1440), (Sum.inr 3606, -1440), (Sum.inr 3608, -720), (Sum.inr 3614, -1440), (Sum.inr 3633, -720), (Sum.inr 3891, -1440), (Sum.inr 3893, -720), (Sum.inr 3907, -720)]

theorem reindexCheck1780 : Integer.Sparse.reindex keyMap MixedData.row1780 = numericRow1780 := by decide +kernel

theorem numericCheck1780 (x : Master → ℝ) : Integer.Sparse.eval numericRow1780 x =
    (2880 : ℝ) * reducedSource1780 x := by
  norm_num [numericRow1780, reducedSource1780, Integer.Sparse.eval, Sparse.eval, nodeValue4553, nodeValue4557, nodeValue4559, nodeValue4627, nodeValue4686, nodeValue4693, nodeValue4871, nodeValue4970, nodeValue4973, nodeValue4979, nodeValue5114, nodeValue5168, nodeValue5170, nodeValue5171, nodeValue5176, nodeValue5308, nodeValue5310, nodeValue5387, nodeValue5389, nodeValue5441, nodeValue5443]
  ring

noncomputable def reducedSource1781 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((2 : ℝ) * Sparse.eval nodeValue2815 x + ((2 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2896 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((1 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((2 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3740 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

def numericRow1781 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, -20), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -290), (Sum.inr 1138, 1440), (Sum.inr 1143, 720), (Sum.inr 1145, 720), (Sum.inr 1812, 1440), (Sum.inr 1819, 720), (Sum.inr 2112, 720), (Sum.inr 2815, 1440), (Sum.inr 2817, 1440), (Sum.inr 2820, 720), (Sum.inr 2896, 1440), (Sum.inr 2954, 1440)]

theorem reindexCheck1781 : Integer.Sparse.reindex keyMap MixedData.row1781 = numericRow1781 := by decide +kernel

theorem numericCheck1781 (x : Master → ℝ) : Integer.Sparse.eval numericRow1781 x =
    (720 : ℝ) * reducedSource1781 x := by
  norm_num [numericRow1781, reducedSource1781, Integer.Sparse.eval, Sparse.eval, nodeValue1138, nodeValue1143, nodeValue1145, nodeValue1311, nodeValue1812, nodeValue1819, nodeValue2112, nodeValue2815, nodeValue2817, nodeValue2820, nodeValue2896, nodeValue2954, nodeValue2963, nodeValue2965, nodeValue2968, nodeValue3121, nodeValue3124, nodeValue3739, nodeValue3740, nodeValue3889, nodeValue4037]
  ring

noncomputable def reducedSource1782 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5038 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

def numericRow1782 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 5, 4), (Sum.inl 2, -1), (Sum.inl 7, 16), (Sum.inl 3, 16), (Sum.inl 1, -32), (Sum.inr 932, -432), (Sum.inr 937, -216), (Sum.inr 939, -216), (Sum.inr 1049, -216), (Sum.inr 1681, -432), (Sum.inr 1683, -216), (Sum.inr 1694, -216), (Sum.inr 1738, -216), (Sum.inr 1807, -432), (Sum.inr 1818, -216), (Sum.inr 2109, -216), (Sum.inr 2151, -432), (Sum.inr 2168, -216), (Sum.inr 2261, -216), (Sum.inr 2341, -432), (Sum.inr 2345, -216), (Sum.inr 2431, -432), (Sum.inr 2434, -432), (Sum.inr 2488, -432), (Sum.inr 2590, -432), (Sum.inr 2765, -216), (Sum.inr 3417, -432), (Sum.inr 3423, -216), (Sum.inr 3453, -432), (Sum.inr 3457, -432), (Sum.inr 3478, -432), (Sum.inr 3564, -432), (Sum.inr 3582, -216), (Sum.inr 3613, -432), (Sum.inr 3615, -216), (Sum.inr 3632, -216), (Sum.inr 3892, -432), (Sum.inr 3894, -216), (Sum.inr 3913, -216)]

theorem reindexCheck1782 : Integer.Sparse.reindex keyMap MixedData.row1782 = numericRow1782 := by decide +kernel

theorem numericCheck1782 (x : Master → ℝ) : Integer.Sparse.eval numericRow1782 x =
    (864 : ℝ) * reducedSource1782 x := by
  norm_num [numericRow1782, reducedSource1782, Integer.Sparse.eval, Sparse.eval, nodeValue4354, nodeValue4359, nodeValue4361, nodeValue4466, nodeValue4681, nodeValue4692, nodeValue4868, nodeValue4949, nodeValue4953, nodeValue4972, nodeValue5038, nodeValue5080, nodeValue5163, nodeValue5172, nodeValue5174, nodeValue5291, nodeValue5294, nodeValue5388, nodeValue5390, nodeValue5442, nodeValue5451]
  ring

noncomputable def reducedSource1783 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((2 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((2 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2431 x + ((2 : ℝ) * Sparse.eval nodeValue2434 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((2 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

def numericRow1783 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 5, -4), (Sum.inl 2, 1), (Sum.inl 7, -16), (Sum.inl 3, -16), (Sum.inl 1, 32), (Sum.inr 932, 432), (Sum.inr 937, 216), (Sum.inr 939, 216), (Sum.inr 1049, 216), (Sum.inr 1807, 432), (Sum.inr 1818, 216), (Sum.inr 2109, 216), (Sum.inr 2341, 432), (Sum.inr 2345, 216), (Sum.inr 2431, 432), (Sum.inr 2434, 432), (Sum.inr 2488, 432), (Sum.inr 2590, 432), (Sum.inr 2765, 216)]

theorem reindexCheck1783 : Integer.Sparse.reindex keyMap MixedData.row1783 = numericRow1783 := by decide +kernel

theorem numericCheck1783 (x : Master → ℝ) : Integer.Sparse.eval numericRow1783 x =
    (216 : ℝ) * reducedSource1783 x := by
  norm_num [numericRow1783, reducedSource1783, Integer.Sparse.eval, Sparse.eval, nodeValue932, nodeValue937, nodeValue939, nodeValue1049, nodeValue1807, nodeValue1818, nodeValue2109, nodeValue2341, nodeValue2345, nodeValue2431, nodeValue2434, nodeValue2488, nodeValue2590, nodeValue2599, nodeValue2601, nodeValue2765, nodeValue2768, nodeValue3737, nodeValue3741, nodeValue3888, nodeValue4001]
  ring

noncomputable def reducedSource1784 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((4 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5110 x + ((2 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))))))))

def numericRow1784 : Integer.Sparse Master := [(Sum.inl 0, 39), (Sum.inl 5, -40), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 2028, -4320), (Sum.inr 2065, -2160), (Sum.inr 2115, -2160), (Sum.inr 2215, -4320), (Sum.inr 2218, -2160), (Sum.inr 2276, -2160), (Sum.inr 2488, -8640), (Sum.inr 2522, -4320), (Sum.inr 2561, -4320), (Sum.inr 2685, -4320), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3478, -8640), (Sum.inr 3522, -4320), (Sum.inr 3612, -4320), (Sum.inr 3614, -2160), (Sum.inr 3616, -2160), (Sum.inr 3631, -2160), (Sum.inr 5129, 17280), (Sum.inr 5140, 17280), (Sum.inr 5151, 17280), (Sum.inr 5175, 8640), (Sum.inr 5188, 17280), (Sum.inr 5206, 8640)]

theorem reindexCheck1784 : Integer.Sparse.reindex keyMap MixedData.row1784 = numericRow1784 := by decide +kernel

theorem numericCheck1784 (x : Master → ℝ) : Integer.Sparse.eval numericRow1784 x =
    (8640 : ℝ) * reducedSource1784 x := by
  norm_num [numericRow1784, reducedSource1784, Integer.Sparse.eval, Sparse.eval, nodeValue4810, nodeValue4845, nodeValue4846, nodeValue4874, nodeValue5080, nodeValue5110, nodeValue5111, nodeValue5129, nodeValue5140, nodeValue5141, nodeValue5151, nodeValue5152, nodeValue5175, nodeValue5176, nodeValue5177, nodeValue5188, nodeValue5206, nodeValue5207]
  ring

noncomputable def reducedSource1785 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2523 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2942 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

def numericRow1785 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 100), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 10), (Sum.inr 2488, 1440), (Sum.inr 2522, 720), (Sum.inr 2867, 1440), (Sum.inr 2888, 720), (Sum.inr 2889, 720), (Sum.inr 2916, 1440), (Sum.inr 2930, 1440), (Sum.inr 2931, 1440), (Sum.inr 2942, 1440), (Sum.inr 2967, 720)]

theorem reindexCheck1785 : Integer.Sparse.reindex keyMap MixedData.row1785 = numericRow1785 := by decide +kernel

theorem numericCheck1785 (x : Master → ℝ) : Integer.Sparse.eval numericRow1785 x =
    (720 : ℝ) * reducedSource1785 x := by
  norm_num [numericRow1785, reducedSource1785, Integer.Sparse.eval, Sparse.eval, nodeValue2488, nodeValue2522, nodeValue2523, nodeValue2604, nodeValue2867, nodeValue2888, nodeValue2889, nodeValue2916, nodeValue2930, nodeValue2931, nodeValue2942, nodeValue2943, nodeValue2967, nodeValue2969, nodeValue2990, nodeValue3005, nodeValue3006, nodeValue3095, nodeValue3187, nodeValue3206, nodeValue3216]
  ring

noncomputable def reducedSource1786 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((4 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((2 : ℝ) * Sparse.eval nodeValue5115 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))

def numericRow1786 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -35), (Sum.inr 1139, -540), (Sum.inr 1144, -540), (Sum.inr 2339, -1080), (Sum.inr 2345, -540), (Sum.inr 2818, -540), (Sum.inr 3274, -540), (Sum.inr 3276, -540), (Sum.inr 3312, -270), (Sum.inr 3420, -1080), (Sum.inr 3423, -540), (Sum.inr 3592, -540), (Sum.inr 3607, -1080), (Sum.inr 3615, -540), (Sum.inr 3616, -540), (Sum.inr 3894, -270), (Sum.inr 3898, -540)]

theorem reindexCheck1786 : Integer.Sparse.reindex keyMap MixedData.row1786 = numericRow1786 := by decide +kernel

theorem numericCheck1786 (x : Master → ℝ) : Integer.Sparse.eval numericRow1786 x =
    (1080 : ℝ) * reducedSource1786 x := by
  norm_num [numericRow1786, reducedSource1786, Integer.Sparse.eval, Sparse.eval, nodeValue4554, nodeValue4558, nodeValue4628, nodeValue4948, nodeValue4953, nodeValue4974, nodeValue5115, nodeValue5169, nodeValue5174, nodeValue5177, nodeValue5309, nodeValue5390, nodeValue5418, nodeValue5442]
  ring

noncomputable def reducedSource1787 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1139 x + ((2 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((4 : ℝ) * Sparse.eval nodeValue2339 x + ((2 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2818 x + ((2 : ℝ) * Sparse.eval nodeValue2897 x + ((4 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3741 x + ((2 : ℝ) * Sparse.eval nodeValue3933 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0)))))))))))))

def numericRow1787 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 5, -10), (Sum.inl 8, -40), (Sum.inl 1, 35), (Sum.inr 1139, 540), (Sum.inr 1144, 540), (Sum.inr 2339, 1080), (Sum.inr 2345, 540), (Sum.inr 2818, 540)]

theorem reindexCheck1787 : Integer.Sparse.reindex keyMap MixedData.row1787 = numericRow1787 := by decide +kernel

theorem numericCheck1787 (x : Master → ℝ) : Integer.Sparse.eval numericRow1787 x =
    (270 : ℝ) * reducedSource1787 x := by
  norm_num [numericRow1787, reducedSource1787, Integer.Sparse.eval, Sparse.eval, nodeValue1139, nodeValue1144, nodeValue1312, nodeValue2339, nodeValue2345, nodeValue2601, nodeValue2818, nodeValue2897, nodeValue2960, nodeValue2969, nodeValue3123, nodeValue3741, nodeValue3933, nodeValue4001]
  ring

noncomputable def reducedSource1788 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4355 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((4 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((2 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue5039 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))

def numericRow1788 : Integer.Sparse Master := [(Sum.inl 0, 9), (Sum.inl 5, 2), (Sum.inl 8, 8), (Sum.inl 1, 5), (Sum.inr 933, -144), (Sum.inr 938, -144), (Sum.inr 1050, -72), (Sum.inr 1691, -144), (Sum.inr 1693, -144), (Sum.inr 1751, -72), (Sum.inr 2334, -288), (Sum.inr 2342, -144), (Sum.inr 2344, -144), (Sum.inr 2432, -144), (Sum.inr 2489, -144), (Sum.inr 3411, -288), (Sum.inr 3421, -144), (Sum.inr 3422, -144), (Sum.inr 3456, -144), (Sum.inr 3482, -144), (Sum.inr 3607, -288), (Sum.inr 3608, -144), (Sum.inr 3627, -144), (Sum.inr 4042, -144), (Sum.inr 4043, -72)]

theorem reindexCheck1788 : Integer.Sparse.reindex keyMap MixedData.row1788 = numericRow1788 := by decide +kernel

theorem numericCheck1788 (x : Master → ℝ) : Integer.Sparse.eval numericRow1788 x =
    (288 : ℝ) * reducedSource1788 x := by
  norm_num [numericRow1788, reducedSource1788, Integer.Sparse.eval, Sparse.eval, nodeValue4355, nodeValue4360, nodeValue4467, nodeValue4943, nodeValue4950, nodeValue4952, nodeValue5039, nodeValue5081, nodeValue5169, nodeValue5171, nodeValue5293, nodeValue5465, nodeValue5466, nodeValue5487]
  ring

noncomputable def reducedSource1789 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue933 x + ((2 : ℝ) * Sparse.eval nodeValue938 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((4 : ℝ) * Sparse.eval nodeValue2334 x + ((2 : ℝ) * Sparse.eval nodeValue2342 x + ((2 : ℝ) * Sparse.eval nodeValue2344 x + ((2 : ℝ) * Sparse.eval nodeValue2432 x + ((2 : ℝ) * Sparse.eval nodeValue2489 x + ((4 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2598 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3934 x + ((2 : ℝ) * Sparse.eval nodeValue4000 x + 0)))))))))))))

def numericRow1789 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -2), (Sum.inl 8, -8), (Sum.inl 1, -5), (Sum.inr 933, 144), (Sum.inr 938, 144), (Sum.inr 1050, 72), (Sum.inr 2334, 288), (Sum.inr 2342, 144), (Sum.inr 2344, 144), (Sum.inr 2432, 144), (Sum.inr 2489, 144)]

theorem reindexCheck1789 : Integer.Sparse.reindex keyMap MixedData.row1789 = numericRow1789 := by decide +kernel

theorem numericCheck1789 (x : Master → ℝ) : Integer.Sparse.eval numericRow1789 x =
    (72 : ℝ) * reducedSource1789 x := by
  norm_num [numericRow1789, reducedSource1789, Integer.Sparse.eval, Sparse.eval, nodeValue933, nodeValue938, nodeValue1050, nodeValue2334, nodeValue2342, nodeValue2344, nodeValue2432, nodeValue2489, nodeValue2595, nodeValue2598, nodeValue2767, nodeValue3931, nodeValue3934, nodeValue4000]
  ring

noncomputable def reducedSource1790 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((4 : ℝ) * Sparse.eval nodeValue5081 x + ((4 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5130 x + ((4 : ℝ) * Sparse.eval nodeValue5141 x + ((4 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + 0)))))))))))

def numericRow1790 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 5, -30), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, -40), (Sum.inl 3, -80), (Sum.inl 1, 60), (Sum.inr 2029, -2160), (Sum.inr 2116, -1080), (Sum.inr 2225, -2160), (Sum.inr 2288, -1080), (Sum.inr 2489, -4320), (Sum.inr 2561, -4320), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3482, -4320), (Sum.inr 3522, -4320), (Sum.inr 3612, -4320), (Sum.inr 3614, -2160), (Sum.inr 3616, -1080), (Sum.inr 3631, -2160), (Sum.inr 5189, 8640)]

theorem reindexCheck1790 : Integer.Sparse.reindex keyMap MixedData.row1790 = numericRow1790 := by decide +kernel

theorem numericCheck1790 (x : Master → ℝ) : Integer.Sparse.eval numericRow1790 x =
    (4320 : ℝ) * reducedSource1790 x := by
  norm_num [numericRow1790, reducedSource1790, Integer.Sparse.eval, Sparse.eval, nodeValue4811, nodeValue4846, nodeValue4875, nodeValue5081, nodeValue5111, nodeValue5130, nodeValue5141, nodeValue5152, nodeValue5176, nodeValue5177, nodeValue5189, nodeValue5207]
  ring

noncomputable def reducedSource1791 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3482 x + ((2 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3616 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))

def numericRow1791 : Integer.Sparse Master := [(Sum.inr 3482, 2), (Sum.inr 3616, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1791 : Integer.Sparse.reindex keyMap MixedData.row1791 = numericRow1791 := by decide +kernel

theorem numericCheck1791 (x : Master → ℝ) : Integer.Sparse.eval numericRow1791 x =
    (1 : ℝ) * reducedSource1791 x := by
  norm_num [numericRow1791, reducedSource1791, Integer.Sparse.eval, Sparse.eval, nodeValue3482, nodeValue3485, nodeValue3616, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
