import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
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

noncomputable def reducedSource2032 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3709 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((2 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow2032 : Integer.Sparse Master := [(Sum.inr 2351, 1), (Sum.inr 3135, 1), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 2), (Sum.inr 4091, -1)]

theorem reindexCheck2032 : Integer.Sparse.reindex keyMap MixedData.row2032 = numericRow2032 := by decide +kernel

theorem numericCheck2032 (x : Master → ℝ) : Integer.Sparse.eval numericRow2032 x =
    (1 : ℝ) * reducedSource2032 x := by
  norm_num [numericRow2032, reducedSource2032, Integer.Sparse.eval, Sparse.eval, nodeValue2351, nodeValue3135, nodeValue3709, nodeValue3716, nodeValue3721, nodeValue4091]

noncomputable def reducedSource2033 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((2 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((4 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5372 x + ((4 : ℝ) * Sparse.eval nodeValue5384 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + 0))))))))))))

def numericRow2033 : Integer.Sparse Master := [(Sum.inl 0, 180), (Sum.inl 23, -720), (Sum.inl 27, -180), (Sum.inl 1, 720), (Sum.inr 1814, -12960), (Sum.inr 1817, -3240), (Sum.inr 1819, -6480), (Sum.inr 2115, -6480), (Sum.inr 2157, -12960), (Sum.inr 2159, -3240), (Sum.inr 2169, -6480), (Sum.inr 2276, -6480), (Sum.inr 2817, -12960), (Sum.inr 2820, -3240), (Sum.inr 3591, -12960), (Sum.inr 3596, -3240), (Sum.inr 3614, -6480), (Sum.inr 3708, -6480), (Sum.inr 3732, -12960), (Sum.inr 3791, -6480), (Sum.inr 3811, -12960), (Sum.inr 3886, -6480), (Sum.inr 3891, -12960), (Sum.inr 3907, -6480)]

theorem reindexCheck2033 : Integer.Sparse.reindex keyMap MixedData.row2033 = numericRow2033 := by decide +kernel

theorem numericCheck2033 (x : Master → ℝ) : Integer.Sparse.eval numericRow2033 x =
    (12960 : ℝ) * reducedSource2033 x := by
  norm_num [numericRow2033, reducedSource2033, Integer.Sparse.eval, Sparse.eval, nodeValue4688, nodeValue4691, nodeValue4693, nodeValue4874, nodeValue4973, nodeValue4979, nodeValue5176, nodeValue5372, nodeValue5384, nodeValue5387, nodeValue5441, nodeValue5443, nodeValue5449]; ring

noncomputable def reducedSource2034 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((2 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue2115 x + ((4 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((2 : ℝ) * Sparse.eval nodeValue3708 x + ((4 : ℝ) * Sparse.eval nodeValue3732 x + ((4 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((2 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

def numericRow2034 : Integer.Sparse Master := [(Sum.inl 0, -180), (Sum.inl 23, 720), (Sum.inl 27, 180), (Sum.inl 1, -720), (Sum.inr 1814, 12960), (Sum.inr 1817, 3240), (Sum.inr 1819, 6480), (Sum.inr 2115, 6480), (Sum.inr 2817, 12960), (Sum.inr 2820, 3240), (Sum.inr 3708, 6480), (Sum.inr 3732, 12960), (Sum.inr 3886, 3240)]

theorem reindexCheck2034 : Integer.Sparse.reindex keyMap MixedData.row2034 = numericRow2034 := by decide +kernel

theorem numericCheck2034 (x : Master → ℝ) : Integer.Sparse.eval numericRow2034 x =
    (3240 : ℝ) * reducedSource2034 x := by
  norm_num [numericRow2034, reducedSource2034, Integer.Sparse.eval, Sparse.eval, nodeValue1814, nodeValue1817, nodeValue1819, nodeValue2115, nodeValue2817, nodeValue2820, nodeValue2968, nodeValue3708, nodeValue3732, nodeValue3739, nodeValue3886, nodeValue3889, nodeValue4037]; ring

noncomputable def reducedSource2035 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5232 x + ((2 : ℝ) * Sparse.eval nodeValue5235 x + ((4 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5297 x + ((8 : ℝ) * Sparse.eval nodeValue5355 x + ((2 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5376 x + ((2 : ℝ) * Sparse.eval nodeValue5390 x + 0)))))))

def numericRow2035 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -45), (Sum.inr 2686, -6480), (Sum.inr 3397, -6480), (Sum.inr 3693, -12960), (Sum.inr 3770, -12960), (Sum.inr 3894, -3240), (Sum.inr 5232, 51840), (Sum.inr 5235, 12960), (Sum.inr 5297, 12960), (Sum.inr 5376, 12960)]

theorem reindexCheck2035 : Integer.Sparse.reindex keyMap MixedData.row2035 = numericRow2035 := by decide +kernel

theorem numericCheck2035 (x : Master → ℝ) : Integer.Sparse.eval numericRow2035 x =
    (6480 : ℝ) * reducedSource2035 x := by
  norm_num [numericRow2035, reducedSource2035, Integer.Sparse.eval, Sparse.eval, nodeValue5232, nodeValue5235, nodeValue5238, nodeValue5297, nodeValue5355, nodeValue5371, nodeValue5376, nodeValue5390]; ring

noncomputable def reducedSource2036 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((4 : ℝ) * Sparse.eval nodeValue4949 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((4 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + 0)))))))))))))

def numericRow2036 : Integer.Sparse Master := [(Sum.inl 0, 108), (Sum.inl 24, -360), (Sum.inl 27, -90), (Sum.inl 1, -90), (Sum.inr 1815, -2160), (Sum.inr 1818, -2160), (Sum.inr 2116, -1080), (Sum.inr 2166, -2160), (Sum.inr 2168, -2160), (Sum.inr 2288, -1080), (Sum.inr 2341, -4320), (Sum.inr 2345, -2160), (Sum.inr 2818, -2160), (Sum.inr 3417, -4320), (Sum.inr 3423, -2160), (Sum.inr 3592, -2160), (Sum.inr 3614, -2160), (Sum.inr 3616, -1080), (Sum.inr 3709, -2160), (Sum.inr 3790, -2160), (Sum.inr 3792, -2160), (Sum.inr 3815, -2160), (Sum.inr 3892, -4320), (Sum.inr 3898, -2160), (Sum.inr 3913, -2160)]

theorem reindexCheck2036 : Integer.Sparse.reindex keyMap MixedData.row2036 = numericRow2036 := by decide +kernel

theorem numericCheck2036 (x : Master → ℝ) : Integer.Sparse.eval numericRow2036 x =
    (4320 : ℝ) * reducedSource2036 x := by
  norm_num [numericRow2036, reducedSource2036, Integer.Sparse.eval, Sparse.eval, nodeValue4689, nodeValue4692, nodeValue4875, nodeValue4949, nodeValue4953, nodeValue4974, nodeValue5176, nodeValue5177, nodeValue5373, nodeValue5388, nodeValue5404, nodeValue5418, nodeValue5442, nodeValue5451]; ring

noncomputable def reducedSource2037 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1815 x + ((2 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((4 : ℝ) * Sparse.eval nodeValue2341 x + ((2 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3709 x + ((4 : ℝ) * Sparse.eval nodeValue3737 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + ((2 : ℝ) * Sparse.eval nodeValue3933 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0)))))))))))))

def numericRow2037 : Integer.Sparse Master := [(Sum.inl 0, -108), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, 90), (Sum.inr 1815, 2160), (Sum.inr 1818, 2160), (Sum.inr 2116, 1080), (Sum.inr 2341, 4320), (Sum.inr 2345, 2160), (Sum.inr 2818, 2160), (Sum.inr 3709, 2160), (Sum.inr 3790, 2160)]

theorem reindexCheck2037 : Integer.Sparse.reindex keyMap MixedData.row2037 = numericRow2037 := by decide +kernel

theorem numericCheck2037 (x : Master → ℝ) : Integer.Sparse.eval numericRow2037 x =
    (1080 : ℝ) * reducedSource2037 x := by
  norm_num [numericRow2037, reducedSource2037, Integer.Sparse.eval, Sparse.eval, nodeValue1815, nodeValue1818, nodeValue2116, nodeValue2341, nodeValue2345, nodeValue2604, nodeValue2818, nodeValue2969, nodeValue3709, nodeValue3737, nodeValue3790, nodeValue3888, nodeValue3933, nodeValue4001]; ring

noncomputable def reducedSource2038 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5236 x + ((4 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((8 : ℝ) * Sparse.eval nodeValue5355 x + ((4 : ℝ) * Sparse.eval nodeValue5356 x + ((4 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + 0))))))))

def numericRow2038 : Integer.Sparse Master := [(Sum.inl 0, 20), (Sum.inl 23, 192), (Sum.inl 27, 72), (Sum.inl 1, 100), (Sum.inl 30, 96), (Sum.inr 2686, -3456), (Sum.inr 3397, -3456), (Sum.inr 3693, -6912), (Sum.inr 3694, -3456), (Sum.inr 3770, -6912), (Sum.inr 3773, -3456), (Sum.inr 3893, -1728), (Sum.inr 4043, -864), (Sum.inr 5236, 13824), (Sum.inr 5303, 3456), (Sum.inr 5377, 6912)]

theorem reindexCheck2038 : Integer.Sparse.reindex keyMap MixedData.row2038 = numericRow2038 := by decide +kernel

theorem numericCheck2038 (x : Master → ℝ) : Integer.Sparse.eval numericRow2038 x =
    (3456 : ℝ) * reducedSource2038 x := by
  norm_num [numericRow2038, reducedSource2038, Integer.Sparse.eval, Sparse.eval, nodeValue5236, nodeValue5238, nodeValue5303, nodeValue5355, nodeValue5356, nodeValue5371, nodeValue5377, nodeValue5389, nodeValue5466]; ring

noncomputable def reducedSource2039 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4959 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5339 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + 0)))))))))))))))))))))))))))))

def numericRow2039 : Integer.Sparse Master := [(Sum.inr 2341, -1), (Sum.inr 2488, -1), (Sum.inr 2561, -1), (Sum.inr 2817, -1), (Sum.inr 3417, -1), (Sum.inr 3478, -1), (Sum.inr 3522, -1), (Sum.inr 3591, -1), (Sum.inr 3671, -1), (Sum.inr 3689, -1), (Sum.inr 3706, -1), (Sum.inr 3719, -1), (Sum.inr 3732, -1), (Sum.inr 3754, -1), (Sum.inr 3757, -1), (Sum.inr 3771, -1), (Sum.inr 3795, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 3845, -2), (Sum.inr 4668, 4), (Sum.inr 4669, 4), (Sum.inr 4670, 4), (Sum.inr 4690, 4), (Sum.inr 4856, 4), (Sum.inr 4931, 4), (Sum.inr 4934, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4959, 4), (Sum.inr 4966, 4), (Sum.inr 5188, 4), (Sum.inr 5339, 4), (Sum.inr 5353, 4), (Sum.inr 5379, 4), (Sum.inr 5385, 4), (Sum.inr 5446, 4)]

theorem reindexCheck2039 : Integer.Sparse.reindex keyMap MixedData.row2039 = numericRow2039 := by decide +kernel

theorem numericCheck2039 (x : Master → ℝ) : Integer.Sparse.eval numericRow2039 x =
    (4 : ℝ) * reducedSource2039 x := by
  norm_num [numericRow2039, reducedSource2039, Integer.Sparse.eval, Sparse.eval, nodeValue4668, nodeValue4669, nodeValue4670, nodeValue4690, nodeValue4856, nodeValue4931, nodeValue4934, nodeValue4949, nodeValue4955, nodeValue4957, nodeValue4959, nodeValue4966, nodeValue4973, nodeValue5080, nodeValue5141, nodeValue5188, nodeValue5336, nodeValue5339, nodeValue5351, nodeValue5353, nodeValue5367, nodeValue5370, nodeValue5378, nodeValue5379, nodeValue5384, nodeValue5385, nodeValue5409, nodeValue5411, nodeValue5428, nodeValue5446]; ring

noncomputable def reducedSource2040 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1816 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2359 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2829 x + ((1 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3710 x + ((1 : ℝ) * Sparse.eval nodeValue3711 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3941 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + 0)))))))))))))))))))))))))))))

def numericRow2040 : Integer.Sparse Master := [(Sum.inl 0, -630), (Sum.inl 2, -270), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -1440), (Sum.inl 27, 1080), (Sum.inl 1, 360), (Sum.inr 1794, 8640), (Sum.inr 1795, 8640), (Sum.inr 1796, 8640), (Sum.inr 1816, 8640), (Sum.inr 2094, 8640), (Sum.inr 2350, 8640), (Sum.inr 2352, 8640), (Sum.inr 2620, 8640), (Sum.inr 2801, 8640), (Sum.inr 2802, 8640), (Sum.inr 2819, 8640), (Sum.inr 2824, 8640), (Sum.inr 3710, 8640), (Sum.inr 3724, 8640), (Sum.inr 3733, 8640), (Sum.inr 3783, 8640), (Sum.inr 3881, 8640)]

theorem reindexCheck2040 : Integer.Sparse.reindex keyMap MixedData.row2040 = numericRow2040 := by decide +kernel

theorem numericCheck2040 (x : Master → ℝ) : Integer.Sparse.eval numericRow2040 x =
    (8640 : ℝ) * reducedSource2040 x := by
  norm_num [numericRow2040, reducedSource2040, Integer.Sparse.eval, Sparse.eval, nodeValue1794, nodeValue1795, nodeValue1796, nodeValue1816, nodeValue2094, nodeValue2350, nodeValue2352, nodeValue2359, nodeValue2620, nodeValue2801, nodeValue2802, nodeValue2819, nodeValue2824, nodeValue2829, nodeValue2943, nodeValue2990, nodeValue3710, nodeValue3711, nodeValue3724, nodeValue3727, nodeValue3733, nodeValue3738, nodeValue3783, nodeValue3831, nodeValue3881, nodeValue3883, nodeValue3937, nodeValue3941, nodeValue4003, nodeValue4035]; ring

noncomputable def reducedSource2041 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3512 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3760 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + 0)))))))))))))))))))))))))))))

def numericRow2041 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2155, 1), (Sum.inr 2158, 1), (Sum.inr 2164, 1), (Sum.inr 2274, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3512, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3555, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3757, 1), (Sum.inr 3760, 1), (Sum.inr 3761, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3884, 1)]

theorem reindexCheck2041 : Integer.Sparse.reindex keyMap MixedData.row2041 = numericRow2041 := by decide +kernel

theorem numericCheck2041 (x : Master → ℝ) : Integer.Sparse.eval numericRow2041 x =
    (1 : ℝ) * reducedSource2041 x := by
  norm_num [numericRow2041, reducedSource2041, Integer.Sparse.eval, Sparse.eval, nodeValue2154, nodeValue2155, nodeValue2158, nodeValue2164, nodeValue2274, nodeValue3406, nodeValue3415, nodeValue3417, nodeValue3478, nodeValue3508, nodeValue3509, nodeValue3512, nodeValue3522, nodeValue3538, nodeValue3555, nodeValue3591, nodeValue3754, nodeValue3757, nodeValue3760, nodeValue3761, nodeValue3766, nodeValue3771, nodeValue3795, nodeValue3807, nodeValue3811, nodeValue3813, nodeValue3832, nodeValue3845, nodeValue3868, nodeValue3884]

noncomputable def reducedSource2042 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3671 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2042 : Integer.Sparse Master := [(Sum.inr 2348, 1), (Sum.inr 3133, 1), (Sum.inr 3671, 1), (Sum.inr 3693, 1), (Sum.inr 3719, 1), (Sum.inr 3720, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2042 : Integer.Sparse.reindex keyMap MixedData.row2042 = numericRow2042 := by decide +kernel

theorem numericCheck2042 (x : Master → ℝ) : Integer.Sparse.eval numericRow2042 x =
    (1 : ℝ) * reducedSource2042 x := by
  norm_num [numericRow2042, reducedSource2042, Integer.Sparse.eval, Sparse.eval, nodeValue2348, nodeValue3133, nodeValue3671, nodeValue3693, nodeValue3719, nodeValue3720, nodeValue4092]

noncomputable def reducedSource2043 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue3674 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2043 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2798, 1), (Sum.inr 3674, 1), (Sum.inr 3689, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2043 : Integer.Sparse.reindex keyMap MixedData.row2043 = numericRow2043 := by decide +kernel

theorem numericCheck2043 (x : Master → ℝ) : Integer.Sparse.eval numericRow2043 x =
    (1 : ℝ) * reducedSource2043 x := by
  norm_num [numericRow2043, reducedSource2043, Integer.Sparse.eval, Sparse.eval, nodeValue2321, nodeValue2798, nodeValue3674, nodeValue3689, nodeValue3691, nodeValue3693, nodeValue4092]

noncomputable def reducedSource2044 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3674 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow2044 : Integer.Sparse Master := [(Sum.inr 2356, 1), (Sum.inr 3138, 1), (Sum.inr 3674, 1), (Sum.inr 3693, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 4092, -1)]

theorem reindexCheck2044 : Integer.Sparse.reindex keyMap MixedData.row2044 = numericRow2044 := by decide +kernel

theorem numericCheck2044 (x : Master → ℝ) : Integer.Sparse.eval numericRow2044 x =
    (1 : ℝ) * reducedSource2044 x := by
  norm_num [numericRow2044, reducedSource2044, Integer.Sparse.eval, Sparse.eval, nodeValue2356, nodeValue3138, nodeValue3674, nodeValue3693, nodeValue3732, nodeValue3733, nodeValue4092]

noncomputable def reducedSource2045 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

def numericRow2045 : Integer.Sparse Master := [(Sum.inr 1810, -2), (Sum.inr 1818, -1), (Sum.inr 1819, -1), (Sum.inr 2152, -2), (Sum.inr 2168, -1), (Sum.inr 2169, -1), (Sum.inr 2522, -1), (Sum.inr 2672, -2), (Sum.inr 2685, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -1), (Sum.inr 3054, -1), (Sum.inr 3391, -2), (Sum.inr 3498, -2), (Sum.inr 3548, -1), (Sum.inr 3626, -1), (Sum.inr 4703, 8), (Sum.inr 4704, 4), (Sum.inr 4705, 4), (Sum.inr 4884, 4), (Sum.inr 4945, 8), (Sum.inr 4976, 8), (Sum.inr 5206, 4), (Sum.inr 5215, 8), (Sum.inr 5229, 8), (Sum.inr 5287, 8), (Sum.inr 5300, 4)]

theorem reindexCheck2045 : Integer.Sparse.reindex keyMap MixedData.row2045 = numericRow2045 := by decide +kernel

theorem numericCheck2045 (x : Master → ℝ) : Integer.Sparse.eval numericRow2045 x =
    (4 : ℝ) * reducedSource2045 x := by
  norm_num [numericRow2045, reducedSource2045, Integer.Sparse.eval, Sparse.eval, nodeValue4684, nodeValue4692, nodeValue4693, nodeValue4703, nodeValue4704, nodeValue4705, nodeValue4846, nodeValue4884, nodeValue4945, nodeValue4976, nodeValue5110, nodeValue5206, nodeValue5215, nodeValue5228, nodeValue5229, nodeValue5248, nodeValue5274, nodeValue5275, nodeValue5287, nodeValue5300, nodeValue5302]; ring

noncomputable def reducedSource2046 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((1 : ℝ) * Sparse.eval nodeValue1831 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2363 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue2831 x + ((1 : ℝ) * Sparse.eval nodeValue2832 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((2 : ℝ) * Sparse.eval nodeValue3083 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((2 : ℝ) * Sparse.eval nodeValue3094 x + ((2 : ℝ) * Sparse.eval nodeValue3106 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((2 : ℝ) * Sparse.eval nodeValue3144 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

def numericRow2046 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 2, 150), (Sum.inl 55, 480), (Sum.inl 27, 120), (Sum.inl 1, 120), (Sum.inr 1829, 2880), (Sum.inr 1830, 1440), (Sum.inr 1831, 1440), (Sum.inr 2138, 1440), (Sum.inr 2362, 2880), (Sum.inr 2643, 1440), (Sum.inr 2758, 2880), (Sum.inr 2774, 1440), (Sum.inr 2831, 2880), (Sum.inr 3083, 2880), (Sum.inr 3092, 2880)]

theorem reindexCheck2046 : Integer.Sparse.reindex keyMap MixedData.row2046 = numericRow2046 := by decide +kernel

theorem numericCheck2046 (x : Master → ℝ) : Integer.Sparse.eval numericRow2046 x =
    (1440 : ℝ) * reducedSource2046 x := by
  norm_num [numericRow2046, reducedSource2046, Integer.Sparse.eval, Sparse.eval, nodeValue1829, nodeValue1830, nodeValue1831, nodeValue2138, nodeValue2362, nodeValue2363, nodeValue2643, nodeValue2758, nodeValue2774, nodeValue2776, nodeValue2831, nodeValue2832, nodeValue3005, nodeValue3083, nodeValue3092, nodeValue3094, nodeValue3106, nodeValue3110, nodeValue3112, nodeValue3144, nodeValue3216]; ring

noncomputable def reducedSource2047 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2659 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + 0))))))))))))))))))))

def numericRow2047 : Integer.Sparse Master := [(Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2272, 2), (Sum.inr 2273, 1), (Sum.inr 2280, 1), (Sum.inr 2286, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2672, 2), (Sum.inr 2673, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 2705, 2), (Sum.inr 2743, 1), (Sum.inr 3025, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1)]

theorem reindexCheck2047 : Integer.Sparse.reindex keyMap MixedData.row2047 = numericRow2047 := by decide +kernel

theorem numericCheck2047 (x : Master → ℝ) : Integer.Sparse.eval numericRow2047 x =
    (1 : ℝ) * reducedSource2047 x := by
  norm_num [numericRow2047, reducedSource2047, Integer.Sparse.eval, Sparse.eval, nodeValue2152, nodeValue2168, nodeValue2169, nodeValue2229, nodeValue2272, nodeValue2273, nodeValue2280, nodeValue2286, nodeValue2653, nodeValue2658, nodeValue2659, nodeValue2672, nodeValue2673, nodeValue2685, nodeValue2687, nodeValue2705, nodeValue2742, nodeValue2743, nodeValue3025, nodeValue3054, nodeValue3055]

end MUB6.Certificate.MixedSourceBridge

end OAI
