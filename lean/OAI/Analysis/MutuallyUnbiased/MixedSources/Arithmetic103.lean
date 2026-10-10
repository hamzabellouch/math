import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1648 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4551 x + ((1 : ℝ) * Sparse.eval nodeValue4555 x + ((2 : ℝ) * Sparse.eval nodeValue4559 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((4 : ℝ) * Sparse.eval nodeValue4970 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5113 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0))))))))))))

def numericRow1648 : Integer.Sparse Master := [(Sum.inl 0, 53), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 1, 260), (Sum.inr 1136, -2160), (Sum.inr 1140, -540), (Sum.inr 1145, -1080), (Sum.inr 2815, -2160), (Sum.inr 2820, -540), (Sum.inr 3273, -2160), (Sum.inr 3275, -540), (Sum.inr 3277, -1080), (Sum.inr 3310, -1080), (Sum.inr 3588, -2160), (Sum.inr 3596, -540), (Sum.inr 3603, -2160), (Sum.inr 3608, -2160), (Sum.inr 3614, -1080)]

theorem reindexCheck1648 : Integer.Sparse.reindex keyMap MixedData.row1648 = numericRow1648 := by decide +kernel

theorem numericCheck1648 (x : Master → ℝ) : Integer.Sparse.eval numericRow1648 x =
    (2160 : ℝ) * reducedSource1648 x := by
  norm_num [numericRow1648, reducedSource1648, Integer.Sparse.eval, Sparse.eval, nodeValue4551, nodeValue4555, nodeValue4559, nodeValue4625, nodeValue4970, nodeValue4979, nodeValue5113, nodeValue5168, nodeValue5171, nodeValue5176, nodeValue5308, nodeValue5312, nodeValue5441]
  ring

noncomputable def reducedSource1649 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((2 : ℝ) * Sparse.eval nodeValue1145 x + ((2 : ℝ) * Sparse.eval nodeValue1307 x + ((4 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2894 x + ((4 : ℝ) * Sparse.eval nodeValue2963 x + ((4 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

def numericRow1649 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, -260), (Sum.inr 1136, 2160), (Sum.inr 1140, 540), (Sum.inr 1145, 1080), (Sum.inr 2815, 2160), (Sum.inr 2820, 540)]

theorem reindexCheck1649 : Integer.Sparse.reindex keyMap MixedData.row1649 = numericRow1649 := by decide +kernel

theorem numericCheck1649 (x : Master → ℝ) : Integer.Sparse.eval numericRow1649 x =
    (540 : ℝ) * reducedSource1649 x := by
  norm_num [numericRow1649, reducedSource1649, Integer.Sparse.eval, Sparse.eval, nodeValue1136, nodeValue1140, nodeValue1145, nodeValue1307, nodeValue2815, nodeValue2820, nodeValue2894, nodeValue2963, nodeValue2965, nodeValue2968, nodeValue3124, nodeValue3126, nodeValue4037]
  ring

noncomputable def reducedSource1650 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((2 : ℝ) * Sparse.eval nodeValue4360 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((4 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue5033 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))

def numericRow1650 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, -14), (Sum.inr 924, -864), (Sum.inr 928, -216), (Sum.inr 938, -432), (Sum.inr 1043, -432), (Sum.inr 1674, -864), (Sum.inr 1677, -216), (Sum.inr 1693, -432), (Sum.inr 1725, -432), (Sum.inr 2334, -864), (Sum.inr 2344, -216), (Sum.inr 2425, -432), (Sum.inr 2482, -864), (Sum.inr 2726, -216), (Sum.inr 3411, -864), (Sum.inr 3422, -216), (Sum.inr 3449, -432), (Sum.inr 3468, -864), (Sum.inr 3545, -216), (Sum.inr 3607, -864), (Sum.inr 3616, -432), (Sum.inr 3627, -432)]

theorem reindexCheck1650 : Integer.Sparse.reindex keyMap MixedData.row1650 = numericRow1650 := by decide +kernel

theorem numericCheck1650 (x : Master → ℝ) : Integer.Sparse.eval numericRow1650 x =
    (864 : ℝ) * reducedSource1650 x := by
  norm_num [numericRow1650, reducedSource1650, Integer.Sparse.eval, Sparse.eval, nodeValue4346, nodeValue4350, nodeValue4360, nodeValue4460, nodeValue4943, nodeValue4952, nodeValue5033, nodeValue5075, nodeValue5169, nodeValue5177, nodeValue5261, nodeValue5293, nodeValue5487]
  ring

noncomputable def reducedSource1651 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue928 x + ((2 : ℝ) * Sparse.eval nodeValue938 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((4 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2344 x + ((2 : ℝ) * Sparse.eval nodeValue2425 x + ((4 : ℝ) * Sparse.eval nodeValue2482 x + ((4 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2605 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + 0))))))))))))

def numericRow1651 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, 14), (Sum.inr 924, 864), (Sum.inr 928, 216), (Sum.inr 938, 432), (Sum.inr 1043, 432), (Sum.inr 2334, 864), (Sum.inr 2344, 216), (Sum.inr 2425, 432), (Sum.inr 2482, 864), (Sum.inr 2726, 216)]

theorem reindexCheck1651 : Integer.Sparse.reindex keyMap MixedData.row1651 = numericRow1651 := by decide +kernel

theorem numericCheck1651 (x : Master → ℝ) : Integer.Sparse.eval numericRow1651 x =
    (216 : ℝ) * reducedSource1651 x := by
  norm_num [numericRow1651, reducedSource1651, Integer.Sparse.eval, Sparse.eval, nodeValue924, nodeValue928, nodeValue938, nodeValue1043, nodeValue2334, nodeValue2344, nodeValue2425, nodeValue2482, nodeValue2595, nodeValue2605, nodeValue2726, nodeValue2767, nodeValue4000]
  ring

noncomputable def reducedSource1652 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0))))))))))))))))))))

def numericRow1652 : Integer.Sparse Master := [(Sum.inl 0, 71), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, -40), (Sum.inr 930, -1440), (Sum.inr 934, -720), (Sum.inr 939, -720), (Sum.inr 1046, -720), (Sum.inr 1131, -1440), (Sum.inr 1144, -720), (Sum.inr 1690, -1440), (Sum.inr 1692, -720), (Sum.inr 1694, -720), (Sum.inr 1750, -720), (Sum.inr 2339, -1440), (Sum.inr 2345, -720), (Sum.inr 2429, -1440), (Sum.inr 2434, -1440), (Sum.inr 2485, -1440), (Sum.inr 3264, -1440), (Sum.inr 3276, -720), (Sum.inr 3310, -720), (Sum.inr 3420, -1440), (Sum.inr 3423, -720), (Sum.inr 3455, -1440), (Sum.inr 3457, -1440), (Sum.inr 3481, -1440), (Sum.inr 3607, -1440), (Sum.inr 3613, -1440), (Sum.inr 3614, -720), (Sum.inr 3615, -1440), (Sum.inr 3616, -720), (Sum.inr 3632, -720), (Sum.inr 3634, -720)]

theorem reindexCheck1652 : Integer.Sparse.reindex keyMap MixedData.row1652 = numericRow1652 := by decide +kernel

theorem numericCheck1652 (x : Master → ℝ) : Integer.Sparse.eval numericRow1652 x =
    (2880 : ℝ) * reducedSource1652 x := by
  norm_num [numericRow1652, reducedSource1652, Integer.Sparse.eval, Sparse.eval, nodeValue4352, nodeValue4356, nodeValue4361, nodeValue4463, nodeValue4546, nodeValue4558, nodeValue4625, nodeValue4948, nodeValue4953, nodeValue4972, nodeValue5037, nodeValue5078, nodeValue5169, nodeValue5172, nodeValue5174, nodeValue5176, nodeValue5177, nodeValue5294, nodeValue5296, nodeValue5309, nodeValue5442]
  ring

noncomputable def reducedSource1653 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((2 : ℝ) * Sparse.eval nodeValue2339 x + ((1 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2434 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

def numericRow1653 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, 40), (Sum.inr 930, 1440), (Sum.inr 934, 720), (Sum.inr 939, 720), (Sum.inr 1046, 720), (Sum.inr 1131, 1440), (Sum.inr 1144, 720), (Sum.inr 2339, 1440), (Sum.inr 2345, 720), (Sum.inr 2429, 1440), (Sum.inr 2434, 1440), (Sum.inr 2485, 1440)]

theorem reindexCheck1653 : Integer.Sparse.reindex keyMap MixedData.row1653 = numericRow1653 := by decide +kernel

theorem numericCheck1653 (x : Master → ℝ) : Integer.Sparse.eval numericRow1653 x =
    (720 : ℝ) * reducedSource1653 x := by
  norm_num [numericRow1653, reducedSource1653, Integer.Sparse.eval, Sparse.eval, nodeValue930, nodeValue934, nodeValue939, nodeValue1046, nodeValue1131, nodeValue1144, nodeValue1304, nodeValue2339, nodeValue2345, nodeValue2429, nodeValue2434, nodeValue2485, nodeValue2599, nodeValue2601, nodeValue2604, nodeValue2768, nodeValue2770, nodeValue2960, nodeValue2969, nodeValue3123, nodeValue4001]
  ring

noncomputable def reducedSource1654 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4841 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((4 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5107 x + ((2 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((4 : ℝ) * Sparse.eval nodeValue5139 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + 0))))))))))

def numericRow1654 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 100), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2112, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -2160), (Sum.inr 2287, -2160), (Sum.inr 2482, -4320), (Sum.inr 2485, -4320), (Sum.inr 2519, -2160), (Sum.inr 3468, -4320), (Sum.inr 3481, -4320), (Sum.inr 3486, -2160), (Sum.inr 3608, -2160), (Sum.inr 5128, 8640), (Sum.inr 5139, 17280)]

theorem reindexCheck1654 : Integer.Sparse.reindex keyMap MixedData.row1654 = numericRow1654 := by decide +kernel

theorem numericCheck1654 (x : Master → ℝ) : Integer.Sparse.eval numericRow1654 x =
    (4320 : ℝ) * reducedSource1654 x := by
  norm_num [numericRow1654, reducedSource1654, Integer.Sparse.eval, Sparse.eval, nodeValue4807, nodeValue4841, nodeValue4843, nodeValue4871, nodeValue5075, nodeValue5078, nodeValue5107, nodeValue5109, nodeValue5128, nodeValue5139, nodeValue5171]
  ring

noncomputable def reducedSource1655 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4237 x + ((1 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4243 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((2 : ℝ) * Sparse.eval nodeValue4538 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4723 x + ((2 : ℝ) * Sparse.eval nodeValue4727 x + ((2 : ℝ) * Sparse.eval nodeValue4747 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + 0))))))))))))))))))))

def numericRow1655 : Integer.Sparse Master := [(Sum.inl 0, 45), (Sum.inl 5, -20), (Sum.inl 2, -5), (Sum.inl 7, -80), (Sum.inl 3, 80), (Sum.inl 12, -80), (Sum.inl 1, 150), (Sum.inr 737, -4320), (Sum.inr 740, -2160), (Sum.inr 743, -2160), (Sum.inr 828, -2160), (Sum.inr 840, -4320), (Sum.inr 842, -2160), (Sum.inr 844, -2160), (Sum.inr 857, -2160), (Sum.inr 1123, -4320), (Sum.inr 1143, -2160), (Sum.inr 1297, -2160), (Sum.inr 1812, -4320), (Sum.inr 1819, -2160), (Sum.inr 1877, -4320), (Sum.inr 1881, -4320), (Sum.inr 1926, -4320), (Sum.inr 1935, -4320), (Sum.inr 1937, -4320), (Sum.inr 1939, -4320), (Sum.inr 1948, -4320), (Sum.inr 2110, -4320), (Sum.inr 2112, -4320), (Sum.inr 2115, -2160), (Sum.inr 2165, -4320), (Sum.inr 2167, -2160), (Sum.inr 2169, -2160), (Sum.inr 2275, -4320), (Sum.inr 2276, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -2160), (Sum.inr 2287, -4320), (Sum.inr 2289, -2160), (Sum.inr 2294, -2160), (Sum.inr 2954, -4320), (Sum.inr 3606, -4320), (Sum.inr 3614, -2160), (Sum.inr 3633, -2160), (Sum.inr 3907, -2160)]

theorem reindexCheck1655 : Integer.Sparse.reindex keyMap MixedData.row1655 = numericRow1655 := by decide +kernel

theorem numericCheck1655 (x : Master → ℝ) : Integer.Sparse.eval numericRow1655 x =
    (8640 : ℝ) * reducedSource1655 x := by
  norm_num [numericRow1655, reducedSource1655, Integer.Sparse.eval, Sparse.eval, nodeValue4237, nodeValue4240, nodeValue4243, nodeValue4276, nodeValue4538, nodeValue4557, nodeValue4621, nodeValue4686, nodeValue4693, nodeValue4723, nodeValue4727, nodeValue4747, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue4899, nodeValue5170, nodeValue5176, nodeValue5310, nodeValue5443]
  ring

noncomputable def reducedSource1656 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue737 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue743 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((2 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue1877 x + ((2 : ℝ) * Sparse.eval nodeValue1881 x + ((2 : ℝ) * Sparse.eval nodeValue1926 x + ((2 : ℝ) * Sparse.eval nodeValue2110 x + ((2 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow1656 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 5, 20), (Sum.inl 2, 5), (Sum.inl 7, 80), (Sum.inl 3, -80), (Sum.inl 12, 80), (Sum.inl 1, -150), (Sum.inr 737, 4320), (Sum.inr 740, 2160), (Sum.inr 743, 2160), (Sum.inr 828, 2160), (Sum.inr 1123, 4320), (Sum.inr 1143, 2160), (Sum.inr 1297, 2160), (Sum.inr 1812, 4320), (Sum.inr 1819, 2160), (Sum.inr 1877, 4320), (Sum.inr 1881, 4320), (Sum.inr 1926, 4320), (Sum.inr 2110, 4320), (Sum.inr 2112, 4320), (Sum.inr 2115, 2160), (Sum.inr 2279, 2160), (Sum.inr 2281, 2160), (Sum.inr 2954, 4320)]

theorem reindexCheck1656 : Integer.Sparse.reindex keyMap MixedData.row1656 = numericRow1656 := by decide +kernel

theorem numericCheck1656 (x : Master → ℝ) : Integer.Sparse.eval numericRow1656 x =
    (2160 : ℝ) * reducedSource1656 x := by
  norm_num [numericRow1656, reducedSource1656, Integer.Sparse.eval, Sparse.eval, nodeValue737, nodeValue740, nodeValue743, nodeValue828, nodeValue1123, nodeValue1143, nodeValue1297, nodeValue1812, nodeValue1819, nodeValue1877, nodeValue1881, nodeValue1926, nodeValue2110, nodeValue2112, nodeValue2115, nodeValue2279, nodeValue2281, nodeValue2954, nodeValue2968, nodeValue3121, nodeValue3889]
  ring

noncomputable def reducedSource1657 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4353 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((1 : ℝ) * Sparse.eval nodeValue4362 x + ((2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((2 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((2 : ℝ) * Sparse.eval nodeValue4772 x + ((2 : ℝ) * Sparse.eval nodeValue4777 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + 0))))))))))))))))))))

def numericRow1657 : Integer.Sparse Master := [(Sum.inr 1046, -1), (Sum.inr 1750, -1), (Sum.inr 2025, -2), (Sum.inr 2107, -2), (Sum.inr 2116, -1), (Sum.inr 2224, -2), (Sum.inr 2247, -1), (Sum.inr 2260, -2), (Sum.inr 2288, -1), (Sum.inr 2290, -1), (Sum.inr 2782, -1), (Sum.inr 3583, -1), (Sum.inr 4353, 8), (Sum.inr 4358, 4), (Sum.inr 4362, 4), (Sum.inr 4367, 8), (Sum.inr 4374, 4), (Sum.inr 4464, 4), (Sum.inr 4699, 8), (Sum.inr 4705, 4), (Sum.inr 4772, 8), (Sum.inr 4777, 8), (Sum.inr 4853, 8), (Sum.inr 5173, 8), (Sum.inr 5175, 4), (Sum.inr 5295, 4)]

theorem reindexCheck1657 : Integer.Sparse.reindex keyMap MixedData.row1657 = numericRow1657 := by decide +kernel

theorem numericCheck1657 (x : Master → ℝ) : Integer.Sparse.eval numericRow1657 x =
    (4 : ℝ) * reducedSource1657 x := by
  norm_num [numericRow1657, reducedSource1657, Integer.Sparse.eval, Sparse.eval, nodeValue4353, nodeValue4358, nodeValue4362, nodeValue4367, nodeValue4374, nodeValue4463, nodeValue4464, nodeValue4699, nodeValue4705, nodeValue4772, nodeValue4777, nodeValue4807, nodeValue4853, nodeValue4866, nodeValue4875, nodeValue4890, nodeValue4895, nodeValue5173, nodeValue5175, nodeValue5295, nodeValue5304]
  ring

noncomputable def reducedSource1658 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1686 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue2198 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((2 : ℝ) * Sparse.eval nodeValue2256 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + 0))))))))))))))))))))

def numericRow1658 : Integer.Sparse Master := [(Sum.inr 1686, 2), (Sum.inr 1687, 1), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1745, 1), (Sum.inr 1748, 1), (Sum.inr 1750, 1), (Sum.inr 2198, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2256, 2), (Sum.inr 2259, 2), (Sum.inr 2260, 2), (Sum.inr 2286, 1), (Sum.inr 2288, 1), (Sum.inr 2290, 1), (Sum.inr 2735, 2), (Sum.inr 2761, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1)]

theorem reindexCheck1658 : Integer.Sparse.reindex keyMap MixedData.row1658 = numericRow1658 := by decide +kernel

theorem numericCheck1658 (x : Master → ℝ) : Integer.Sparse.eval numericRow1658 x =
    (1 : ℝ) * reducedSource1658 x := by
  norm_num [numericRow1658, reducedSource1658, Integer.Sparse.eval, Sparse.eval, nodeValue1686, nodeValue1687, nodeValue1695, nodeValue1720, nodeValue1745, nodeValue1748, nodeValue1750, nodeValue2198, nodeValue2223, nodeValue2224, nodeValue2256, nodeValue2259, nodeValue2260, nodeValue2286, nodeValue2288, nodeValue2290, nodeValue2291, nodeValue2735, nodeValue2761, nodeValue2781, nodeValue2782]

noncomputable def reducedSource1659 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1831 x + ((2 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1659 : Integer.Sparse Master := [(Sum.inr 953, 1), (Sum.inr 1831, 1), (Sum.inr 1979, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1659 : Integer.Sparse.reindex keyMap MixedData.row1659 = numericRow1659 := by decide +kernel

theorem numericCheck1659 (x : Master → ℝ) : Integer.Sparse.eval numericRow1659 x =
    (1 : ℝ) * reducedSource1659 x := by
  norm_num [numericRow1659, reducedSource1659, Integer.Sparse.eval, Sparse.eval, nodeValue953, nodeValue1831, nodeValue1979, nodeValue2112, nodeValue2116, nodeValue4083]

noncomputable def reducedSource1660 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1660 : Integer.Sparse Master := [(Sum.inr 1336, 1), (Sum.inr 1973, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2112, 1), (Sum.inr 2952, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1660 : Integer.Sparse.reindex keyMap MixedData.row1660 = numericRow1660 := by decide +kernel

theorem numericCheck1660 (x : Master → ℝ) : Integer.Sparse.eval numericRow1660 x =
    (1 : ℝ) * reducedSource1660 x := by
  norm_num [numericRow1660, reducedSource1660, Integer.Sparse.eval, Sparse.eval, nodeValue1336, nodeValue1973, nodeValue1979, nodeValue2025, nodeValue2112, nodeValue2952, nodeValue4083]

noncomputable def reducedSource1661 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((1 : ℝ) * Sparse.eval nodeValue4492 x + ((1 : ℝ) * Sparse.eval nodeValue4504 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4824 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((2 : ℝ) * Sparse.eval nodeValue4829 x + ((2 : ℝ) * Sparse.eval nodeValue4840 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4844 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + 0)))))))))))))))))))

def numericRow1661 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -50), (Sum.inr 1074, -2160), (Sum.inr 1650, -2160), (Sum.inr 2025, -4320), (Sum.inr 2047, -4320), (Sum.inr 2062, -4320), (Sum.inr 2079, -4320), (Sum.inr 2109, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -4320), (Sum.inr 2261, -2160), (Sum.inr 2519, -2160), (Sum.inr 3486, -2160), (Sum.inr 3615, -2160), (Sum.inr 4486, 17280), (Sum.inr 4492, 8640), (Sum.inr 4504, 8640), (Sum.inr 4808, 17280), (Sum.inr 4824, 17280), (Sum.inr 4829, 17280), (Sum.inr 4840, 17280), (Sum.inr 4844, 8640), (Sum.inr 4853, 17280), (Sum.inr 4872, 8640), (Sum.inr 4881, 8640), (Sum.inr 5139, 17280)]

theorem reindexCheck1661 : Integer.Sparse.reindex keyMap MixedData.row1661 = numericRow1661 := by decide +kernel

theorem numericCheck1661 (x : Master → ℝ) : Integer.Sparse.eval numericRow1661 x =
    (8640 : ℝ) * reducedSource1661 x := by
  norm_num [numericRow1661, reducedSource1661, Integer.Sparse.eval, Sparse.eval, nodeValue4486, nodeValue4490, nodeValue4492, nodeValue4504, nodeValue4807, nodeValue4808, nodeValue4824, nodeValue4827, nodeValue4829, nodeValue4840, nodeValue4841, nodeValue4843, nodeValue4844, nodeValue4853, nodeValue4868, nodeValue4872, nodeValue4881, nodeValue5109, nodeValue5139, nodeValue5174]
  ring

noncomputable def reducedSource1662 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2071 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((2 : ℝ) * Sparse.eval nodeValue2080 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((1 : ℝ) * Sparse.eval nodeValue2642 x + 0))))))))))))))))))))

def numericRow1662 : Integer.Sparse Master := [(Sum.inl 0, -96), (Sum.inl 5, -40), (Sum.inl 6, -30), (Sum.inl 2, 160), (Sum.inl 3, 160), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 1, 230), (Sum.inr 1639, 8640), (Sum.inr 1650, 4320), (Sum.inr 1651, 4320), (Sum.inr 1659, 4320), (Sum.inr 2025, 8640), (Sum.inr 2062, 4320), (Sum.inr 2071, 8640), (Sum.inr 2079, 8640), (Sum.inr 2080, 8640), (Sum.inr 2090, 8640), (Sum.inr 2092, 8640), (Sum.inr 2109, 4320), (Sum.inr 2113, 4320), (Sum.inr 2121, 8640), (Sum.inr 2134, 4320), (Sum.inr 2136, 4320), (Sum.inr 2618, 8640)]

theorem reindexCheck1662 : Integer.Sparse.reindex keyMap MixedData.row1662 = numericRow1662 := by decide +kernel

theorem numericCheck1662 (x : Master → ℝ) : Integer.Sparse.eval numericRow1662 x =
    (4320 : ℝ) * reducedSource1662 x := by
  norm_num [numericRow1662, reducedSource1662, Integer.Sparse.eval, Sparse.eval, nodeValue1639, nodeValue1650, nodeValue1651, nodeValue1659, nodeValue2025, nodeValue2060, nodeValue2062, nodeValue2071, nodeValue2079, nodeValue2080, nodeValue2090, nodeValue2092, nodeValue2109, nodeValue2113, nodeValue2121, nodeValue2134, nodeValue2136, nodeValue2601, nodeValue2618, nodeValue2640, nodeValue2642]
  ring

noncomputable def reducedSource1663 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2436 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1663 : Integer.Sparse Master := [(Sum.inr 1159, 1), (Sum.inr 2355, 1), (Sum.inr 2436, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1663 : Integer.Sparse.reindex keyMap MixedData.row1663 = numericRow1663 := by decide +kernel

theorem numericCheck1663 (x : Master → ℝ) : Integer.Sparse.eval numericRow1663 x =
    (1 : ℝ) * reducedSource1663 x := by
  norm_num [numericRow1663, reducedSource1663, Integer.Sparse.eval, Sparse.eval, nodeValue1159, nodeValue2355, nodeValue2436, nodeValue2482, nodeValue2569, nodeValue2590, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
