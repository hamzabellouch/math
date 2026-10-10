import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1696 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2011 x + ((2 : ℝ) * Sparse.eval nodeValue2016 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1696 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2011, 1), (Sum.inr 2016, 2), (Sum.inr 2242, 1), (Sum.inr 3524, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1696 : Integer.Sparse.reindex keyMap MixedData.row1696 = numericRow1696 := by decide +kernel

theorem numericCheck1696 (x : Master → ℝ) : Integer.Sparse.eval numericRow1696 x =
    (1 : ℝ) * reducedSource1696 x := by
  norm_num [numericRow1696, reducedSource1696, Integer.Sparse.eval, Sparse.eval, nodeValue2008, nodeValue2011, nodeValue2016, nodeValue2242, nodeValue3524, nodeValue4080]

noncomputable def reducedSource1697 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2117 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2122 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1697 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2119, 1), (Sum.inr 2122, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2681, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1697 : Integer.Sparse.reindex keyMap MixedData.row1697 = numericRow1697 := by decide +kernel

theorem numericCheck1697 (x : Master → ℝ) : Integer.Sparse.eval numericRow1697 x =
    (1 : ℝ) * reducedSource1697 x := by
  norm_num [numericRow1697, reducedSource1697, Integer.Sparse.eval, Sparse.eval, nodeValue2117, nodeValue2119, nodeValue2122, nodeValue2128, nodeValue2215, nodeValue2681, nodeValue4082]

noncomputable def reducedSource1698 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2072 x + ((1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1698 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2072, 1), (Sum.inr 2075, 1), (Sum.inr 2085, 1), (Sum.inr 2190, 1), (Sum.inr 3557, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1698 : Integer.Sparse.reindex keyMap MixedData.row1698 = numericRow1698 := by decide +kernel

theorem numericCheck1698 (x : Master → ℝ) : Integer.Sparse.eval numericRow1698 x =
    (1 : ℝ) * reducedSource1698 x := by
  norm_num [numericRow1698, reducedSource1698, Integer.Sparse.eval, Sparse.eval, nodeValue2070, nodeValue2072, nodeValue2075, nodeValue2085, nodeValue2190, nodeValue3557, nodeValue4080]

noncomputable def reducedSource1699 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2490 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1699 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2455, 1), (Sum.inr 2459, 1), (Sum.inr 2490, 1), (Sum.inr 2697, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1699 : Integer.Sparse.reindex keyMap MixedData.row1699 = numericRow1699 := by decide +kernel

theorem numericCheck1699 (x : Master → ℝ) : Integer.Sparse.eval numericRow1699 x =
    (1 : ℝ) * reducedSource1699 x := by
  norm_num [numericRow1699, reducedSource1699, Integer.Sparse.eval, Sparse.eval, nodeValue2453, nodeValue2455, nodeValue2459, nodeValue2490, nodeValue2697, nodeValue3795, nodeValue4088]

noncomputable def reducedSource1700 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2536 x + ((1 : ℝ) * Sparse.eval nodeValue2565 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1700 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2533, 1), (Sum.inr 2536, 1), (Sum.inr 2565, 1), (Sum.inr 2672, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1700 : Integer.Sparse.reindex keyMap MixedData.row1700 = numericRow1700 := by decide +kernel

theorem numericCheck1700 (x : Master → ℝ) : Integer.Sparse.eval numericRow1700 x =
    (1 : ℝ) * reducedSource1700 x := by
  norm_num [numericRow1700, reducedSource1700, Integer.Sparse.eval, Sparse.eval, nodeValue2453, nodeValue2533, nodeValue2536, nodeValue2565, nodeValue2672, nodeValue3795, nodeValue4088]

noncomputable def reducedSource1701 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue1993 x + ((1 : ℝ) * Sparse.eval nodeValue1997 x + ((1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1701 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1993, 1), (Sum.inr 1997, 1), (Sum.inr 2030, 1), (Sum.inr 2215, 1), (Sum.inr 3516, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1701 : Integer.Sparse.reindex keyMap MixedData.row1701 = numericRow1701 := by decide +kernel

theorem numericCheck1701 (x : Master → ℝ) : Integer.Sparse.eval numericRow1701 x =
    (1 : ℝ) * reducedSource1701 x := by
  norm_num [numericRow1701, reducedSource1701, Integer.Sparse.eval, Sparse.eval, nodeValue1991, nodeValue1993, nodeValue1997, nodeValue2030, nodeValue2215, nodeValue3516, nodeValue4082]

noncomputable def reducedSource1702 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4365 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4560 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4697 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((2 : ℝ) * Sparse.eval nodeValue4771 x + ((2 : ℝ) * Sparse.eval nodeValue4776 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5175 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + 0))))))))))))))))))))

def numericRow1702 : Integer.Sparse Master := [(Sum.inr 1043, -1), (Sum.inr 1297, -1), (Sum.inr 1725, -1), (Sum.inr 2022, -2), (Sum.inr 2106, -2), (Sum.inr 2109, -2), (Sum.inr 2115, -1), (Sum.inr 2203, -2), (Sum.inr 2242, -2), (Sum.inr 2261, -2), (Sum.inr 2276, -1), (Sum.inr 2289, -1), (Sum.inr 2765, -1), (Sum.inr 2783, -2), (Sum.inr 3582, -1), (Sum.inr 4365, 8), (Sum.inr 4370, 4), (Sum.inr 4373, 4), (Sum.inr 4552, 8), (Sum.inr 4560, 4), (Sum.inr 4697, 8), (Sum.inr 4704, 4), (Sum.inr 4771, 8), (Sum.inr 4776, 8), (Sum.inr 5161, 8), (Sum.inr 5175, 4)]

theorem reindexCheck1702 : Integer.Sparse.reindex keyMap MixedData.row1702 = numericRow1702 := by decide +kernel

theorem numericCheck1702 (x : Master → ℝ) : Integer.Sparse.eval numericRow1702 x =
    (4 : ℝ) * reducedSource1702 x := by
  norm_num [numericRow1702, reducedSource1702, Integer.Sparse.eval, Sparse.eval, nodeValue4365, nodeValue4370, nodeValue4373, nodeValue4460, nodeValue4552, nodeValue4560, nodeValue4621, nodeValue4697, nodeValue4704, nodeValue4771, nodeValue4776, nodeValue4804, nodeValue4865, nodeValue4868, nodeValue4874, nodeValue4894, nodeValue4897, nodeValue5161, nodeValue5175, nodeValue5291, nodeValue5305]
  ring

noncomputable def reducedSource1703 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((2 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((2 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((2 : ℝ) * Sparse.eval nodeValue2895 x + ((2 : ℝ) * Sparse.eval nodeValue2899 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((2 : ℝ) * Sparse.eval nodeValue2964 x + ((2 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow1703 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 6, 5), (Sum.inl 2, 80), (Sum.inl 35, -80), (Sum.inl 26, -80), (Sum.inl 1, 60), (Sum.inr 1137, 1440), (Sum.inr 1142, 720), (Sum.inr 1146, 720), (Sum.inr 1320, 1440), (Sum.inr 1325, 720), (Sum.inr 2816, 1440), (Sum.inr 2821, 720), (Sum.inr 2895, 1440), (Sum.inr 2899, 1440), (Sum.inr 2964, 1440), (Sum.inr 2967, 720)]

theorem reindexCheck1703 : Integer.Sparse.reindex keyMap MixedData.row1703 = numericRow1703 := by decide +kernel

theorem numericCheck1703 (x : Master → ℝ) : Integer.Sparse.eval numericRow1703 x =
    (720 : ℝ) * reducedSource1703 x := by
  norm_num [numericRow1703, reducedSource1703, Integer.Sparse.eval, Sparse.eval, nodeValue1137, nodeValue1142, nodeValue1146, nodeValue1308, nodeValue1320, nodeValue1325, nodeValue1416, nodeValue2816, nodeValue2821, nodeValue2895, nodeValue2899, nodeValue2941, nodeValue2964, nodeValue2966, nodeValue2967, nodeValue3103, nodeValue3114, nodeValue3125, nodeValue3185, nodeValue3187, nodeValue3230]
  ring

noncomputable def reducedSource1704 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1704 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((2 : ℝ) * Sparse.eval nodeValue2189 x + ((2 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((2 : ℝ) * Sparse.eval nodeValue2239 x + ((2 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((2 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + 0))))))))))))))))))))

def numericRow1704 : Integer.Sparse Master := [(Sum.inr 1704, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 2189, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2212, 2), (Sum.inr 2239, 2), (Sum.inr 2242, 2), (Sum.inr 2258, 1), (Sum.inr 2261, 2), (Sum.inr 2273, 1), (Sum.inr 2276, 1), (Sum.inr 2289, 1), (Sum.inr 2719, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2783, 1)]

theorem reindexCheck1704 : Integer.Sparse.reindex keyMap MixedData.row1704 = numericRow1704 := by decide +kernel

theorem numericCheck1704 (x : Master → ℝ) : Integer.Sparse.eval numericRow1704 x =
    (1 : ℝ) * reducedSource1704 x := by
  norm_num [numericRow1704, reducedSource1704, Integer.Sparse.eval, Sparse.eval, nodeValue1704, nodeValue1722, nodeValue1725, nodeValue1735, nodeValue2189, nodeValue2200, nodeValue2203, nodeValue2212, nodeValue2239, nodeValue2242, nodeValue2258, nodeValue2261, nodeValue2264, nodeValue2273, nodeValue2276, nodeValue2289, nodeValue2292, nodeValue2719, nodeValue2761, nodeValue2765, nodeValue2783]

noncomputable def reducedSource1705 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((2 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2115 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1705 : Integer.Sparse Master := [(Sum.inr 952, 1), (Sum.inr 1830, 1), (Sum.inr 1978, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1705 : Integer.Sparse.reindex keyMap MixedData.row1705 = numericRow1705 := by decide +kernel

theorem numericCheck1705 (x : Master → ℝ) : Integer.Sparse.eval numericRow1705 x =
    (1 : ℝ) * reducedSource1705 x := by
  norm_num [numericRow1705, reducedSource1705, Integer.Sparse.eval, Sparse.eval, nodeValue952, nodeValue1830, nodeValue1978, nodeValue2109, nodeValue2115, nodeValue4084]

noncomputable def reducedSource1706 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1706 : Integer.Sparse Master := [(Sum.inr 1157, 1), (Sum.inr 1972, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2109, 1), (Sum.inr 2588, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1706 : Integer.Sparse.reindex keyMap MixedData.row1706 = numericRow1706 := by decide +kernel

theorem numericCheck1706 (x : Master → ℝ) : Integer.Sparse.eval numericRow1706 x =
    (1 : ℝ) * reducedSource1706 x := by
  norm_num [numericRow1706, reducedSource1706, Integer.Sparse.eval, Sparse.eval, nodeValue1157, nodeValue1972, nodeValue1978, nodeValue2022, nodeValue2109, nodeValue2588, nodeValue4084]

noncomputable def reducedSource1707 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue1823 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((2 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1707 : Integer.Sparse Master := [(Sum.inr 943, 1), (Sum.inr 1823, 1), (Sum.inr 1972, 1), (Sum.inr 2106, 1), (Sum.inr 2109, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1707 : Integer.Sparse.reindex keyMap MixedData.row1707 = numericRow1707 := by decide +kernel

theorem numericCheck1707 (x : Master → ℝ) : Integer.Sparse.eval numericRow1707 x =
    (1 : ℝ) * reducedSource1707 x := by
  norm_num [numericRow1707, reducedSource1707, Integer.Sparse.eval, Sparse.eval, nodeValue943, nodeValue1823, nodeValue1972, nodeValue2106, nodeValue2109, nodeValue4084]

noncomputable def reducedSource1708 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4233 x + ((1 : ℝ) * Sparse.eval nodeValue4235 x + ((1 : ℝ) * Sparse.eval nodeValue4242 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((2 : ℝ) * Sparse.eval nodeValue4338 x + ((1 : ℝ) * Sparse.eval nodeValue4359 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4721 x + ((2 : ℝ) * Sparse.eval nodeValue4726 x + ((2 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

def numericRow1708 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 5, -20), (Sum.inl 2, 10), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 4, -80), (Sum.inl 1, 45), (Sum.inr 733, -4320), (Sum.inr 735, -2160), (Sum.inr 742, -2160), (Sum.inr 799, -4320), (Sum.inr 801, -2160), (Sum.inr 815, -2160), (Sum.inr 826, -2160), (Sum.inr 843, -2160), (Sum.inr 916, -4320), (Sum.inr 937, -2160), (Sum.inr 1037, -2160), (Sum.inr 1633, -4320), (Sum.inr 1647, -2160), (Sum.inr 1683, -2160), (Sum.inr 1807, -4320), (Sum.inr 1818, -2160), (Sum.inr 1875, -4320), (Sum.inr 1880, -4320), (Sum.inr 1905, -4320), (Sum.inr 1917, -4320), (Sum.inr 1924, -4320), (Sum.inr 1938, -4320), (Sum.inr 2047, -4320), (Sum.inr 2065, -2160), (Sum.inr 2079, -4320), (Sum.inr 2107, -4320), (Sum.inr 2116, -2160), (Sum.inr 2151, -4320), (Sum.inr 2168, -2160), (Sum.inr 2218, -2160), (Sum.inr 2260, -4320), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2288, -2160), (Sum.inr 2590, -4320), (Sum.inr 2765, -2160), (Sum.inr 3564, -4320), (Sum.inr 3582, -2160), (Sum.inr 3614, -2160), (Sum.inr 3913, -2160)]

theorem reindexCheck1708 : Integer.Sparse.reindex keyMap MixedData.row1708 = numericRow1708 := by decide +kernel

theorem numericCheck1708 (x : Master → ℝ) : Integer.Sparse.eval numericRow1708 x =
    (8640 : ℝ) * reducedSource1708 x := by
  norm_num [numericRow1708, reducedSource1708, Integer.Sparse.eval, Sparse.eval, nodeValue4233, nodeValue4235, nodeValue4242, nodeValue4272, nodeValue4338, nodeValue4359, nodeValue4454, nodeValue4681, nodeValue4692, nodeValue4721, nodeValue4726, nodeValue4744, nodeValue4827, nodeValue4845, nodeValue4866, nodeValue4875, nodeValue4896, nodeValue5163, nodeValue5176, nodeValue5291, nodeValue5451]
  ring

noncomputable def reducedSource1709 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue742 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((2 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue937 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1818 x + ((2 : ℝ) * Sparse.eval nodeValue1875 x + ((2 : ℝ) * Sparse.eval nodeValue1880 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((2 : ℝ) * Sparse.eval nodeValue2079 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

def numericRow1709 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 5, 20), (Sum.inl 2, -10), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, -45), (Sum.inr 733, 4320), (Sum.inr 735, 2160), (Sum.inr 742, 2160), (Sum.inr 826, 2160), (Sum.inr 916, 4320), (Sum.inr 937, 2160), (Sum.inr 1037, 2160), (Sum.inr 1807, 4320), (Sum.inr 1818, 2160), (Sum.inr 1875, 4320), (Sum.inr 1880, 4320), (Sum.inr 1924, 4320), (Sum.inr 2079, 4320), (Sum.inr 2107, 4320), (Sum.inr 2116, 2160), (Sum.inr 2218, 2160), (Sum.inr 2278, 2160), (Sum.inr 2590, 4320), (Sum.inr 2765, 2160)]

theorem reindexCheck1709 : Integer.Sparse.reindex keyMap MixedData.row1709 = numericRow1709 := by decide +kernel

theorem numericCheck1709 (x : Master → ℝ) : Integer.Sparse.eval numericRow1709 x =
    (2160 : ℝ) * reducedSource1709 x := by
  norm_num [numericRow1709, reducedSource1709, Integer.Sparse.eval, Sparse.eval, nodeValue733, nodeValue735, nodeValue742, nodeValue826, nodeValue916, nodeValue937, nodeValue1037, nodeValue1807, nodeValue1818, nodeValue1875, nodeValue1880, nodeValue1924, nodeValue2079, nodeValue2107, nodeValue2116, nodeValue2218, nodeValue2278, nodeValue2590, nodeValue2604, nodeValue2765, nodeValue3888]
  ring

noncomputable def reducedSource1710 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4527 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4531 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4929 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5127 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + 0)))))))))))))))))))))))))))))

def numericRow1710 : Integer.Sparse Master := [(Sum.inr 1131, -1), (Sum.inr 1242, -1), (Sum.inr 2334, -1), (Sum.inr 2425, -1), (Sum.inr 2479, -1), (Sum.inr 2482, -1), (Sum.inr 2488, -1), (Sum.inr 2553, -1), (Sum.inr 2561, -1), (Sum.inr 2590, -1), (Sum.inr 2722, -1), (Sum.inr 2726, -1), (Sum.inr 3264, -1), (Sum.inr 3300, -1), (Sum.inr 3411, -1), (Sum.inr 3449, -1), (Sum.inr 3459, -1), (Sum.inr 3468, -1), (Sum.inr 3478, -1), (Sum.inr 3514, -1), (Sum.inr 3522, -1), (Sum.inr 3533, -1), (Sum.inr 3545, -1), (Sum.inr 3564, -1), (Sum.inr 4527, 4), (Sum.inr 4528, 4), (Sum.inr 4531, 4), (Sum.inr 4534, 4), (Sum.inr 4535, 4), (Sum.inr 4547, 4), (Sum.inr 4591, 4), (Sum.inr 4934, 4), (Sum.inr 4954, 4), (Sum.inr 4965, 4), (Sum.inr 5041, 4), (Sum.inr 5147, 4)]

theorem reindexCheck1710 : Integer.Sparse.reindex keyMap MixedData.row1710 = numericRow1710 := by decide +kernel

theorem numericCheck1710 (x : Master → ℝ) : Integer.Sparse.eval numericRow1710 x =
    (4 : ℝ) * reducedSource1710 x := by
  norm_num [numericRow1710, reducedSource1710, Integer.Sparse.eval, Sparse.eval, nodeValue4527, nodeValue4528, nodeValue4531, nodeValue4534, nodeValue4535, nodeValue4546, nodeValue4547, nodeValue4591, nodeValue4608, nodeValue4929, nodeValue4934, nodeValue4943, nodeValue4954, nodeValue4965, nodeValue5033, nodeValue5041, nodeValue5072, nodeValue5075, nodeValue5080, nodeValue5101, nodeValue5107, nodeValue5127, nodeValue5134, nodeValue5141, nodeValue5147, nodeValue5163, nodeValue5258, nodeValue5261, nodeValue5274, nodeValue5409]
  ring

noncomputable def reducedSource1711 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3262 x + ((1 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3266 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3449 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3458 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3513 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + 0)))))))))))))))))))))))))))))

def numericRow1711 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3260, 1), (Sum.inr 3262, 1), (Sum.inr 3264, 1), (Sum.inr 3266, 1), (Sum.inr 3268, 1), (Sum.inr 3272, 1), (Sum.inr 3291, 1), (Sum.inr 3300, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3449, 1), (Sum.inr 3452, 1), (Sum.inr 3458, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3545, 1), (Sum.inr 3564, 1)]

theorem reindexCheck1711 : Integer.Sparse.reindex keyMap MixedData.row1711 = numericRow1711 := by decide +kernel

theorem numericCheck1711 (x : Master → ℝ) : Integer.Sparse.eval numericRow1711 x =
    (1 : ℝ) * reducedSource1711 x := by
  norm_num [numericRow1711, reducedSource1711, Integer.Sparse.eval, Sparse.eval, nodeValue3255, nodeValue3260, nodeValue3262, nodeValue3264, nodeValue3266, nodeValue3268, nodeValue3272, nodeValue3291, nodeValue3300, nodeValue3403, nodeValue3411, nodeValue3415, nodeValue3449, nodeValue3452, nodeValue3458, nodeValue3459, nodeValue3468, nodeValue3470, nodeValue3475, nodeValue3478, nodeValue3484, nodeValue3513, nodeValue3514, nodeValue3522, nodeValue3530, nodeValue3533, nodeValue3545, nodeValue3547, nodeValue3564, nodeValue3807]

end MUB6.Certificate.MixedSourceBridge

end OAI
