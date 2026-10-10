import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource96 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow96 : Integer.Sparse Master := [(Sum.inr 2290, 3), (Sum.inr 2294, 1), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

theorem reindexCheck96 : Integer.Sparse.reindex keyMap MixedData.row96 = numericRow96 := by decide +kernel

theorem numericCheck96 (x : Master → ℝ) : Integer.Sparse.eval numericRow96 x =
    (1 : ℝ) * reducedSource96 x := by
  norm_num [numericRow96, reducedSource96, Integer.Sparse.eval, Sparse.eval, nodeValue2290, nodeValue2292, nodeValue2294, nodeValue3634, nodeValue4085]

noncomputable def reducedSource97 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((1 : ℝ) * Sparse.eval nodeValue4285 x + ((3 : ℝ) * Sparse.eval nodeValue4572 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((6 : ℝ) * Sparse.eval nodeValue4747 x + ((3 : ℝ) * Sparse.eval nodeValue4754 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((3 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))

def numericRow97 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 160), (Sum.inl 1, 130), (Sum.inr 828, -2160), (Sum.inr 832, -720), (Sum.inr 857, -2160), (Sum.inr 860, -1440), (Sum.inr 862, -720), (Sum.inr 1190, -2160), (Sum.inr 1297, -720), (Sum.inr 1926, -4320), (Sum.inr 1948, -4320), (Sum.inr 1951, -4320), (Sum.inr 1952, -2160), (Sum.inr 2112, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2289, -720), (Sum.inr 2294, -720), (Sum.inr 3054, -2160), (Sum.inr 3626, -2160), (Sum.inr 3633, -720)]

theorem reindexCheck97 : Integer.Sparse.reindex keyMap MixedData.row97 = numericRow97 := by decide +kernel

theorem numericCheck97 (x : Master → ℝ) : Integer.Sparse.eval numericRow97 x =
    (2880 : ℝ) * reducedSource97 x := by
  norm_num [numericRow97, reducedSource97, Integer.Sparse.eval, Sparse.eval, nodeValue4276, nodeValue4280, nodeValue4285, nodeValue4572, nodeValue4621, nodeValue4747, nodeValue4754, nodeValue4871, nodeValue4898, nodeValue4899, nodeValue5302, nodeValue5310, nodeValue5456]
  ring

noncomputable def reducedSource98 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue860 x + ((3 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((6 : ℝ) * Sparse.eval nodeValue1926 x + ((3 : ℝ) * Sparse.eval nodeValue1951 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((3 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((3 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + 0))))))))))))

def numericRow98 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -70), (Sum.inr 828, 2160), (Sum.inr 832, 720), (Sum.inr 860, 720), (Sum.inr 1190, 2160), (Sum.inr 1297, 720), (Sum.inr 1926, 4320), (Sum.inr 1951, 2160), (Sum.inr 2112, 2160), (Sum.inr 2279, 2160), (Sum.inr 2294, 720), (Sum.inr 3054, 2160)]

theorem reindexCheck98 : Integer.Sparse.reindex keyMap MixedData.row98 = numericRow98 := by decide +kernel

theorem numericCheck98 (x : Master → ℝ) : Integer.Sparse.eval numericRow98 x =
    (720 : ℝ) * reducedSource98 x := by
  norm_num [numericRow98, reducedSource98, Integer.Sparse.eval, Sparse.eval, nodeValue828, nodeValue832, nodeValue860, nodeValue1190, nodeValue1297, nodeValue1926, nodeValue1951, nodeValue2112, nodeValue2279, nodeValue2294, nodeValue3054, nodeValue3121, nodeValue3916]
  ring

noncomputable def reducedSource99 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4476 x + ((3 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4481 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((6 : ℝ) * Sparse.eval nodeValue4817 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((3 : ℝ) * Sparse.eval nodeValue4881 x + ((3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((3 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

def numericRow99 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1091, -144), (Sum.inr 1756, -144), (Sum.inr 2062, -432), (Sum.inr 2230, -432), (Sum.inr 2266, -432), (Sum.inr 2278, -432), (Sum.inr 3633, -144), (Sum.inr 4476, 1728), (Sum.inr 4478, 1728), (Sum.inr 4481, 576), (Sum.inr 4508, 576), (Sum.inr 4817, 3456), (Sum.inr 4881, 1728), (Sum.inr 5276, 1728), (Sum.inr 5311, 576)]

theorem reindexCheck99 : Integer.Sparse.reindex keyMap MixedData.row99 = numericRow99 := by decide +kernel

theorem numericCheck99 (x : Master → ℝ) : Integer.Sparse.eval numericRow99 x =
    (576 : ℝ) * reducedSource99 x := by
  norm_num [numericRow99, reducedSource99, Integer.Sparse.eval, Sparse.eval, nodeValue4476, nodeValue4478, nodeValue4481, nodeValue4507, nodeValue4508, nodeValue4817, nodeValue4843, nodeValue4881, nodeValue4896, nodeValue4901, nodeValue5276, nodeValue5310, nodeValue5311]
  ring

noncomputable def reducedSource100 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((3 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1445 x + ((6 : ℝ) * Sparse.eval nodeValue2497 x + ((3 : ℝ) * Sparse.eval nodeValue2520 x + ((3 : ℝ) * Sparse.eval nodeValue2642 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((3 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))

def numericRow100 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 9), (Sum.inl 13, 16), (Sum.inl 1, 9), (Sum.inr 1061, 216), (Sum.inr 1064, 72), (Sum.inr 1092, 72), (Sum.inr 1372, 216), (Sum.inr 2497, 432), (Sum.inr 2520, 216), (Sum.inr 2777, 216), (Sum.inr 2789, 72)]

theorem reindexCheck100 : Integer.Sparse.reindex keyMap MixedData.row100 = numericRow100 := by decide +kernel

theorem numericCheck100 (x : Master → ℝ) : Integer.Sparse.eval numericRow100 x =
    (72 : ℝ) * reducedSource100 x := by
  norm_num [numericRow100, reducedSource100, Integer.Sparse.eval, Sparse.eval, nodeValue1061, nodeValue1064, nodeValue1092, nodeValue1372, nodeValue1445, nodeValue2497, nodeValue2520, nodeValue2642, nodeValue2777, nodeValue2789, nodeValue3121, nodeValue3225, nodeValue3231]
  ring

noncomputable def reducedSource101 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1729 x + ((3 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((6 : ℝ) * Sparse.eval nodeValue2207 x + ((3 : ℝ) * Sparse.eval nodeValue2230 x + ((3 : ℝ) * Sparse.eval nodeValue2266 x + ((3 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((3 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + 0))))))))))))

def numericRow101 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, -2), (Sum.inr 1729, 432), (Sum.inr 1746, 432), (Sum.inr 1747, 144), (Sum.inr 1756, 144), (Sum.inr 1757, 144), (Sum.inr 2207, 864), (Sum.inr 2230, 432), (Sum.inr 2266, 432), (Sum.inr 2267, 432), (Sum.inr 2744, 432), (Sum.inr 2789, 144)]

theorem reindexCheck101 : Integer.Sparse.reindex keyMap MixedData.row101 = numericRow101 := by decide +kernel

theorem numericCheck101 (x : Master → ℝ) : Integer.Sparse.eval numericRow101 x =
    (144 : ℝ) * reducedSource101 x := by
  norm_num [numericRow101, reducedSource101, Integer.Sparse.eval, Sparse.eval, nodeValue1729, nodeValue1746, nodeValue1747, nodeValue1756, nodeValue1757, nodeValue2207, nodeValue2230, nodeValue2266, nodeValue2267, nodeValue2293, nodeValue2744, nodeValue2788, nodeValue2789]
  ring

noncomputable def reducedSource102 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow102 : Integer.Sparse Master := [(Sum.inr 2278, 3), (Sum.inr 2281, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck102 : Integer.Sparse.reindex keyMap MixedData.row102 = numericRow102 := by decide +kernel

theorem numericCheck102 (x : Master → ℝ) : Integer.Sparse.eval numericRow102 x =
    (1 : ℝ) * reducedSource102 x := by
  norm_num [numericRow102, reducedSource102, Integer.Sparse.eval, Sparse.eval, nodeValue2278, nodeValue2281, nodeValue2293, nodeValue3633, nodeValue4084]

noncomputable def reducedSource103 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1064 x + ((3 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow103 : Integer.Sparse Master := [(Sum.inr 1064, 1), (Sum.inr 1369, 3), (Sum.inr 1438, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem reindexCheck103 : Integer.Sparse.reindex keyMap MixedData.row103 = numericRow103 := by decide +kernel

theorem numericCheck103 (x : Master → ℝ) : Integer.Sparse.eval numericRow103 x =
    (1 : ℝ) * reducedSource103 x := by
  norm_num [numericRow103, reducedSource103, Integer.Sparse.eval, Sparse.eval, nodeValue1064, nodeValue1369, nodeValue1438, nodeValue2281, nodeValue4084]

noncomputable def reducedSource104 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1369 x + ((2 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow104 : Integer.Sparse Master := [(Sum.inr 1369, 1), (Sum.inr 2035, 2), (Sum.inr 2062, 1), (Sum.inr 2281, 1), (Sum.inr 3052, 1), (Sum.inr 4084, -1)]

theorem reindexCheck104 : Integer.Sparse.reindex keyMap MixedData.row104 = numericRow104 := by decide +kernel

theorem numericCheck104 (x : Master → ℝ) : Integer.Sparse.eval numericRow104 x =
    (1 : ℝ) * reducedSource104 x := by
  norm_num [numericRow104, reducedSource104, Integer.Sparse.eval, Sparse.eval, nodeValue1369, nodeValue2035, nodeValue2062, nodeValue2281, nodeValue3052, nodeValue4084]

noncomputable def reducedSource105 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1059 x + ((2 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow105 : Integer.Sparse Master := [(Sum.inr 1059, 1), (Sum.inr 2035, 2), (Sum.inr 2134, 1), (Sum.inr 2278, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem reindexCheck105 : Integer.Sparse.reindex keyMap MixedData.row105 = numericRow105 := by decide +kernel

theorem numericCheck105 (x : Master → ℝ) : Integer.Sparse.eval numericRow105 x =
    (1 : ℝ) * reducedSource105 x := by
  norm_num [numericRow105, reducedSource105, Integer.Sparse.eval, Sparse.eval, nodeValue1059, nodeValue2035, nodeValue2134, nodeValue2278, nodeValue2281, nodeValue4084]

noncomputable def reducedSource106 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1438 x + ((3 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow106 : Integer.Sparse Master := [(Sum.inr 1438, 1), (Sum.inr 2134, 3), (Sum.inr 2281, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem reindexCheck106 : Integer.Sparse.reindex keyMap MixedData.row106 = numericRow106 := by decide +kernel

theorem numericCheck106 (x : Master → ℝ) : Integer.Sparse.eval numericRow106 x =
    (1 : ℝ) * reducedSource106 x := by
  norm_num [numericRow106, reducedSource106, Integer.Sparse.eval, Sparse.eval, nodeValue1438, nodeValue2134, nodeValue2281, nodeValue2789, nodeValue4084]

noncomputable def reducedSource107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow107 : Integer.Sparse Master := [(Sum.inr 1091, 1), (Sum.inr 2062, 3), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem reindexCheck107 : Integer.Sparse.reindex keyMap MixedData.row107 = numericRow107 := by decide +kernel

theorem numericCheck107 (x : Master → ℝ) : Integer.Sparse.eval numericRow107 x =
    (1 : ℝ) * reducedSource107 x := by
  norm_num [numericRow107, reducedSource107, Integer.Sparse.eval, Sparse.eval, nodeValue1091, nodeValue2062, nodeValue2281, nodeValue2293, nodeValue4084]

noncomputable def reducedSource108 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow108 : Integer.Sparse Master := [(Sum.inr 1059, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem reindexCheck108 : Integer.Sparse.reindex keyMap MixedData.row108 = numericRow108 := by decide +kernel

theorem numericCheck108 (x : Master → ℝ) : Integer.Sparse.eval numericRow108 x =
    (1 : ℝ) * reducedSource108 x := by
  norm_num [numericRow108, reducedSource108, Integer.Sparse.eval, Sparse.eval, nodeValue1059, nodeValue1064, nodeValue1091, nodeValue2281, nodeValue4084]

noncomputable def reducedSource109 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4500 x + ((1 : ℝ) * Sparse.eval nodeValue4508 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue4836 x + ((3 : ℝ) * Sparse.eval nodeValue4844 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((3 : ℝ) * Sparse.eval nodeValue4890 x + ((3 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4900 x + ((3 : ℝ) * Sparse.eval nodeValue5268 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

def numericRow109 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1094, -120), (Sum.inr 1741, -120), (Sum.inr 2065, -360), (Sum.inr 2218, -360), (Sum.inr 2247, -360), (Sum.inr 2281, -120), (Sum.inr 2290, -360), (Sum.inr 2294, -120), (Sum.inr 3634, -120), (Sum.inr 4500, 1440), (Sum.inr 4508, 480), (Sum.inr 4836, 2880), (Sum.inr 4844, 1440), (Sum.inr 4892, 1440), (Sum.inr 4900, 480), (Sum.inr 5268, 1440)]

theorem reindexCheck109 : Integer.Sparse.reindex keyMap MixedData.row109 = numericRow109 := by decide +kernel

theorem numericCheck109 (x : Master → ℝ) : Integer.Sparse.eval numericRow109 x =
    (480 : ℝ) * reducedSource109 x := by
  norm_num [numericRow109, reducedSource109, Integer.Sparse.eval, Sparse.eval, nodeValue4500, nodeValue4508, nodeValue4510, nodeValue4836, nodeValue4844, nodeValue4845, nodeValue4890, nodeValue4892, nodeValue4897, nodeValue4899, nodeValue4900, nodeValue5268, nodeValue5296]
  ring

noncomputable def reducedSource110 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((3 : ℝ) * Sparse.eval nodeValue2136 x + ((3 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((6 : ℝ) * Sparse.eval nodeValue2716 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((3 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((3 : ℝ) * Sparse.eval nodeValue3095 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

def numericRow110 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, -21), (Sum.inl 13, 16), (Sum.inl 1, 3), (Sum.inr 1436, 216), (Sum.inr 1438, 72), (Sum.inr 2136, 216), (Sum.inr 2255, 216), (Sum.inr 2281, 72), (Sum.inr 2285, 72), (Sum.inr 2716, 432), (Sum.inr 2734, 216)]

theorem reindexCheck110 : Integer.Sparse.reindex keyMap MixedData.row110 = numericRow110 := by decide +kernel

theorem numericCheck110 (x : Master → ℝ) : Integer.Sparse.eval numericRow110 x =
    (72 : ℝ) * reducedSource110 x := by
  norm_num [numericRow110, reducedSource110, Integer.Sparse.eval, Sparse.eval, nodeValue1436, nodeValue1438, nodeValue1454, nodeValue2136, nodeValue2255, nodeValue2281, nodeValue2285, nodeValue2716, nodeValue2734, nodeValue2755, nodeValue2770, nodeValue3095, nodeValue3114]
  ring

noncomputable def reducedSource111 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((6 : ℝ) * Sparse.eval nodeValue2197 x + ((3 : ℝ) * Sparse.eval nodeValue2218 x + ((3 : ℝ) * Sparse.eval nodeValue2222 x + ((3 : ℝ) * Sparse.eval nodeValue2247 x + ((3 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + 0))))))))))))

def numericRow111 : Integer.Sparse Master := [(Sum.inl 0, -2), (Sum.inl 2, -9), (Sum.inl 13, -16), (Sum.inl 1, -3), (Sum.inr 1716, 432), (Sum.inr 1741, 144), (Sum.inr 1747, 144), (Sum.inr 2197, 864), (Sum.inr 2218, 432), (Sum.inr 2222, 432), (Sum.inr 2247, 432), (Sum.inr 2255, 432), (Sum.inr 2285, 144), (Sum.inr 2734, 432)]

theorem reindexCheck111 : Integer.Sparse.reindex keyMap MixedData.row111 = numericRow111 := by decide +kernel

theorem numericCheck111 (x : Master → ℝ) : Integer.Sparse.eval numericRow111 x =
    (144 : ℝ) * reducedSource111 x := by
  norm_num [numericRow111, reducedSource111, Integer.Sparse.eval, Sparse.eval, nodeValue1716, nodeValue1741, nodeValue1747, nodeValue2197, nodeValue2218, nodeValue2222, nodeValue2247, nodeValue2255, nodeValue2268, nodeValue2285, nodeValue2734, nodeValue2770, nodeValue2778]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
