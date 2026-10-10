import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource560 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow560 : Integer.Sparse Master := [(Sum.inr 1044, 1), (Sum.inr 2023, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 2), (Sum.inr 4083, -1)]

theorem reindexCheck560 : Integer.Sparse.reindex keyMap MixedData.row560 = numericRow560 := by decide +kernel

theorem numericCheck560 (x : Master → ℝ) : Integer.Sparse.eval numericRow560 x =
    (1 : ℝ) * reducedSource560 x := by
  norm_num [numericRow560, reducedSource560, Integer.Sparse.eval, Sparse.eval, nodeValue1044, nodeValue2023, nodeValue2110, nodeValue2245, nodeValue2263, nodeValue4083]

noncomputable def reducedSource561 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow561 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2092, 1), (Sum.inr 2094, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem reindexCheck561 : Integer.Sparse.reindex keyMap MixedData.row561 = numericRow561 := by decide +kernel

theorem numericCheck561 (x : Master → ℝ) : Integer.Sparse.eval numericRow561 x =
    (1 : ℝ) * reducedSource561 x := by
  norm_num [numericRow561, reducedSource561, Integer.Sparse.eval, Sparse.eval, nodeValue2089, nodeValue2092, nodeValue2094, nodeValue2110, nodeValue2245, nodeValue3573, nodeValue4083]

noncomputable def reducedSource562 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow562 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2012, 1), (Sum.inr 2023, 2), (Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

theorem reindexCheck562 : Integer.Sparse.reindex keyMap MixedData.row562 = numericRow562 := by decide +kernel

theorem numericCheck562 (x : Master → ℝ) : Integer.Sparse.eval numericRow562 x =
    (1 : ℝ) * reducedSource562 x := by
  norm_num [numericRow562, reducedSource562, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue2012, nodeValue2023, nodeValue2245, nodeValue3526, nodeValue4083]

noncomputable def reducedSource563 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow563 : Integer.Sparse Master := [(Sum.inr 1026, 1), (Sum.inr 2012, 1), (Sum.inr 2094, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem reindexCheck563 : Integer.Sparse.reindex keyMap MixedData.row563 = numericRow563 := by decide +kernel

theorem numericCheck563 (x : Master → ℝ) : Integer.Sparse.eval numericRow563 x =
    (1 : ℝ) * reducedSource563 x := by
  norm_num [numericRow563, reducedSource563, Integer.Sparse.eval, Sparse.eval, nodeValue1026, nodeValue2012, nodeValue2094, nodeValue2244, nodeValue2245, nodeValue4083]

noncomputable def reducedSource564 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4252 x + ((1 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((2 : ℝ) * Sparse.eval nodeValue4740 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0))))))))))))))))))))

def numericRow564 : Integer.Sparse Master := [(Sum.inl 0, 93), (Sum.inl 2, 15), (Sum.inl 3, 240), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -90), (Sum.inr 786, -2160), (Sum.inr 787, -2160), (Sum.inr 789, -2160), (Sum.inr 811, -4320), (Sum.inr 822, -2160), (Sum.inr 823, -2160), (Sum.inr 824, -4320), (Sum.inr 847, -2160), (Sum.inr 1898, -2160), (Sum.inr 1900, -2160), (Sum.inr 1913, -4320), (Sum.inr 1921, -2160), (Sum.inr 1922, -4320), (Sum.inr 1940, -2160), (Sum.inr 2023, -4320), (Sum.inr 2025, -4320), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2105, -2160), (Sum.inr 2106, -2160), (Sum.inr 2107, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -4320), (Sum.inr 2241, -2160), (Sum.inr 2242, -2160), (Sum.inr 2245, -2160), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -2160), (Sum.inr 2278, -4320), (Sum.inr 2290, -2160), (Sum.inr 3801, -2160), (Sum.inr 3812, -2160), (Sum.inr 3906, -4320), (Sum.inr 3910, -2160)]

theorem reindexCheck564 : Integer.Sparse.reindex keyMap MixedData.row564 = numericRow564 := by decide +kernel

theorem numericCheck564 (x : Master → ℝ) : Integer.Sparse.eval numericRow564 x =
    (8640 : ℝ) * reducedSource564 x := by
  norm_num [numericRow564, reducedSource564, Integer.Sparse.eval, Sparse.eval, nodeValue4252, nodeValue4253, nodeValue4255, nodeValue4268, nodeValue4729, nodeValue4731, nodeValue4740, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4839, nodeValue4864, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue4890, nodeValue4896, nodeValue5406, nodeValue5435, nodeValue5450, nodeValue5453]
  ring

noncomputable def reducedSource565 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((1 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue789 x + ((2 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((1 : ℝ) * Sparse.eval nodeValue1900 x + ((2 : ℝ) * Sparse.eval nodeValue1913 x + ((2 : ℝ) * Sparse.eval nodeValue2023 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((2 : ℝ) * Sparse.eval nodeValue2028 x + ((2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + 0))))))))))))))))))))

def numericRow565 : Integer.Sparse Master := [(Sum.inl 0, -28), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 50), (Sum.inr 786, 1080), (Sum.inr 787, 1080), (Sum.inr 789, 1080), (Sum.inr 811, 2160), (Sum.inr 1898, 1080), (Sum.inr 1900, 1080), (Sum.inr 1913, 2160), (Sum.inr 2023, 2160), (Sum.inr 2025, 2160), (Sum.inr 2028, 2160), (Sum.inr 2058, 2160), (Sum.inr 2241, 1080), (Sum.inr 2242, 1080), (Sum.inr 2245, 1080), (Sum.inr 2247, 1080), (Sum.inr 2260, 2160), (Sum.inr 2266, 2160), (Sum.inr 3801, 1080), (Sum.inr 3910, 1080)]

theorem reindexCheck565 : Integer.Sparse.reindex keyMap MixedData.row565 = numericRow565 := by decide +kernel

theorem numericCheck565 (x : Master → ℝ) : Integer.Sparse.eval numericRow565 x =
    (1080 : ℝ) * reducedSource565 x := by
  norm_num [numericRow565, reducedSource565, Integer.Sparse.eval, Sparse.eval, nodeValue786, nodeValue787, nodeValue789, nodeValue811, nodeValue1898, nodeValue1900, nodeValue1913, nodeValue2023, nodeValue2025, nodeValue2028, nodeValue2058, nodeValue2241, nodeValue2242, nodeValue2245, nodeValue2247, nodeValue2260, nodeValue2266, nodeValue3801, nodeValue3853, nodeValue3910, nodeValue3912]
  ring

noncomputable def reducedSource566 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4473 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((2 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((2 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

def numericRow566 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1079, -1080), (Sum.inr 1708, -1080), (Sum.inr 2051, -1080), (Sum.inr 2191, -1080), (Sum.inr 2244, -1080), (Sum.inr 2245, -2160), (Sum.inr 2262, -1080), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 3077, -1080), (Sum.inr 3625, -1080), (Sum.inr 3632, -2160), (Sum.inr 4473, 4320), (Sum.inr 4474, 4320), (Sum.inr 4475, 8640), (Sum.inr 4815, 4320), (Sum.inr 4816, 8640), (Sum.inr 4878, 4320), (Sum.inr 4879, 4320), (Sum.inr 4880, 8640), (Sum.inr 4885, 4320), (Sum.inr 4891, 8640), (Sum.inr 5251, 4320), (Sum.inr 5270, 4320)]

theorem reindexCheck566 : Integer.Sparse.reindex keyMap MixedData.row566 = numericRow566 := by decide +kernel

theorem numericCheck566 (x : Master → ℝ) : Integer.Sparse.eval numericRow566 x =
    (4320 : ℝ) * reducedSource566 x := by
  norm_num [numericRow566, reducedSource566, Integer.Sparse.eval, Sparse.eval, nodeValue4473, nodeValue4474, nodeValue4475, nodeValue4495, nodeValue4815, nodeValue4816, nodeValue4831, nodeValue4878, nodeValue4879, nodeValue4880, nodeValue4885, nodeValue4888, nodeValue4889, nodeValue4891, nodeValue4895, nodeValue4896, nodeValue4898, nodeValue5251, nodeValue5270, nodeValue5284, nodeValue5294]
  ring

noncomputable def reducedSource567 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1699 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue1709 x + ((2 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + 0))))))))))))))))))))

def numericRow567 : Integer.Sparse Master := [(Sum.inl 0, -94), (Sum.inl 2, 125), (Sum.inl 3, 160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 215), (Sum.inr 1699, 4320), (Sum.inr 1708, 4320), (Sum.inr 1709, 4320), (Sum.inr 1715, 8640), (Sum.inr 2191, 4320), (Sum.inr 2192, 4320), (Sum.inr 2196, 8640), (Sum.inr 2233, 4320), (Sum.inr 2234, 4320), (Sum.inr 2244, 4320), (Sum.inr 2245, 8640), (Sum.inr 2246, 4320), (Sum.inr 2253, 8640), (Sum.inr 2254, 8640), (Sum.inr 2266, 8640), (Sum.inr 2279, 8640), (Sum.inr 2710, 4320), (Sum.inr 2754, 4320)]

theorem reindexCheck567 : Integer.Sparse.reindex keyMap MixedData.row567 = numericRow567 := by decide +kernel

theorem numericCheck567 (x : Master → ℝ) : Integer.Sparse.eval numericRow567 x =
    (4320 : ℝ) * reducedSource567 x := by
  norm_num [numericRow567, reducedSource567, Integer.Sparse.eval, Sparse.eval, nodeValue1699, nodeValue1708, nodeValue1709, nodeValue1715, nodeValue2191, nodeValue2192, nodeValue2196, nodeValue2233, nodeValue2234, nodeValue2244, nodeValue2245, nodeValue2246, nodeValue2253, nodeValue2254, nodeValue2265, nodeValue2266, nodeValue2279, nodeValue2710, nodeValue2753, nodeValue2754, nodeValue2768]
  ring

noncomputable def reducedSource568 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1366 x + ((2 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((2 : ℝ) * Sparse.eval nodeValue3223 x + ((2 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

def numericRow568 : Integer.Sparse Master := [(Sum.inl 0, -118), (Sum.inl 2, 185), (Sum.inl 3, 160), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 155), (Sum.inr 1366, 1440), (Sum.inr 1367, 2880), (Sum.inr 1370, 1440), (Sum.inr 3064, 1440), (Sum.inr 3075, 1440), (Sum.inr 3077, 1440), (Sum.inr 3155, 1440), (Sum.inr 3156, 2880), (Sum.inr 3158, 1440), (Sum.inr 3196, 2880), (Sum.inr 3197, 1440), (Sum.inr 3221, 1440), (Sum.inr 3222, 2880)]

theorem reindexCheck568 : Integer.Sparse.reindex keyMap MixedData.row568 = numericRow568 := by decide +kernel

theorem numericCheck568 (x : Master → ℝ) : Integer.Sparse.eval numericRow568 x =
    (1440 : ℝ) * reducedSource568 x := by
  norm_num [numericRow568, reducedSource568, Integer.Sparse.eval, Sparse.eval, nodeValue1366, nodeValue1367, nodeValue1370, nodeValue1441, nodeValue3064, nodeValue3075, nodeValue3077, nodeValue3101, nodeValue3155, nodeValue3156, nodeValue3158, nodeValue3196, nodeValue3197, nodeValue3209, nodeValue3221, nodeValue3222, nodeValue3223, nodeValue3224, nodeValue3225, nodeValue3227, nodeValue3229]
  ring

noncomputable def reducedSource569 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow569 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 2), (Sum.inr 1079, 1), (Sum.inr 2277, 1), (Sum.inr 4084, -1)]

theorem reindexCheck569 : Integer.Sparse.reindex keyMap MixedData.row569 = numericRow569 := by decide +kernel

theorem numericCheck569 (x : Master → ℝ) : Integer.Sparse.eval numericRow569 x =
    (1 : ℝ) * reducedSource569 x := by
  norm_num [numericRow569, reducedSource569, Integer.Sparse.eval, Sparse.eval, nodeValue1056, nodeValue1057, nodeValue1058, nodeValue1079, nodeValue2277, nodeValue4084]

noncomputable def reducedSource570 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((2 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0))))))))))))))))))))

def numericRow570 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 1041, -1728), (Sum.inr 1724, -1728), (Sum.inr 2020, -1728), (Sum.inr 2107, -1728), (Sum.inr 2202, -1728), (Sum.inr 2243, -1728), (Sum.inr 2244, -864), (Sum.inr 2245, -864), (Sum.inr 2247, -864), (Sum.inr 2260, -1728), (Sum.inr 2262, -864), (Sum.inr 2277, -864), (Sum.inr 2290, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 4440, 3456), (Sum.inr 4444, 3456), (Sum.inr 4792, 3456), (Sum.inr 4795, 3456), (Sum.inr 4851, 6912), (Sum.inr 4853, 6912), (Sum.inr 4856, 6912), (Sum.inr 5289, 6912)]

theorem reindexCheck570 : Integer.Sparse.reindex keyMap MixedData.row570 = numericRow570 := by decide +kernel

theorem numericCheck570 (x : Master → ℝ) : Integer.Sparse.eval numericRow570 x =
    (3456 : ℝ) * reducedSource570 x := by
  norm_num [numericRow570, reducedSource570, Integer.Sparse.eval, Sparse.eval, nodeValue4438, nodeValue4440, nodeValue4444, nodeValue4458, nodeValue4792, nodeValue4795, nodeValue4802, nodeValue4851, nodeValue4853, nodeValue4856, nodeValue4866, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4890, nodeValue4893, nodeValue4895, nodeValue5256, nodeValue5289, nodeValue5292, nodeValue5306]
  ring

noncomputable def reducedSource571 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((2 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3172 x + ((2 : ℝ) * Sparse.eval nodeValue3174 x + ((2 : ℝ) * Sparse.eval nodeValue3184 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3226 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3228 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

def numericRow571 : Integer.Sparse Master := [(Sum.inl 0, -99), (Sum.inl 2, -140), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 1, -185), (Sum.inr 1388, 1080), (Sum.inr 1391, 1080), (Sum.inr 2471, 1080), (Sum.inr 2486, 2160), (Sum.inr 3097, 2160), (Sum.inr 3172, 2160), (Sum.inr 3174, 2160), (Sum.inr 3199, 1080)]

theorem reindexCheck571 : Integer.Sparse.reindex keyMap MixedData.row571 = numericRow571 := by decide +kernel

theorem numericCheck571 (x : Master → ℝ) : Integer.Sparse.eval numericRow571 x =
    (1080 : ℝ) * reducedSource571 x := by
  norm_num [numericRow571, reducedSource571, Integer.Sparse.eval, Sparse.eval, nodeValue1386, nodeValue1388, nodeValue1391, nodeValue1411, nodeValue2471, nodeValue2486, nodeValue2755, nodeValue3085, nodeValue3097, nodeValue3100, nodeValue3120, nodeValue3172, nodeValue3174, nodeValue3184, nodeValue3199, nodeValue3204, nodeValue3223, nodeValue3226, nodeValue3227, nodeValue3228, nodeValue3229]
  ring

noncomputable def reducedSource572 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + 0))))))))))))))))))))

def numericRow572 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, -13), (Sum.inl 3, 16), (Sum.inl 1, -40), (Sum.inr 1723, 864), (Sum.inr 1724, 1728), (Sum.inr 1736, 864), (Sum.inr 2201, 864), (Sum.inr 2202, 1728), (Sum.inr 2213, 864), (Sum.inr 2240, 1728), (Sum.inr 2243, 864), (Sum.inr 2259, 1728), (Sum.inr 2260, 1728), (Sum.inr 2262, 864), (Sum.inr 2274, 1728), (Sum.inr 2277, 864), (Sum.inr 2290, 864), (Sum.inr 2763, 1728)]

theorem reindexCheck572 : Integer.Sparse.reindex keyMap MixedData.row572 = numericRow572 := by decide +kernel

theorem numericCheck572 (x : Master → ℝ) : Integer.Sparse.eval numericRow572 x =
    (864 : ℝ) * reducedSource572 x := by
  norm_num [numericRow572, reducedSource572, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1723, nodeValue1724, nodeValue1736, nodeValue2201, nodeValue2202, nodeValue2213, nodeValue2240, nodeValue2243, nodeValue2259, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2274, nodeValue2277, nodeValue2290, nodeValue2291, nodeValue2720, nodeValue2763, nodeValue2766, nodeValue2784]
  ring

noncomputable def reducedSource573 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow573 : Integer.Sparse Master := [(Sum.inr 2244, 1), (Sum.inr 3572, 2), (Sum.inr 3622, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem reindexCheck573 : Integer.Sparse.reindex keyMap MixedData.row573 = numericRow573 := by decide +kernel

theorem numericCheck573 (x : Master → ℝ) : Integer.Sparse.eval numericRow573 x =
    (1 : ℝ) * reducedSource573 x := by
  norm_num [numericRow573, reducedSource573, Integer.Sparse.eval, Sparse.eval, nodeValue2244, nodeValue3525, nodeValue3572, nodeValue3622, nodeValue3623, nodeValue4083]

noncomputable def reducedSource574 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow574 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 2), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

theorem reindexCheck574 : Integer.Sparse.reindex keyMap MixedData.row574 = numericRow574 := by decide +kernel

theorem numericCheck574 (x : Master → ℝ) : Integer.Sparse.eval numericRow574 x =
    (1 : ℝ) * reducedSource574 x := by
  norm_num [numericRow574, reducedSource574, Integer.Sparse.eval, Sparse.eval, nodeValue1020, nodeValue1022, nodeValue1026, nodeValue1041, nodeValue2244, nodeValue4083]

noncomputable def reducedSource575 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow575 : Integer.Sparse Master := [(Sum.inr 1041, 1), (Sum.inr 2020, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

theorem reindexCheck575 : Integer.Sparse.reindex keyMap MixedData.row575 = numericRow575 := by decide +kernel

theorem numericCheck575 (x : Master → ℝ) : Integer.Sparse.eval numericRow575 x =
    (1 : ℝ) * reducedSource575 x := by
  norm_num [numericRow575, reducedSource575, Integer.Sparse.eval, Sparse.eval, nodeValue1041, nodeValue2020, nodeValue2107, nodeValue2244, nodeValue2263, nodeValue2265, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
