import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource112 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1094 x + ((3 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow112 : Integer.Sparse Master := [(Sum.inr 1094, 1), (Sum.inr 2065, 3), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem reindexCheck112 : Integer.Sparse.reindex keyMap MixedData.row112 = numericRow112 := by decide +kernel

theorem numericCheck112 (x : Master → ℝ) : Integer.Sparse.eval numericRow112 x =
    (1 : ℝ) * reducedSource112 x := by
  norm_num [numericRow112, reducedSource112, Integer.Sparse.eval, Sparse.eval, nodeValue1094, nodeValue2065, nodeValue2292, nodeValue2294, nodeValue4085]

noncomputable def reducedSource113 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4270 x + ((2 : ℝ) * Sparse.eval nodeValue4583 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4729 x + ((4 : ℝ) * Sparse.eval nodeValue4742 x + ((4 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4843 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0)))))))))))))

def numericRow113 : Integer.Sparse Master := [(Sum.inl 0, 39), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 20), (Sum.inr 787, -2160), (Sum.inr 791, -1080), (Sum.inr 813, -2160), (Sum.inr 847, -2160), (Sum.inr 849, -1080), (Sum.inr 853, -2160), (Sum.inr 1202, -2160), (Sum.inr 1239, -2160), (Sum.inr 1898, -2160), (Sum.inr 1915, -4320), (Sum.inr 1940, -2160), (Sum.inr 1942, -2160), (Sum.inr 1946, -4320), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2245, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 3077, -2160), (Sum.inr 3625, -2160), (Sum.inr 3632, -2160)]

theorem reindexCheck113 : Integer.Sparse.reindex keyMap MixedData.row113 = numericRow113 := by decide +kernel

theorem numericCheck113 (x : Master → ℝ) : Integer.Sparse.eval numericRow113 x =
    (4320 : ℝ) * reducedSource113 x := by
  norm_num [numericRow113, reducedSource113, Integer.Sparse.eval, Sparse.eval, nodeValue4253, nodeValue4257, nodeValue4270, nodeValue4583, nodeValue4605, nodeValue4729, nodeValue4742, nodeValue4807, nodeValue4843, nodeValue4889, nodeValue4896, nodeValue5284, nodeValue5294, nodeValue5453]; ring

noncomputable def reducedSource114 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue813 x + ((2 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1898 x + ((4 : ℝ) * Sparse.eval nodeValue1915 x + ((4 : ℝ) * Sparse.eval nodeValue2025 x + ((2 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + 0)))))))))))))

def numericRow114 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 10), (Sum.inr 787, 2160), (Sum.inr 791, 1080), (Sum.inr 813, 2160), (Sum.inr 1202, 2160), (Sum.inr 1239, 2160), (Sum.inr 1898, 2160), (Sum.inr 1915, 4320), (Sum.inr 2025, 4320), (Sum.inr 2062, 2160), (Sum.inr 2245, 2160), (Sum.inr 2266, 2160), (Sum.inr 3077, 2160)]

theorem reindexCheck114 : Integer.Sparse.reindex keyMap MixedData.row114 = numericRow114 := by decide +kernel

theorem numericCheck114 (x : Master → ℝ) : Integer.Sparse.eval numericRow114 x =
    (1080 : ℝ) * reducedSource114 x := by
  norm_num [numericRow114, reducedSource114, Integer.Sparse.eval, Sparse.eval, nodeValue787, nodeValue791, nodeValue813, nodeValue1202, nodeValue1239, nodeValue1898, nodeValue1915, nodeValue2025, nodeValue2062, nodeValue2245, nodeValue2266, nodeValue3077, nodeValue3101, nodeValue3912]; ring

noncomputable def reducedSource115 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4440 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4445 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4464 x + ((2 : ℝ) * Sparse.eval nodeValue4792 x + ((4 : ℝ) * Sparse.eval nodeValue4807 x + ((4 : ℝ) * Sparse.eval nodeValue4853 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((2 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + 0)))))))))))))

def numericRow115 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 1046, -4320), (Sum.inr 1750, -4320), (Sum.inr 2025, -8640), (Sum.inr 2112, -4320), (Sum.inr 2224, -8640), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2287, -4320), (Sum.inr 3623, -2160), (Sum.inr 4440, 17280), (Sum.inr 4442, 17280), (Sum.inr 4445, 8640), (Sum.inr 4464, 17280), (Sum.inr 4792, 17280), (Sum.inr 4853, 34560), (Sum.inr 5270, 17280), (Sum.inr 5295, 17280)]

theorem reindexCheck115 : Integer.Sparse.reindex keyMap MixedData.row115 = numericRow115 := by decide +kernel

theorem numericCheck115 (x : Master → ℝ) : Integer.Sparse.eval numericRow115 x =
    (8640 : ℝ) * reducedSource115 x := by
  norm_num [numericRow115, reducedSource115, Integer.Sparse.eval, Sparse.eval, nodeValue4440, nodeValue4442, nodeValue4445, nodeValue4463, nodeValue4464, nodeValue4792, nodeValue4807, nodeValue4853, nodeValue4871, nodeValue4888, nodeValue4895, nodeValue5270, nodeValue5295, nodeValue5306]; ring

noncomputable def reducedSource116 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1047 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue2471 x + ((4 : ℝ) * Sparse.eval nodeValue2486 x + ((4 : ℝ) * Sparse.eval nodeValue2574 x + ((2 : ℝ) * Sparse.eval nodeValue2602 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((2 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))

def numericRow116 : Integer.Sparse Master := [(Sum.inl 0, -52), (Sum.inl 2, 15), (Sum.inl 13, -80), (Sum.inl 1, -105), (Sum.inr 1024, 1440), (Sum.inr 1027, 720), (Sum.inr 1047, 1440), (Sum.inr 1388, 1440), (Sum.inr 2471, 1440), (Sum.inr 2486, 2880), (Sum.inr 2754, 1440), (Sum.inr 2769, 1440)]

theorem reindexCheck116 : Integer.Sparse.reindex keyMap MixedData.row116 = numericRow116 := by decide +kernel

theorem numericCheck116 (x : Master → ℝ) : Integer.Sparse.eval numericRow116 x =
    (720 : ℝ) * reducedSource116 x := by
  norm_num [numericRow116, reducedSource116, Integer.Sparse.eval, Sparse.eval, nodeValue1024, nodeValue1027, nodeValue1047, nodeValue1388, nodeValue1413, nodeValue2471, nodeValue2486, nodeValue2574, nodeValue2602, nodeValue2754, nodeValue2769, nodeValue3120, nodeValue3227, nodeValue3229]; ring

noncomputable def reducedSource117 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1744 x + ((2 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((2 : ℝ) * Sparse.eval nodeValue2201 x + ((4 : ℝ) * Sparse.eval nodeValue2224 x + ((4 : ℝ) * Sparse.eval nodeValue2259 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2287 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + 0)))))))))))))

def numericRow117 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1723, 4320), (Sum.inr 1744, 4320), (Sum.inr 1745, 4320), (Sum.inr 1749, 2160), (Sum.inr 1750, 4320), (Sum.inr 2201, 4320), (Sum.inr 2224, 8640), (Sum.inr 2259, 8640), (Sum.inr 2262, 4320), (Sum.inr 2287, 4320), (Sum.inr 2738, 4320), (Sum.inr 2781, 4320)]

theorem reindexCheck117 : Integer.Sparse.reindex keyMap MixedData.row117 = numericRow117 := by decide +kernel

theorem numericCheck117 (x : Master → ℝ) : Integer.Sparse.eval numericRow117 x =
    (2160 : ℝ) * reducedSource117 x := by
  norm_num [numericRow117, reducedSource117, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1744, nodeValue1745, nodeValue1749, nodeValue1750, nodeValue2201, nodeValue2224, nodeValue2259, nodeValue2262, nodeValue2287, nodeValue2291, nodeValue2738, nodeValue2781, nodeValue2784]; ring

noncomputable def reducedSource118 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow118 : Integer.Sparse Master := [(Sum.inr 2244, 2), (Sum.inr 2247, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem reindexCheck118 : Integer.Sparse.reindex keyMap MixedData.row118 = numericRow118 := by decide +kernel

theorem numericCheck118 (x : Master → ℝ) : Integer.Sparse.eval numericRow118 x =
    (1 : ℝ) * reducedSource118 x := by
  norm_num [numericRow118, reducedSource118, Integer.Sparse.eval, Sparse.eval, nodeValue2244, nodeValue2247, nodeValue2265, nodeValue3623, nodeValue4083]

noncomputable def reducedSource119 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1385 x + ((2 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow119 : Integer.Sparse Master := [(Sum.inr 1027, 1), (Sum.inr 1385, 2), (Sum.inr 1408, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem reindexCheck119 : Integer.Sparse.reindex keyMap MixedData.row119 = numericRow119 := by decide +kernel

theorem numericCheck119 (x : Master → ℝ) : Integer.Sparse.eval numericRow119 x =
    (1 : ℝ) * reducedSource119 x := by
  norm_num [numericRow119, reducedSource119, Integer.Sparse.eval, Sparse.eval, nodeValue1027, nodeValue1385, nodeValue1408, nodeValue2247, nodeValue4083]

noncomputable def reducedSource120 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow120 : Integer.Sparse Master := [(Sum.inr 1385, 1), (Sum.inr 2009, 1), (Sum.inr 2025, 2), (Sum.inr 2247, 1), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

theorem reindexCheck120 : Integer.Sparse.reindex keyMap MixedData.row120 = numericRow120 := by decide +kernel

theorem numericCheck120 (x : Master → ℝ) : Integer.Sparse.eval numericRow120 x =
    (1 : ℝ) * reducedSource120 x := by
  norm_num [numericRow120, reducedSource120, Integer.Sparse.eval, Sparse.eval, nodeValue1385, nodeValue2009, nodeValue2025, nodeValue2247, nodeValue3075, nodeValue4083]

noncomputable def reducedSource121 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow121 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 2009, 1), (Sum.inr 2090, 2), (Sum.inr 2244, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem reindexCheck121 : Integer.Sparse.reindex keyMap MixedData.row121 = numericRow121 := by decide +kernel

theorem numericCheck121 (x : Master → ℝ) : Integer.Sparse.eval numericRow121 x =
    (1 : ℝ) * reducedSource121 x := by
  norm_num [numericRow121, reducedSource121, Integer.Sparse.eval, Sparse.eval, nodeValue1022, nodeValue2009, nodeValue2090, nodeValue2244, nodeValue2247, nodeValue4083]

noncomputable def reducedSource122 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow122 : Integer.Sparse Master := [(Sum.inr 1408, 1), (Sum.inr 2090, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem reindexCheck122 : Integer.Sparse.reindex keyMap MixedData.row122 = numericRow122 := by decide +kernel

theorem numericCheck122 (x : Master → ℝ) : Integer.Sparse.eval numericRow122 x =
    (1 : ℝ) * reducedSource122 x := by
  norm_num [numericRow122, reducedSource122, Integer.Sparse.eval, Sparse.eval, nodeValue1408, nodeValue2090, nodeValue2112, nodeValue2247, nodeValue3098, nodeValue4083]

noncomputable def reducedSource123 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1046 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow123 : Integer.Sparse Master := [(Sum.inr 1046, 1), (Sum.inr 2025, 2), (Sum.inr 2112, 1), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem reindexCheck123 : Integer.Sparse.reindex keyMap MixedData.row123 = numericRow123 := by decide +kernel

theorem numericCheck123 (x : Master → ℝ) : Integer.Sparse.eval numericRow123 x =
    (1 : ℝ) * reducedSource123 x := by
  norm_num [numericRow123, reducedSource123, Integer.Sparse.eval, Sparse.eval, nodeValue1046, nodeValue2025, nodeValue2112, nodeValue2247, nodeValue2265, nodeValue4083]

noncomputable def reducedSource124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow124 : Integer.Sparse Master := [(Sum.inr 1022, 2), (Sum.inr 1027, 1), (Sum.inr 1046, 2), (Sum.inr 2247, 1), (Sum.inr 4083, -1)]

theorem reindexCheck124 : Integer.Sparse.reindex keyMap MixedData.row124 = numericRow124 := by decide +kernel

theorem numericCheck124 (x : Master → ℝ) : Integer.Sparse.eval numericRow124 x =
    (1 : ℝ) * reducedSource124 x := by
  norm_num [numericRow124, reducedSource124, Integer.Sparse.eval, Sparse.eval, nodeValue1022, nodeValue1027, nodeValue1046, nodeValue2247, nodeValue4083]

noncomputable def reducedSource125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4494 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4500 x + ((2 : ℝ) * Sparse.eval nodeValue4830 x + ((2 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4836 x + ((2 : ℝ) * Sparse.eval nodeValue4886 x + ((5 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4892 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

def numericRow125 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1080, -60), (Sum.inr 1710, -60), (Sum.inr 2052, -120), (Sum.inr 2193, -120), (Sum.inr 2247, -300), (Sum.inr 2281, -120), (Sum.inr 2290, -300), (Sum.inr 2294, -120), (Sum.inr 3634, -120), (Sum.inr 4494, 480), (Sum.inr 4500, 480), (Sum.inr 4830, 480), (Sum.inr 4836, 960), (Sum.inr 4886, 480), (Sum.inr 4892, 480), (Sum.inr 5252, 480)]

theorem reindexCheck125 : Integer.Sparse.reindex keyMap MixedData.row125 = numericRow125 := by decide +kernel

theorem numericCheck125 (x : Master → ℝ) : Integer.Sparse.eval numericRow125 x =
    (240 : ℝ) * reducedSource125 x := by
  norm_num [numericRow125, reducedSource125, Integer.Sparse.eval, Sparse.eval, nodeValue4494, nodeValue4496, nodeValue4500, nodeValue4830, nodeValue4832, nodeValue4836, nodeValue4886, nodeValue4890, nodeValue4892, nodeValue4897, nodeValue4899, nodeValue5252, nodeValue5296]; ring

noncomputable def reducedSource126 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1435 x + ((2 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + ((2 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue2707 x + ((2 : ℝ) * Sparse.eval nodeValue2712 x + ((4 : ℝ) * Sparse.eval nodeValue2716 x + ((4 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3082 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + 0)))))))))))))

def numericRow126 : Integer.Sparse Master := [(Sum.inl 0, -58), (Sum.inl 2, -285), (Sum.inl 13, -80), (Sum.inl 1, -15), (Sum.inr 1435, 1440), (Sum.inr 1436, 1440), (Sum.inr 2235, 1440), (Sum.inr 2247, 720), (Sum.inr 2255, 1440), (Sum.inr 2707, 1440), (Sum.inr 2712, 1440), (Sum.inr 2716, 2880)]

theorem reindexCheck126 : Integer.Sparse.reindex keyMap MixedData.row126 = numericRow126 := by decide +kernel

theorem numericCheck126 (x : Master → ℝ) : Integer.Sparse.eval numericRow126 x =
    (720 : ℝ) * reducedSource126 x := by
  norm_num [numericRow126, reducedSource126, Integer.Sparse.eval, Sparse.eval, nodeValue1435, nodeValue1436, nodeValue1451, nodeValue2235, nodeValue2247, nodeValue2255, nodeValue2707, nodeValue2712, nodeValue2716, nodeValue2755, nodeValue2770, nodeValue2778, nodeValue3082, nodeValue3114]; ring

noncomputable def reducedSource127 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1700 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((2 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2187 x + ((2 : ℝ) * Sparse.eval nodeValue2193 x + ((4 : ℝ) * Sparse.eval nodeValue2197 x + ((2 : ℝ) * Sparse.eval nodeValue2235 x + ((4 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((2 : ℝ) * Sparse.eval nodeValue2281 x + ((2 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + 0)))))))))))))

def numericRow127 : Integer.Sparse Master := [(Sum.inl 0, -10), (Sum.inl 2, -51), (Sum.inl 13, 16), (Sum.inl 1, 3), (Sum.inr 1700, 864), (Sum.inr 1710, 432), (Sum.inr 1716, 864), (Sum.inr 2187, 864), (Sum.inr 2193, 864), (Sum.inr 2197, 1728), (Sum.inr 2235, 864), (Sum.inr 2247, 1728), (Sum.inr 2255, 864), (Sum.inr 2281, 864), (Sum.inr 2712, 864)]

theorem reindexCheck127 : Integer.Sparse.reindex keyMap MixedData.row127 = numericRow127 := by decide +kernel

theorem numericCheck127 (x : Master → ℝ) : Integer.Sparse.eval numericRow127 x =
    (432 : ℝ) * reducedSource127 x := by
  norm_num [numericRow127, reducedSource127, Integer.Sparse.eval, Sparse.eval, nodeValue1700, nodeValue1710, nodeValue1716, nodeValue2187, nodeValue2193, nodeValue2197, nodeValue2235, nodeValue2247, nodeValue2255, nodeValue2268, nodeValue2281, nodeValue2712, nodeValue2755, nodeValue2770]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
