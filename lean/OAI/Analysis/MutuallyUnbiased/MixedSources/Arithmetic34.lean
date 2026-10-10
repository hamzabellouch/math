import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
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

noncomputable def reducedSource544 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow544 : Integer.Sparse Master := [(Sum.inr 1087, 1), (Sum.inr 2058, 2), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

theorem reindexCheck544 : Integer.Sparse.reindex keyMap MixedData.row544 = numericRow544 := by decide +kernel

theorem numericCheck544 (x : Master → ℝ) : Integer.Sparse.eval numericRow544 x =
    (1 : ℝ) * reducedSource544 x := by
  norm_num [numericRow544, reducedSource544, Integer.Sparse.eval, Sparse.eval, nodeValue1087, nodeValue2058, nodeValue2266, nodeValue2279, nodeValue2291, nodeValue4084]

noncomputable def reducedSource545 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4275 x + ((2 : ℝ) * Sparse.eval nodeValue4276 x + ((1 : ℝ) * Sparse.eval nodeValue4278 x + ((2 : ℝ) * Sparse.eval nodeValue4746 x + ((4 : ℝ) * Sparse.eval nodeValue4747 x + ((2 : ℝ) * Sparse.eval nodeValue4749 x + ((4 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0)))))))))))))

def numericRow545 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 160), (Sum.inl 1, 230), (Sum.inr 827, -4320), (Sum.inr 828, -2160), (Sum.inr 830, -2160), (Sum.inr 857, -2160), (Sum.inr 1925, -4320), (Sum.inr 1926, -4320), (Sum.inr 1928, -4320), (Sum.inr 1948, -4320), (Sum.inr 2110, -4320), (Sum.inr 2112, -2160), (Sum.inr 2115, -2160), (Sum.inr 2275, -4320), (Sum.inr 2276, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -2160), (Sum.inr 2287, -2160), (Sum.inr 2294, -2160), (Sum.inr 3814, -4320), (Sum.inr 3907, -2160)]

theorem reindexCheck545 : Integer.Sparse.reindex keyMap MixedData.row545 = numericRow545 := by decide +kernel

theorem numericCheck545 (x : Master → ℝ) : Integer.Sparse.eval numericRow545 x =
    (4320 : ℝ) * reducedSource545 x := by
  norm_num [numericRow545, reducedSource545, Integer.Sparse.eval, Sparse.eval, nodeValue4275, nodeValue4276, nodeValue4278, nodeValue4746, nodeValue4747, nodeValue4749, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue4899, nodeValue5412, nodeValue5443, nodeValue5456]
  ring

noncomputable def reducedSource546 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4480 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4817 x + ((2 : ℝ) * Sparse.eval nodeValue4821 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

def numericRow546 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -20), (Sum.inl 3, 80), (Sum.inl 1, -5), (Sum.inr 1083, -1080), (Sum.inr 1728, -1080), (Sum.inr 2054, -2160), (Sum.inr 2206, -2160), (Sum.inr 2245, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -2160), (Sum.inr 2281, -1080), (Sum.inr 2294, -1080), (Sum.inr 3632, -1080), (Sum.inr 3633, -1080), (Sum.inr 4474, 8640), (Sum.inr 4476, 4320), (Sum.inr 4480, 4320), (Sum.inr 4815, 8640), (Sum.inr 4817, 8640), (Sum.inr 4821, 8640), (Sum.inr 4879, 8640), (Sum.inr 4881, 4320), (Sum.inr 4884, 4320), (Sum.inr 5260, 8640), (Sum.inr 5295, 4320)]

theorem reindexCheck546 : Integer.Sparse.reindex keyMap MixedData.row546 = numericRow546 := by decide +kernel

theorem numericCheck546 (x : Master → ℝ) : Integer.Sparse.eval numericRow546 x =
    (4320 : ℝ) * reducedSource546 x := by
  norm_num [numericRow546, reducedSource546, Integer.Sparse.eval, Sparse.eval, nodeValue4474, nodeValue4476, nodeValue4480, nodeValue4499, nodeValue4815, nodeValue4817, nodeValue4821, nodeValue4835, nodeValue4879, nodeValue4881, nodeValue4884, nodeValue4889, nodeValue4895, nodeValue4896, nodeValue4898, nodeValue4899, nodeValue4901, nodeValue5260, nodeValue5294, nodeValue5295, nodeValue5310]
  ring

noncomputable def reducedSource547 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue1443 x + ((2 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((2 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3198 x + ((2 : ℝ) * Sparse.eval nodeValue3211 x + ((2 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))))))))))

def numericRow547 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 50), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, 35), (Sum.inr 1370, 1440), (Sum.inr 1372, 720), (Sum.inr 1375, 720), (Sum.inr 2497, 1440), (Sum.inr 2520, 720), (Sum.inr 3086, 1440), (Sum.inr 3098, 720), (Sum.inr 3158, 1440), (Sum.inr 3161, 720), (Sum.inr 3197, 1440), (Sum.inr 3198, 1440)]

theorem reindexCheck547 : Integer.Sparse.reindex keyMap MixedData.row547 = numericRow547 := by decide +kernel

theorem numericCheck547 (x : Master → ℝ) : Integer.Sparse.eval numericRow547 x =
    (720 : ℝ) * reducedSource547 x := by
  norm_num [numericRow547, reducedSource547, Integer.Sparse.eval, Sparse.eval, nodeValue1370, nodeValue1372, nodeValue1375, nodeValue1443, nodeValue2497, nodeValue2520, nodeValue2778, nodeValue3086, nodeValue3098, nodeValue3101, nodeValue3121, nodeValue3158, nodeValue3161, nodeValue3197, nodeValue3198, nodeValue3211, nodeValue3223, nodeValue3224, nodeValue3225, nodeValue3229, nodeValue3231]
  ring

noncomputable def reducedSource548 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1709 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((2 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2207 x + ((2 : ℝ) * Sparse.eval nodeValue2217 x + ((2 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + 0))))))))))))))))))))

def numericRow548 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 20), (Sum.inl 3, -80), (Sum.inl 1, 5), (Sum.inr 1709, 2160), (Sum.inr 1728, 1080), (Sum.inr 1729, 1080), (Sum.inr 1740, 1080), (Sum.inr 2192, 2160), (Sum.inr 2206, 2160), (Sum.inr 2207, 2160), (Sum.inr 2217, 2160), (Sum.inr 2245, 2160), (Sum.inr 2246, 2160), (Sum.inr 2266, 2160), (Sum.inr 2267, 1080), (Sum.inr 2279, 1080), (Sum.inr 2280, 1080), (Sum.inr 2294, 1080), (Sum.inr 2724, 2160), (Sum.inr 2769, 1080)]

theorem reindexCheck548 : Integer.Sparse.reindex keyMap MixedData.row548 = numericRow548 := by decide +kernel

theorem numericCheck548 (x : Master → ℝ) : Integer.Sparse.eval numericRow548 x =
    (1080 : ℝ) * reducedSource548 x := by
  norm_num [numericRow548, reducedSource548, Integer.Sparse.eval, Sparse.eval, nodeValue1709, nodeValue1728, nodeValue1729, nodeValue1740, nodeValue2192, nodeValue2206, nodeValue2207, nodeValue2217, nodeValue2245, nodeValue2246, nodeValue2265, nodeValue2266, nodeValue2267, nodeValue2279, nodeValue2280, nodeValue2293, nodeValue2294, nodeValue2724, nodeValue2768, nodeValue2769, nodeValue2788]
  ring

noncomputable def reducedSource549 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow549 : Integer.Sparse Master := [(Sum.inr 1057, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

theorem reindexCheck549 : Integer.Sparse.reindex keyMap MixedData.row549 = numericRow549 := by decide +kernel

theorem numericCheck549 (x : Master → ℝ) : Integer.Sparse.eval numericRow549 x =
    (1 : ℝ) * reducedSource549 x := by
  norm_num [numericRow549, reducedSource549, Integer.Sparse.eval, Sparse.eval, nodeValue1057, nodeValue1059, nodeValue1063, nodeValue1083, nodeValue2278, nodeValue4084]

noncomputable def reducedSource550 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow550 : Integer.Sparse Master := [(Sum.inr 1083, 1), (Sum.inr 2054, 2), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

theorem reindexCheck550 : Integer.Sparse.reindex keyMap MixedData.row550 = numericRow550 := by decide +kernel

theorem numericCheck550 (x : Master → ℝ) : Integer.Sparse.eval numericRow550 x =
    (1 : ℝ) * reducedSource550 x := by
  norm_num [numericRow550, reducedSource550, Integer.Sparse.eval, Sparse.eval, nodeValue1083, nodeValue2054, nodeValue2278, nodeValue2291, nodeValue2293, nodeValue4084]

noncomputable def reducedSource551 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4272 x + ((1 : ℝ) * Sparse.eval nodeValue4279 x + ((2 : ℝ) * Sparse.eval nodeValue4740 x + ((2 : ℝ) * Sparse.eval nodeValue4742 x + ((2 : ℝ) * Sparse.eval nodeValue4744 x + ((2 : ℝ) * Sparse.eval nodeValue4750 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + 0))))))))))))))))))))

def numericRow551 : Integer.Sparse Master := [(Sum.inl 0, 73), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -240), (Sum.inl 4, -80), (Sum.inl 1, 145), (Sum.inr 811, -4320), (Sum.inr 813, -2160), (Sum.inr 815, -2160), (Sum.inr 824, -4320), (Sum.inr 826, -2160), (Sum.inr 831, -2160), (Sum.inr 853, -2160), (Sum.inr 858, -2160), (Sum.inr 1913, -4320), (Sum.inr 1915, -4320), (Sum.inr 1917, -4320), (Sum.inr 1922, -4320), (Sum.inr 1924, -4320), (Sum.inr 1929, -4320), (Sum.inr 1946, -4320), (Sum.inr 1949, -4320), (Sum.inr 2058, -4320), (Sum.inr 2062, -2160), (Sum.inr 2065, -2160), (Sum.inr 2107, -4320), (Sum.inr 2109, -2160), (Sum.inr 2116, -2160), (Sum.inr 2216, -4320), (Sum.inr 2218, -2160), (Sum.inr 2230, -2160), (Sum.inr 2245, -4320), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2261, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -4320), (Sum.inr 2278, -2160), (Sum.inr 2288, -2160), (Sum.inr 2290, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160)]

theorem reindexCheck551 : Integer.Sparse.reindex keyMap MixedData.row551 = numericRow551 := by decide +kernel

theorem numericCheck551 (x : Master → ℝ) : Integer.Sparse.eval numericRow551 x =
    (8640 : ℝ) * reducedSource551 x := by
  norm_num [numericRow551, reducedSource551, Integer.Sparse.eval, Sparse.eval, nodeValue4268, nodeValue4270, nodeValue4272, nodeValue4279, nodeValue4740, nodeValue4742, nodeValue4744, nodeValue4750, nodeValue4839, nodeValue4843, nodeValue4845, nodeValue4866, nodeValue4868, nodeValue4875, nodeValue4889, nodeValue4890, nodeValue4896, nodeValue5411, nodeValue5443, nodeValue5451, nodeValue5453]
  ring

noncomputable def reducedSource552 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((2 : ℝ) * Sparse.eval nodeValue1922 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((2 : ℝ) * Sparse.eval nodeValue1929 x + ((2 : ℝ) * Sparse.eval nodeValue1946 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3915 x + 0))))))))))))))))))))

def numericRow552 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 824, 4320), (Sum.inr 826, 2160), (Sum.inr 831, 2160), (Sum.inr 853, 2160), (Sum.inr 1922, 4320), (Sum.inr 1924, 4320), (Sum.inr 1929, 4320), (Sum.inr 1946, 4320), (Sum.inr 2107, 4320), (Sum.inr 2109, 2160), (Sum.inr 2116, 2160), (Sum.inr 2216, 4320), (Sum.inr 2218, 2160), (Sum.inr 2230, 2160), (Sum.inr 2277, 4320), (Sum.inr 2278, 2160), (Sum.inr 2290, 2160), (Sum.inr 3813, 4320), (Sum.inr 3907, 2160)]

theorem reindexCheck552 : Integer.Sparse.reindex keyMap MixedData.row552 = numericRow552 := by decide +kernel

theorem numericCheck552 (x : Master → ℝ) : Integer.Sparse.eval numericRow552 x =
    (2160 : ℝ) * reducedSource552 x := by
  norm_num [numericRow552, reducedSource552, Integer.Sparse.eval, Sparse.eval, nodeValue824, nodeValue826, nodeValue831, nodeValue853, nodeValue1922, nodeValue1924, nodeValue1929, nodeValue1946, nodeValue2107, nodeValue2109, nodeValue2116, nodeValue2216, nodeValue2218, nodeValue2230, nodeValue2277, nodeValue2278, nodeValue2290, nodeValue3813, nodeValue3888, nodeValue3907, nodeValue3915]
  ring

noncomputable def reducedSource553 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((1 : ℝ) * Sparse.eval nodeValue4892 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

def numericRow553 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1049, -360), (Sum.inr 1087, -360), (Sum.inr 1738, -360), (Sum.inr 1739, -360), (Sum.inr 2028, -720), (Sum.inr 2058, -720), (Sum.inr 2115, -360), (Sum.inr 2215, -720), (Sum.inr 2216, -720), (Sum.inr 2244, -720), (Sum.inr 2262, -720), (Sum.inr 2276, -360), (Sum.inr 2279, -720), (Sum.inr 3054, -360), (Sum.inr 3626, -360), (Sum.inr 3627, -360), (Sum.inr 4459, 2880), (Sum.inr 4464, 1440), (Sum.inr 4803, 2880), (Sum.inr 4808, 2880), (Sum.inr 4867, 2880), (Sum.inr 4872, 1440), (Sum.inr 4891, 2880), (Sum.inr 4892, 1440), (Sum.inr 5266, 2880), (Sum.inr 5300, 1440)]

theorem reindexCheck553 : Integer.Sparse.reindex keyMap MixedData.row553 = numericRow553 := by decide +kernel

theorem numericCheck553 (x : Master → ℝ) : Integer.Sparse.eval numericRow553 x =
    (1440 : ℝ) * reducedSource553 x := by
  norm_num [numericRow553, reducedSource553, Integer.Sparse.eval, Sparse.eval, nodeValue4459, nodeValue4464, nodeValue4466, nodeValue4503, nodeValue4803, nodeValue4808, nodeValue4810, nodeValue4839, nodeValue4867, nodeValue4872, nodeValue4874, nodeValue4888, nodeValue4891, nodeValue4892, nodeValue4894, nodeValue4895, nodeValue4898, nodeValue5266, nodeValue5293, nodeValue5300, nodeValue5302]
  ring

noncomputable def reducedSource554 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + 0))))))))))))))))))))

def numericRow554 : Integer.Sparse Master := [(Sum.inl 0, -35), (Sum.inl 2, 40), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, -5), (Sum.inr 1714, 4320), (Sum.inr 1738, 2160), (Sum.inr 1739, 2160), (Sum.inr 1745, 2160), (Sum.inr 2195, 4320), (Sum.inr 2215, 4320), (Sum.inr 2216, 4320), (Sum.inr 2220, 4320), (Sum.inr 2244, 4320), (Sum.inr 2251, 4320), (Sum.inr 2253, 4320), (Sum.inr 2276, 2160), (Sum.inr 2279, 2160), (Sum.inr 2282, 2160), (Sum.inr 2284, 2160), (Sum.inr 2731, 4320), (Sum.inr 2774, 2160)]

theorem reindexCheck554 : Integer.Sparse.reindex keyMap MixedData.row554 = numericRow554 := by decide +kernel

theorem numericCheck554 (x : Master → ℝ) : Integer.Sparse.eval numericRow554 x =
    (2160 : ℝ) * reducedSource554 x := by
  norm_num [numericRow554, reducedSource554, Integer.Sparse.eval, Sparse.eval, nodeValue1714, nodeValue1738, nodeValue1739, nodeValue1745, nodeValue2195, nodeValue2215, nodeValue2216, nodeValue2220, nodeValue2244, nodeValue2251, nodeValue2253, nodeValue2264, nodeValue2265, nodeValue2276, nodeValue2279, nodeValue2282, nodeValue2284, nodeValue2731, nodeValue2767, nodeValue2774, nodeValue2776]
  ring

noncomputable def reducedSource555 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1442 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3187 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((2 : ℝ) * Sparse.eval nodeValue3210 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow555 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 50), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, 35), (Sum.inr 1406, 1440), (Sum.inr 1408, 720), (Sum.inr 2092, 1440), (Sum.inr 2113, 720), (Sum.inr 2255, 720), (Sum.inr 3039, 1440), (Sum.inr 3054, 720), (Sum.inr 3055, 720), (Sum.inr 3180, 1440), (Sum.inr 3202, 1440), (Sum.inr 3222, 1440)]

theorem reindexCheck555 : Integer.Sparse.reindex keyMap MixedData.row555 = numericRow555 := by decide +kernel

theorem numericCheck555 (x : Master → ℝ) : Integer.Sparse.eval numericRow555 x =
    (720 : ℝ) * reducedSource555 x := by
  norm_num [numericRow555, reducedSource555, Integer.Sparse.eval, Sparse.eval, nodeValue1406, nodeValue1408, nodeValue1419, nodeValue1442, nodeValue2092, nodeValue2113, nodeValue2255, nodeValue3039, nodeValue3054, nodeValue3055, nodeValue3102, nodeValue3180, nodeValue3187, nodeValue3202, nodeValue3206, nodeValue3210, nodeValue3222, nodeValue3224, nodeValue3227, nodeValue3229, nodeValue3230]
  ring

noncomputable def reducedSource556 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow556 : Integer.Sparse Master := [(Sum.inr 1042, 2), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem reindexCheck556 : Integer.Sparse.reindex keyMap MixedData.row556 = numericRow556 := by decide +kernel

theorem numericCheck556 (x : Master → ℝ) : Integer.Sparse.eval numericRow556 x =
    (1 : ℝ) * reducedSource556 x := by
  norm_num [numericRow556, reducedSource556, Integer.Sparse.eval, Sparse.eval, nodeValue1042, nodeValue1047, nodeValue1049, nodeValue1087, nodeValue2266, nodeValue4084]

noncomputable def reducedSource557 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((2 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue4856 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue4886 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))))

def numericRow557 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1044, -8640), (Sum.inr 1737, -8640), (Sum.inr 2023, -8640), (Sum.inr 2110, -8640), (Sum.inr 2214, -8640), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -8640), (Sum.inr 2262, -4320), (Sum.inr 2275, -8640), (Sum.inr 2277, -8640), (Sum.inr 3053, -4320), (Sum.inr 3619, -4320), (Sum.inr 3622, -4320), (Sum.inr 4439, 17280), (Sum.inr 4442, 17280), (Sum.inr 4444, 17280), (Sum.inr 4793, 17280), (Sum.inr 4795, 17280), (Sum.inr 4808, 34560), (Sum.inr 4852, 34560), (Sum.inr 4856, 34560), (Sum.inr 4885, 17280), (Sum.inr 4886, 17280), (Sum.inr 5265, 17280), (Sum.inr 5299, 34560)]

theorem reindexCheck557 : Integer.Sparse.reindex keyMap MixedData.row557 = numericRow557 := by decide +kernel

theorem numericCheck557 (x : Master → ℝ) : Integer.Sparse.eval numericRow557 x =
    (17280 : ℝ) * reducedSource557 x := by
  norm_num [numericRow557, reducedSource557, Integer.Sparse.eval, Sparse.eval, nodeValue4439, nodeValue4442, nodeValue4444, nodeValue4461, nodeValue4793, nodeValue4795, nodeValue4805, nodeValue4808, nodeValue4852, nodeValue4856, nodeValue4869, nodeValue4885, nodeValue4886, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5265, nodeValue5292, nodeValue5299, nodeValue5301]
  ring

noncomputable def reducedSource558 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2274 x + ((2 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + 0))))))))))))))))))))

def numericRow558 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, -35), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -120), (Sum.inl 1, -50), (Sum.inr 1713, 2160), (Sum.inr 1736, 2160), (Sum.inr 1737, 4320), (Sum.inr 1744, 2160), (Sum.inr 2213, 2160), (Sum.inr 2214, 4320), (Sum.inr 2219, 2160), (Sum.inr 2220, 4320), (Sum.inr 2243, 2160), (Sum.inr 2250, 4320), (Sum.inr 2252, 2160), (Sum.inr 2262, 2160), (Sum.inr 2274, 4320), (Sum.inr 2275, 4320), (Sum.inr 2277, 4320), (Sum.inr 2283, 2160), (Sum.inr 2730, 2160), (Sum.inr 2773, 4320)]

theorem reindexCheck558 : Integer.Sparse.reindex keyMap MixedData.row558 = numericRow558 := by decide +kernel

theorem numericCheck558 (x : Master → ℝ) : Integer.Sparse.eval numericRow558 x =
    (2160 : ℝ) * reducedSource558 x := by
  norm_num [numericRow558, reducedSource558, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue1736, nodeValue1737, nodeValue1744, nodeValue2213, nodeValue2214, nodeValue2219, nodeValue2220, nodeValue2243, nodeValue2250, nodeValue2252, nodeValue2262, nodeValue2263, nodeValue2274, nodeValue2275, nodeValue2277, nodeValue2283, nodeValue2730, nodeValue2766, nodeValue2773, nodeValue2775]
  ring

noncomputable def reducedSource559 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((1 : ℝ) * Sparse.eval nodeValue3622 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow559 : Integer.Sparse Master := [(Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 2), (Sum.inr 3619, 1), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

theorem reindexCheck559 : Integer.Sparse.reindex keyMap MixedData.row559 = numericRow559 := by decide +kernel

theorem numericCheck559 (x : Master → ℝ) : Integer.Sparse.eval numericRow559 x =
    (1 : ℝ) * reducedSource559 x := by
  norm_num [numericRow559, reducedSource559, Integer.Sparse.eval, Sparse.eval, nodeValue2245, nodeValue3526, nodeValue3573, nodeValue3619, nodeValue3622, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
