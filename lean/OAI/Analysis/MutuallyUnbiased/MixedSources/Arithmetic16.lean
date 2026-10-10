import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource256 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow256 : Integer.Sparse Master := [(Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem reindexCheck256 : Integer.Sparse.reindex keyMap MixedData.row256 = numericRow256 := by decide +kernel

theorem numericCheck256 (x : Master → ℝ) : Integer.Sparse.eval numericRow256 x =
    (1 : ℝ) * reducedSource256 x := by
  norm_num [numericRow256, reducedSource256, Integer.Sparse.eval, Sparse.eval, nodeValue3039, nodeValue3880, nodeValue3881, nodeValue3885, nodeValue3910, nodeValue3958, nodeValue4091]

noncomputable def reducedSource257 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue1363 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1423 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow257 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 1361, 1), (Sum.inr 1363, 1), (Sum.inr 1370, 1), (Sum.inr 1423, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem reindexCheck257 : Integer.Sparse.reindex keyMap MixedData.row257 = numericRow257 := by decide +kernel

theorem numericCheck257 (x : Master → ℝ) : Integer.Sparse.eval numericRow257 x =
    (1 : ℝ) * reducedSource257 x := by
  norm_num [numericRow257, reducedSource257, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue1361, nodeValue1363, nodeValue1370, nodeValue1423, nodeValue3039, nodeValue4091]

noncomputable def reducedSource258 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow258 : Integer.Sparse Master := [(Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 2), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

theorem reindexCheck258 : Integer.Sparse.reindex keyMap MixedData.row258 = numericRow258 := by decide +kernel

theorem numericCheck258 (x : Master → ℝ) : Integer.Sparse.eval numericRow258 x =
    (1 : ℝ) * reducedSource258 x := by
  norm_num [numericRow258, reducedSource258, Integer.Sparse.eval, Sparse.eval, nodeValue1370, nodeValue2884, nodeValue2976, nodeValue3039, nodeValue3053, nodeValue4091]

noncomputable def reducedSource259 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2946 x + ((1 : ℝ) * Sparse.eval nodeValue3008 x + ((1 : ℝ) * Sparse.eval nodeValue3011 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow259 : Integer.Sparse Master := [(Sum.inr 2627, 1), (Sum.inr 2946, 1), (Sum.inr 3008, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem reindexCheck259 : Integer.Sparse.reindex keyMap MixedData.row259 = numericRow259 := by decide +kernel

theorem numericCheck259 (x : Master → ℝ) : Integer.Sparse.eval numericRow259 x =
    (1 : ℝ) * reducedSource259 x := by
  norm_num [numericRow259, reducedSource259, Integer.Sparse.eval, Sparse.eval, nodeValue2627, nodeValue2946, nodeValue3008, nodeValue3011, nodeValue3039, nodeValue3881, nodeValue4091]

noncomputable def reducedSource260 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue3008 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow260 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 2862, 1), (Sum.inr 3008, 1), (Sum.inr 3029, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem reindexCheck260 : Integer.Sparse.reindex keyMap MixedData.row260 = numericRow260 := by decide +kernel

theorem numericCheck260 (x : Master → ℝ) : Integer.Sparse.eval numericRow260 x =
    (1 : ℝ) * reducedSource260 x := by
  norm_num [numericRow260, reducedSource260, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue2862, nodeValue3008, nodeValue3029, nodeValue3037, nodeValue3039, nodeValue4091]

noncomputable def reducedSource261 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2918 x + ((1 : ℝ) * Sparse.eval nodeValue2972 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow261 : Integer.Sparse Master := [(Sum.inr 2625, 1), (Sum.inr 2918, 1), (Sum.inr 2972, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem reindexCheck261 : Integer.Sparse.reindex keyMap MixedData.row261 = numericRow261 := by decide +kernel

theorem numericCheck261 (x : Master → ℝ) : Integer.Sparse.eval numericRow261 x =
    (1 : ℝ) * reducedSource261 x := by
  norm_num [numericRow261, reducedSource261, Integer.Sparse.eval, Sparse.eval, nodeValue2625, nodeValue2918, nodeValue2972, nodeValue2976, nodeValue3039, nodeValue3880, nodeValue4091]

noncomputable def reducedSource262 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1423 x + ((1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow262 : Integer.Sparse Master := [(Sum.inr 1423, 1), (Sum.inr 2625, 1), (Sum.inr 2627, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem reindexCheck262 : Integer.Sparse.reindex keyMap MixedData.row262 = numericRow262 := by decide +kernel

theorem numericCheck262 (x : Master → ℝ) : Integer.Sparse.eval numericRow262 x =
    (1 : ℝ) * reducedSource262 x := by
  norm_num [numericRow262, reducedSource262, Integer.Sparse.eval, Sparse.eval, nodeValue1423, nodeValue2625, nodeValue2627, nodeValue2641, nodeValue2754, nodeValue3039, nodeValue4091]

noncomputable def reducedSource263 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow263 : Integer.Sparse Master := [(Sum.inr 2862, 1), (Sum.inr 2865, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 1), (Sum.inr 3039, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem reindexCheck263 : Integer.Sparse.reindex keyMap MixedData.row263 = numericRow263 := by decide +kernel

theorem numericCheck263 (x : Master → ℝ) : Integer.Sparse.eval numericRow263 x =
    (1 : ℝ) * reducedSource263 x := by
  norm_num [numericRow263, reducedSource263, Integer.Sparse.eval, Sparse.eval, nodeValue2862, nodeValue2865, nodeValue2868, nodeValue2884, nodeValue3039, nodeValue3958, nodeValue4091]

noncomputable def reducedSource264 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1363 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2972 x + ((1 : ℝ) * Sparse.eval nodeValue3011 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow264 : Integer.Sparse Master := [(Sum.inr 1363, 1), (Sum.inr 2868, 1), (Sum.inr 2972, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 2), (Sum.inr 4091, -1)]

theorem reindexCheck264 : Integer.Sparse.reindex keyMap MixedData.row264 = numericRow264 := by decide +kernel

theorem numericCheck264 (x : Master → ℝ) : Integer.Sparse.eval numericRow264 x =
    (1 : ℝ) * reducedSource264 x := by
  norm_num [numericRow264, reducedSource264, Integer.Sparse.eval, Sparse.eval, nodeValue1363, nodeValue2868, nodeValue2972, nodeValue3011, nodeValue3039, nodeValue4091]

noncomputable def reducedSource265 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow265 : Integer.Sparse Master := [(Sum.inr 2641, 1), (Sum.inr 3029, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem reindexCheck265 : Integer.Sparse.reindex keyMap MixedData.row265 = numericRow265 := by decide +kernel

theorem numericCheck265 (x : Master → ℝ) : Integer.Sparse.eval numericRow265 x =
    (1 : ℝ) * reducedSource265 x := by
  norm_num [numericRow265, reducedSource265, Integer.Sparse.eval, Sparse.eval, nodeValue2641, nodeValue3029, nodeValue3031, nodeValue3039, nodeValue3885, nodeValue4091]

noncomputable def reducedSource266 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2918 x + ((1 : ℝ) * Sparse.eval nodeValue2946 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow266 : Integer.Sparse Master := [(Sum.inr 1361, 1), (Sum.inr 2865, 1), (Sum.inr 2918, 1), (Sum.inr 2946, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem reindexCheck266 : Integer.Sparse.reindex keyMap MixedData.row266 = numericRow266 := by decide +kernel

theorem numericCheck266 (x : Master → ℝ) : Integer.Sparse.eval numericRow266 x =
    (1 : ℝ) * reducedSource266 x := by
  norm_num [numericRow266, reducedSource266, Integer.Sparse.eval, Sparse.eval, nodeValue1361, nodeValue2865, nodeValue2918, nodeValue2946, nodeValue3031, nodeValue3039, nodeValue4091]

noncomputable def reducedSource267 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4854 x + ((1 : ℝ) * Sparse.eval nodeValue4855 x + ((1 : ℝ) * Sparse.eval nodeValue4870 x + ((1 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5223 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((2 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5253 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))))))))))

def numericRow267 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 2028, -360), (Sum.inr 2058, -360), (Sum.inr 2215, -360), (Sum.inr 2216, -360), (Sum.inr 2266, -360), (Sum.inr 2278, -360), (Sum.inr 2672, -360), (Sum.inr 2722, -360), (Sum.inr 2723, -720), (Sum.inr 3054, -360), (Sum.inr 3391, -360), (Sum.inr 3533, -360), (Sum.inr 3544, -720), (Sum.inr 3626, -360), (Sum.inr 3627, -360), (Sum.inr 4803, 1440), (Sum.inr 4808, 1440), (Sum.inr 4854, 1440), (Sum.inr 4855, 1440), (Sum.inr 4870, 1440), (Sum.inr 4880, 1440), (Sum.inr 5220, 1440), (Sum.inr 5223, 1440), (Sum.inr 5229, 1440), (Sum.inr 5232, 1440), (Sum.inr 5233, 2880), (Sum.inr 5243, 1440), (Sum.inr 5244, 1440), (Sum.inr 5253, 1440), (Sum.inr 5254, 1440), (Sum.inr 5264, 1440), (Sum.inr 5266, 1440), (Sum.inr 5267, 1440), (Sum.inr 5300, 1440)]

theorem reindexCheck267 : Integer.Sparse.reindex keyMap MixedData.row267 = numericRow267 := by decide +kernel

theorem numericCheck267 (x : Master → ℝ) : Integer.Sparse.eval numericRow267 x =
    (1440 : ℝ) * reducedSource267 x := by
  norm_num [numericRow267, reducedSource267, Integer.Sparse.eval, Sparse.eval, nodeValue4803, nodeValue4808, nodeValue4810, nodeValue4839, nodeValue4854, nodeValue4855, nodeValue4870, nodeValue4880, nodeValue4896, nodeValue5220, nodeValue5223, nodeValue5228, nodeValue5229, nodeValue5232, nodeValue5233, nodeValue5243, nodeValue5244, nodeValue5250, nodeValue5253, nodeValue5254, nodeValue5258, nodeValue5259, nodeValue5264, nodeValue5266, nodeValue5267, nodeValue5293, nodeValue5300, nodeValue5302]
  ring

noncomputable def reducedSource268 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2127 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2665 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2713 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + 0)))))))))))))))))))))))))))))

def numericRow268 : Integer.Sparse Master := [(Sum.inl 0, -260), (Sum.inl 5, -40), (Sum.inl 2, 350), (Sum.inl 35, -160), (Sum.inl 3, -160), (Sum.inl 13, 160), (Sum.inl 55, 480), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 27, 120), (Sum.inl 1, 170), (Sum.inr 2127, 8640), (Sum.inr 2128, 8640), (Sum.inr 2129, 8640), (Sum.inr 2133, 8640), (Sum.inr 2195, 8640), (Sum.inr 2215, 8640), (Sum.inr 2216, 8640), (Sum.inr 2220, 8640), (Sum.inr 2278, 8640), (Sum.inr 2665, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2697, 8640), (Sum.inr 2698, 8640), (Sum.inr 2713, 8640), (Sum.inr 2714, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2729, 8640), (Sum.inr 2731, 8640), (Sum.inr 2732, 8640), (Sum.inr 2774, 8640), (Sum.inr 3044, 8640), (Sum.inr 3068, 8640), (Sum.inr 3092, 8640)]

theorem reindexCheck268 : Integer.Sparse.reindex keyMap MixedData.row268 = numericRow268 := by decide +kernel

theorem numericCheck268 (x : Master → ℝ) : Integer.Sparse.eval numericRow268 x =
    (8640 : ℝ) * reducedSource268 x := by
  norm_num [numericRow268, reducedSource268, Integer.Sparse.eval, Sparse.eval, nodeValue2127, nodeValue2128, nodeValue2129, nodeValue2133, nodeValue2195, nodeValue2215, nodeValue2216, nodeValue2220, nodeValue2278, nodeValue2665, nodeValue2677, nodeValue2678, nodeValue2697, nodeValue2698, nodeValue2709, nodeValue2713, nodeValue2714, nodeValue2722, nodeValue2723, nodeValue2729, nodeValue2731, nodeValue2732, nodeValue2767, nodeValue2774, nodeValue2776, nodeValue3044, nodeValue3068, nodeValue3088, nodeValue3092, nodeValue3094]
  ring

noncomputable def reducedSource269 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2091 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2111 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3017 x + ((1 : ℝ) * Sparse.eval nodeValue3019 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0)))))))))))))))))))))))))))))

def numericRow269 : Integer.Sparse Master := [(Sum.inl 0, -804), (Sum.inl 5, 160), (Sum.inl 6, 20), (Sum.inl 2, 1040), (Sum.inl 7, -320), (Sum.inl 35, -640), (Sum.inl 3, -960), (Sum.inl 13, -640), (Sum.inl 52, -320), (Sum.inl 54, 960), (Sum.inl 12, -320), (Sum.inl 26, -320), (Sum.inl 1, 1280), (Sum.inr 2091, 17280), (Sum.inr 2092, 17280), (Sum.inr 2093, 17280), (Sum.inr 2111, 17280), (Sum.inr 2254, 17280), (Sum.inr 2662, 17280), (Sum.inr 2672, 17280), (Sum.inr 2673, 17280), (Sum.inr 2678, 17280), (Sum.inr 2723, 17280), (Sum.inr 3016, 17280), (Sum.inr 3017, 17280), (Sum.inr 3019, 17280), (Sum.inr 3029, 17280), (Sum.inr 3030, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3040, 17280), (Sum.inr 3044, 17280), (Sum.inr 3045, 17280), (Sum.inr 3054, 17280), (Sum.inr 3055, 17280), (Sum.inr 3202, 17280)]

theorem reindexCheck269 : Integer.Sparse.reindex keyMap MixedData.row269 = numericRow269 := by decide +kernel

theorem numericCheck269 (x : Master → ℝ) : Integer.Sparse.eval numericRow269 x =
    (17280 : ℝ) * reducedSource269 x := by
  norm_num [numericRow269, reducedSource269, Integer.Sparse.eval, Sparse.eval, nodeValue2091, nodeValue2092, nodeValue2093, nodeValue2111, nodeValue2254, nodeValue2662, nodeValue2672, nodeValue2673, nodeValue2678, nodeValue2723, nodeValue3016, nodeValue3017, nodeValue3019, nodeValue3029, nodeValue3030, nodeValue3038, nodeValue3039, nodeValue3040, nodeValue3044, nodeValue3045, nodeValue3054, nodeValue3055, nodeValue3065, nodeValue3088, nodeValue3089, nodeValue3102, nodeValue3202, nodeValue3206, nodeValue3210, nodeValue3225]
  ring

noncomputable def reducedSource270 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow270 : Integer.Sparse Master := [(Sum.inr 3388, 1), (Sum.inr 3391, 1), (Sum.inr 3392, 1), (Sum.inr 3395, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem reindexCheck270 : Integer.Sparse.reindex keyMap MixedData.row270 = numericRow270 := by decide +kernel

theorem numericCheck270 (x : Master → ℝ) : Integer.Sparse.eval numericRow270 x =
    (1 : ℝ) * reducedSource270 x := by
  norm_num [numericRow270, reducedSource270, Integer.Sparse.eval, Sparse.eval, nodeValue3388, nodeValue3391, nodeValue3392, nodeValue3395, nodeValue3535, nodeValue3544, nodeValue4084]

noncomputable def reducedSource271 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow271 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2266, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem reindexCheck271 : Integer.Sparse.reindex keyMap MixedData.row271 = numericRow271 := by decide +kernel

theorem numericCheck271 (x : Master → ℝ) : Integer.Sparse.eval numericRow271 x =
    (1 : ℝ) * reducedSource271 x := by
  norm_num [numericRow271, reducedSource271, Integer.Sparse.eval, Sparse.eval, nodeValue2021, nodeValue2026, nodeValue2028, nodeValue2058, nodeValue2266, nodeValue3535, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
