import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource176 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue776 x + ((1 : ℝ) * Sparse.eval nodeValue778 x + ((3 : ℝ) * Sparse.eval nodeValue784 x + ((3 : ℝ) * Sparse.eval nodeValue2009 x + ((3 : ℝ) * Sparse.eval nodeValue2012 x + ((6 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((3 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((3 : ℝ) * Sparse.eval nodeValue2240 x + ((3 : ℝ) * Sparse.eval nodeValue3847 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))

def numericRow176 : Integer.Sparse Master := [(Sum.inl 0, -8), (Sum.inl 2, 35), (Sum.inl 3, 640), (Sum.inl 13, 240), (Sum.inl 12, 320), (Sum.inl 4, 160), (Sum.inl 1, -145), (Sum.inr 776, 1440), (Sum.inr 778, 1440), (Sum.inr 784, 4320), (Sum.inr 2009, 4320), (Sum.inr 2012, 4320), (Sum.inr 2021, 8640), (Sum.inr 2187, 1440), (Sum.inr 2192, 4320), (Sum.inr 2232, 1440), (Sum.inr 2240, 4320), (Sum.inr 3899, 1440), (Sum.inr 3909, 1440)]

theorem reindexCheck176 : Integer.Sparse.reindex keyMap MixedData.row176 = numericRow176 := by decide +kernel

theorem numericCheck176 (x : Master → ℝ) : Integer.Sparse.eval numericRow176 x =
    (1440 : ℝ) * reducedSource176 x := by
  norm_num [numericRow176, reducedSource176, Integer.Sparse.eval, Sparse.eval, nodeValue776, nodeValue778, nodeValue784, nodeValue2009, nodeValue2012, nodeValue2021, nodeValue2187, nodeValue2192, nodeValue2232, nodeValue2240, nodeValue3847, nodeValue3899, nodeValue3909]
  ring

noncomputable def reducedSource177 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3221 x + ((3 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue4025 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow177 : Integer.Sparse Master := [(Sum.inr 3221, 1), (Sum.inr 3801, 3), (Sum.inr 3899, 1), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem reindexCheck177 : Integer.Sparse.reindex keyMap MixedData.row177 = numericRow177 := by decide +kernel

theorem numericCheck177 (x : Master → ℝ) : Integer.Sparse.eval numericRow177 x =
    (1 : ℝ) * reducedSource177 x := by
  norm_num [numericRow177, reducedSource177, Integer.Sparse.eval, Sparse.eval, nodeValue3221, nodeValue3801, nodeValue3899, nodeValue4025, nodeValue4091]

noncomputable def reducedSource178 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1464 x + ((1 : ℝ) * Sparse.eval nodeValue1467 x + ((1 : ℝ) * Sparse.eval nodeValue1474 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow178 : Integer.Sparse Master := [(Sum.inr 1464, 3), (Sum.inr 1467, 1), (Sum.inr 1474, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem reindexCheck178 : Integer.Sparse.reindex keyMap MixedData.row178 = numericRow178 := by decide +kernel

theorem numericCheck178 (x : Master → ℝ) : Integer.Sparse.eval numericRow178 x =
    (1 : ℝ) * reducedSource178 x := by
  norm_num [numericRow178, reducedSource178, Integer.Sparse.eval, Sparse.eval, nodeValue1464, nodeValue1467, nodeValue1474, nodeValue3221, nodeValue4091]

noncomputable def reducedSource179 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1464 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow179 : Integer.Sparse Master := [(Sum.inr 1464, 1), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem reindexCheck179 : Integer.Sparse.reindex keyMap MixedData.row179 = numericRow179 := by decide +kernel

theorem numericCheck179 (x : Master → ℝ) : Integer.Sparse.eval numericRow179 x =
    (1 : ℝ) * reducedSource179 x := by
  norm_num [numericRow179, reducedSource179, Integer.Sparse.eval, Sparse.eval, nodeValue1464, nodeValue3172, nodeValue3197, nodeValue3202, nodeValue3221, nodeValue4091]

noncomputable def reducedSource180 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow180 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 3199, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

theorem reindexCheck180 : Integer.Sparse.reindex keyMap MixedData.row180 = numericRow180 := by decide +kernel

theorem numericCheck180 (x : Master → ℝ) : Integer.Sparse.eval numericRow180 x =
    (1 : ℝ) * reducedSource180 x := by
  norm_num [numericRow180, reducedSource180, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue3199, nodeValue3202, nodeValue3221, nodeValue3801, nodeValue4091]

noncomputable def reducedSource181 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1467 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((3 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow181 : Integer.Sparse Master := [(Sum.inr 1467, 1), (Sum.inr 3179, 1), (Sum.inr 3199, 3), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem reindexCheck181 : Integer.Sparse.reindex keyMap MixedData.row181 = numericRow181 := by decide +kernel

theorem numericCheck181 (x : Master → ℝ) : Integer.Sparse.eval numericRow181 x =
    (1 : ℝ) * reducedSource181 x := by
  norm_num [numericRow181, reducedSource181, Integer.Sparse.eval, Sparse.eval, nodeValue1467, nodeValue3179, nodeValue3199, nodeValue3221, nodeValue4091]

noncomputable def reducedSource182 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2707 x + ((3 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow182 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 3197, 3), (Sum.inr 3221, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

theorem reindexCheck182 : Integer.Sparse.reindex keyMap MixedData.row182 = numericRow182 := by decide +kernel

theorem numericCheck182 (x : Master → ℝ) : Integer.Sparse.eval numericRow182 x =
    (1 : ℝ) * reducedSource182 x := by
  norm_num [numericRow182, reducedSource182, Integer.Sparse.eval, Sparse.eval, nodeValue2707, nodeValue3197, nodeValue3221, nodeValue3899, nodeValue4091]

noncomputable def reducedSource183 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1474 x + ((3 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2707 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow183 : Integer.Sparse Master := [(Sum.inr 1474, 1), (Sum.inr 2471, 3), (Sum.inr 2707, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem reindexCheck183 : Integer.Sparse.reindex keyMap MixedData.row183 = numericRow183 := by decide +kernel

theorem numericCheck183 (x : Master → ℝ) : Integer.Sparse.eval numericRow183 x =
    (1 : ℝ) * reducedSource183 x := by
  norm_num [numericRow183, reducedSource183, Integer.Sparse.eval, Sparse.eval, nodeValue1474, nodeValue2471, nodeValue2707, nodeValue3221, nodeValue4091]

noncomputable def reducedSource184 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1354 x + ((1 : ℝ) * Sparse.eval nodeValue1366 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((3 : ℝ) * Sparse.eval nodeValue3077 x + ((3 : ℝ) * Sparse.eval nodeValue3146 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((3 : ℝ) * Sparse.eval nodeValue3165 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((6 : ℝ) * Sparse.eval nodeValue3222 x + ((3 : ℝ) * Sparse.eval nodeValue3223 x + ((3 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))

def numericRow184 : Integer.Sparse Master := [(Sum.inl 0, -59), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 13, -320), (Sum.inl 12, -80), (Sum.inl 1, 30), (Sum.inr 1354, 4320), (Sum.inr 1366, 1440), (Sum.inr 3058, 1440), (Sum.inr 3059, 1440), (Sum.inr 3077, 4320), (Sum.inr 3146, 4320), (Sum.inr 3155, 1440), (Sum.inr 3165, 4320), (Sum.inr 3179, 1440), (Sum.inr 3222, 8640)]

theorem reindexCheck184 : Integer.Sparse.reindex keyMap MixedData.row184 = numericRow184 := by decide +kernel

theorem numericCheck184 (x : Master → ℝ) : Integer.Sparse.eval numericRow184 x =
    (1440 : ℝ) * reducedSource184 x := by
  norm_num [numericRow184, reducedSource184, Integer.Sparse.eval, Sparse.eval, nodeValue1354, nodeValue1366, nodeValue1405, nodeValue3058, nodeValue3059, nodeValue3077, nodeValue3146, nodeValue3155, nodeValue3165, nodeValue3179, nodeValue3222, nodeValue3223, nodeValue3227]
  ring

noncomputable def reducedSource185 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue2507 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((3 : ℝ) * Sparse.eval nodeValue3625 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow185 : Integer.Sparse Master := [(Sum.inr 2252, 1), (Sum.inr 2507, 1), (Sum.inr 3576, 1), (Sum.inr 3625, 3), (Sum.inr 4084, -1)]

theorem reindexCheck185 : Integer.Sparse.reindex keyMap MixedData.row185 = numericRow185 := by decide +kernel

theorem numericCheck185 (x : Master → ℝ) : Integer.Sparse.eval numericRow185 x =
    (1 : ℝ) * reducedSource185 x := by
  norm_num [numericRow185, reducedSource185, Integer.Sparse.eval, Sparse.eval, nodeValue2252, nodeValue2507, nodeValue3576, nodeValue3625, nodeValue4084]

noncomputable def reducedSource186 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1056 x + ((1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((3 : ℝ) * Sparse.eval nodeValue2277 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow186 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 2131, 1), (Sum.inr 2252, 1), (Sum.inr 2277, 3), (Sum.inr 4084, -1)]

theorem reindexCheck186 : Integer.Sparse.reindex keyMap MixedData.row186 = numericRow186 := by decide +kernel

theorem numericCheck186 (x : Master → ℝ) : Integer.Sparse.eval numericRow186 x =
    (1 : ℝ) * reducedSource186 x := by
  norm_num [numericRow186, reducedSource186, Integer.Sparse.eval, Sparse.eval, nodeValue1056, nodeValue2131, nodeValue2252, nodeValue2277, nodeValue4084]

noncomputable def reducedSource187 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue2104 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((3 : ℝ) * Sparse.eval nodeValue2262 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow187 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2252, 1), (Sum.inr 2262, 3), (Sum.inr 4084, -1)]

theorem reindexCheck187 : Integer.Sparse.reindex keyMap MixedData.row187 = numericRow187 := by decide +kernel

theorem numericCheck187 (x : Master → ℝ) : Integer.Sparse.eval numericRow187 x =
    (1 : ℝ) * reducedSource187 x := by
  norm_num [numericRow187, reducedSource187, Integer.Sparse.eval, Sparse.eval, nodeValue1038, nodeValue2104, nodeValue2252, nodeValue2262, nodeValue4084]

noncomputable def reducedSource188 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2059 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2064 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3035 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + 0))))))))))))))))))))

def numericRow188 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 1, 10), (Sum.inr 2059, 4320), (Sum.inr 2063, 2160), (Sum.inr 2064, 2160), (Sum.inr 2267, 2160), (Sum.inr 2670, 4320), (Sum.inr 2683, 2160), (Sum.inr 2685, 2160), (Sum.inr 2740, 2160), (Sum.inr 3015, 4320), (Sum.inr 3022, 4320), (Sum.inr 3024, 4320), (Sum.inr 3035, 4320), (Sum.inr 3038, 4320), (Sum.inr 3049, 2160), (Sum.inr 3054, 2160), (Sum.inr 3075, 4320), (Sum.inr 3098, 2160), (Sum.inr 3156, 4320), (Sum.inr 3161, 2160)]

theorem reindexCheck188 : Integer.Sparse.reindex keyMap MixedData.row188 = numericRow188 := by decide +kernel

theorem numericCheck188 (x : Master → ℝ) : Integer.Sparse.eval numericRow188 x =
    (2160 : ℝ) * reducedSource188 x := by
  norm_num [numericRow188, reducedSource188, Integer.Sparse.eval, Sparse.eval, nodeValue2059, nodeValue2063, nodeValue2064, nodeValue2267, nodeValue2670, nodeValue2683, nodeValue2685, nodeValue2740, nodeValue3015, nodeValue3022, nodeValue3024, nodeValue3035, nodeValue3038, nodeValue3049, nodeValue3054, nodeValue3075, nodeValue3098, nodeValue3101, nodeValue3156, nodeValue3161, nodeValue3224]
  ring

noncomputable def reducedSource189 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow189 : Integer.Sparse Master := [(Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 2), (Sum.inr 3626, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

theorem reindexCheck189 : Integer.Sparse.reindex keyMap MixedData.row189 = numericRow189 := by decide +kernel

theorem numericCheck189 (x : Master → ℝ) : Integer.Sparse.eval numericRow189 x =
    (1 : ℝ) * reducedSource189 x := by
  norm_num [numericRow189, reducedSource189, Integer.Sparse.eval, Sparse.eval, nodeValue2279, nodeValue2744, nodeValue3541, nodeValue3626, nodeValue3632, nodeValue4084]

noncomputable def reducedSource190 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1238 x + ((1 : ℝ) * Sparse.eval nodeValue1244 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1296 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow190 : Integer.Sparse Master := [(Sum.inr 1238, 2), (Sum.inr 1244, 1), (Sum.inr 1245, 1), (Sum.inr 1296, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem reindexCheck190 : Integer.Sparse.reindex keyMap MixedData.row190 = numericRow190 := by decide +kernel

theorem numericCheck190 (x : Master → ℝ) : Integer.Sparse.eval numericRow190 x =
    (1 : ℝ) * reducedSource190 x := by
  norm_num [numericRow190, reducedSource190, Integer.Sparse.eval, Sparse.eval, nodeValue1238, nodeValue1244, nodeValue1245, nodeValue1296, nodeValue2744, nodeValue4084]

noncomputable def reducedSource191 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1296 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow191 : Integer.Sparse Master := [(Sum.inr 1296, 1), (Sum.inr 2138, 1), (Sum.inr 2592, 2), (Sum.inr 2744, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

theorem reindexCheck191 : Integer.Sparse.reindex keyMap MixedData.row191 = numericRow191 := by decide +kernel

theorem numericCheck191 (x : Master → ℝ) : Integer.Sparse.eval numericRow191 x =
    (1 : ℝ) * reducedSource191 x := by
  norm_num [numericRow191, reducedSource191, Integer.Sparse.eval, Sparse.eval, nodeValue1296, nodeValue2138, nodeValue2592, nodeValue2744, nodeValue2781, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
