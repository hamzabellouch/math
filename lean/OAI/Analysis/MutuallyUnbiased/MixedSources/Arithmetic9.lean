import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((8 : ℝ) * Sparse.eval nodeValue4897 x + ((12 : ℝ) * Sparse.eval nodeValue5261 x + ((8 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))

def numericRow144 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2726, -180), (Sum.inr 3545, -180), (Sum.inr 3634, -120), (Sum.inr 4085, 60)]

theorem reindexCheck144 : Integer.Sparse.reindex keyMap MixedData.row144 = numericRow144 := by decide +kernel

theorem numericCheck144 (x : Master → ℝ) : Integer.Sparse.eval numericRow144 x =
    (60 : ℝ) * reducedSource144 x := by
  norm_num [numericRow144, reducedSource144, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4897, nodeValue5261, nodeValue5296, nodeValue5312]
  ring

noncomputable def reducedSource145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((6 : ℝ) * Sparse.eval nodeValue4804 x + ((3 : ℝ) * Sparse.eval nodeValue4841 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((3 : ℝ) * Sparse.eval nodeValue4894 x + ((3 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))

def numericRow145 : Integer.Sparse Master := [(Sum.inr 1043, -3), (Sum.inr 1051, -1), (Sum.inr 1239, -3), (Sum.inr 1297, -1), (Sum.inr 1725, -3), (Sum.inr 1752, -1), (Sum.inr 2022, -6), (Sum.inr 2109, -3), (Sum.inr 2203, -6), (Sum.inr 2226, -3), (Sum.inr 2261, -3), (Sum.inr 2289, -1), (Sum.inr 2740, -6), (Sum.inr 2783, -2), (Sum.inr 4084, 4)]

theorem reindexCheck145 : Integer.Sparse.reindex keyMap MixedData.row145 = numericRow145 := by decide +kernel

theorem numericCheck145 (x : Master → ℝ) : Integer.Sparse.eval numericRow145 x =
    (4 : ℝ) * reducedSource145 x := by
  norm_num [numericRow145, reducedSource145, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4460, nodeValue4468, nodeValue4505, nodeValue4605, nodeValue4621, nodeValue4804, nodeValue4841, nodeValue4868, nodeValue4894, nodeValue5272, nodeValue5305, nodeValue5308]
  ring

noncomputable def reducedSource146 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((6 : ℝ) * Sparse.eval nodeValue2203 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((3 : ℝ) * Sparse.eval nodeValue2228 x + ((3 : ℝ) * Sparse.eval nodeValue2261 x + ((3 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((3 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

def numericRow146 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 2203, 6), (Sum.inr 2226, 3), (Sum.inr 2261, 3), (Sum.inr 2289, 1), (Sum.inr 2740, 3), (Sum.inr 2783, 1), (Sum.inr 4084, 1)]

theorem reindexCheck146 : Integer.Sparse.reindex keyMap MixedData.row146 = numericRow146 := by decide +kernel

theorem numericCheck146 (x : Master → ℝ) : Integer.Sparse.eval numericRow146 x =
    (1 : ℝ) * reducedSource146 x := by
  norm_num [numericRow146, reducedSource146, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue1752, nodeValue1754, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2261, nodeValue2264, nodeValue2289, nodeValue2740, nodeValue2783, nodeValue2786, nodeValue4084]

noncomputable def reducedSource147 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1051 x + ((3 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow147 : Integer.Sparse Master := [(Sum.inr 1051, 1), (Sum.inr 1239, 3), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem reindexCheck147 : Integer.Sparse.reindex keyMap MixedData.row147 = numericRow147 := by decide +kernel

theorem numericCheck147 (x : Master → ℝ) : Integer.Sparse.eval numericRow147 x =
    (1 : ℝ) * reducedSource147 x := by
  norm_num [numericRow147, reducedSource147, Integer.Sparse.eval, Sparse.eval, nodeValue1051, nodeValue1239, nodeValue1297, nodeValue2268, nodeValue4084]

noncomputable def reducedSource148 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow148 : Integer.Sparse Master := [(Sum.inr 1239, 1), (Sum.inr 2022, 2), (Sum.inr 2740, 1), (Sum.inr 4084, -1)]

theorem reindexCheck148 : Integer.Sparse.reindex keyMap MixedData.row148 = numericRow148 := by decide +kernel

theorem numericCheck148 (x : Master → ℝ) : Integer.Sparse.eval numericRow148 x =
    (1 : ℝ) * reducedSource148 x := by
  norm_num [numericRow148, reducedSource148, Integer.Sparse.eval, Sparse.eval, nodeValue1239, nodeValue2022, nodeValue2060, nodeValue2268, nodeValue2740, nodeValue4084]

noncomputable def reducedSource149 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1043 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow149 : Integer.Sparse Master := [(Sum.inr 1043, 1), (Sum.inr 2022, 2), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

theorem reindexCheck149 : Integer.Sparse.reindex keyMap MixedData.row149 = numericRow149 := by decide +kernel

theorem numericCheck149 (x : Master → ℝ) : Integer.Sparse.eval numericRow149 x =
    (1 : ℝ) * reducedSource149 x := by
  norm_num [numericRow149, reducedSource149, Integer.Sparse.eval, Sparse.eval, nodeValue1043, nodeValue2022, nodeValue2109, nodeValue2264, nodeValue2268, nodeValue4084]

noncomputable def reducedSource150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1297 x + ((3 : ℝ) * Sparse.eval nodeValue2109 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow150 : Integer.Sparse Master := [(Sum.inr 1297, 1), (Sum.inr 2109, 3), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

theorem reindexCheck150 : Integer.Sparse.reindex keyMap MixedData.row150 = numericRow150 := by decide +kernel

theorem numericCheck150 (x : Master → ℝ) : Integer.Sparse.eval numericRow150 x =
    (1 : ℝ) * reducedSource150 x := by
  norm_num [numericRow150, reducedSource150, Integer.Sparse.eval, Sparse.eval, nodeValue1297, nodeValue2109, nodeValue2268, nodeValue2783, nodeValue4084]

noncomputable def reducedSource151 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue4832 x + ((3 : ℝ) * Sparse.eval nodeValue4837 x + ((3 : ℝ) * Sparse.eval nodeValue4845 x + ((3 : ℝ) * Sparse.eval nodeValue4890 x + ((3 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))))))))))

def numericRow151 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 1080, -360), (Sum.inr 1094, -120), (Sum.inr 1710, -360), (Sum.inr 1741, -120), (Sum.inr 2052, -720), (Sum.inr 2065, -360), (Sum.inr 2193, -720), (Sum.inr 2218, -360), (Sum.inr 2247, -360), (Sum.inr 2281, -120), (Sum.inr 2290, -360), (Sum.inr 2294, -120), (Sum.inr 2726, -360), (Sum.inr 3545, -360), (Sum.inr 3634, -120), (Sum.inr 4085, 480)]

theorem reindexCheck151 : Integer.Sparse.reindex keyMap MixedData.row151 = numericRow151 := by decide +kernel

theorem numericCheck151 (x : Master → ℝ) : Integer.Sparse.eval numericRow151 x =
    (480 : ℝ) * reducedSource151 x := by
  norm_num [numericRow151, reducedSource151, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4496, nodeValue4501, nodeValue4510, nodeValue4832, nodeValue4837, nodeValue4845, nodeValue4890, nodeValue4897, nodeValue4899, nodeValue5261, nodeValue5296, nodeValue5312]
  ring

noncomputable def reducedSource152 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4072 x + ((12 : ℝ) * Sparse.eval nodeValue4081 x + ((8 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + 0))))

def numericRow152 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, -5), (Sum.inr 4070, 240), (Sum.inr 4072, 30), (Sum.inr 4081, 360), (Sum.inr 4084, 240)]

theorem reindexCheck152 : Integer.Sparse.reindex keyMap MixedData.row152 = numericRow152 := by decide +kernel

theorem numericCheck152 (x : Master → ℝ) : Integer.Sparse.eval numericRow152 x =
    (30 : ℝ) * reducedSource152 x := by
  norm_num [numericRow152, reducedSource152, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4072, nodeValue4081, nodeValue4084, nodeValue4094]
  ring

noncomputable def reducedSource153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1354 x + ((1 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1356 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1903 x + ((1 : ℝ) * Sparse.eval nodeValue1916 x + ((1 : ℝ) * Sparse.eval nodeValue1927 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3146 x + ((1 : ℝ) * Sparse.eval nodeValue3147 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3165 x + ((1 : ℝ) * Sparse.eval nodeValue3166 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3193 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))))))))))

def numericRow153 : Integer.Sparse Master := [(Sum.inl 0, -113), (Sum.inl 2, 155), (Sum.inl 3, -80), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 1, 80), (Sum.inr 1354, 4320), (Sum.inr 1355, 4320), (Sum.inr 1356, 4320), (Sum.inr 1367, 4320), (Sum.inr 1406, 4320), (Sum.inr 1903, 4320), (Sum.inr 1916, 4320), (Sum.inr 1927, 4320), (Sum.inr 2255, 4320), (Sum.inr 3016, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3054, 4320), (Sum.inr 3077, 4320), (Sum.inr 3146, 4320), (Sum.inr 3147, 4320), (Sum.inr 3156, 4320), (Sum.inr 3165, 4320), (Sum.inr 3166, 4320), (Sum.inr 3180, 4320), (Sum.inr 3193, 4320), (Sum.inr 3196, 4320), (Sum.inr 3202, 4320), (Sum.inr 3221, 4320), (Sum.inr 3222, 8640)]

theorem reindexCheck153 : Integer.Sparse.reindex keyMap MixedData.row153 = numericRow153 := by decide +kernel

theorem numericCheck153 (x : Master → ℝ) : Integer.Sparse.eval numericRow153 x =
    (4320 : ℝ) * reducedSource153 x := by
  norm_num [numericRow153, reducedSource153, Integer.Sparse.eval, Sparse.eval, nodeValue1354, nodeValue1355, nodeValue1356, nodeValue1367, nodeValue1406, nodeValue1903, nodeValue1916, nodeValue1927, nodeValue2255, nodeValue3016, nodeValue3024, nodeValue3025, nodeValue3054, nodeValue3077, nodeValue3146, nodeValue3147, nodeValue3156, nodeValue3165, nodeValue3166, nodeValue3180, nodeValue3193, nodeValue3196, nodeValue3202, nodeValue3221, nodeValue3222, nodeValue3223, nodeValue3224, nodeValue3225, nodeValue3227]
  ring

noncomputable def reducedSource154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow154 : Integer.Sparse Master := [(Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 3528, 1), (Sum.inr 3577, 1), (Sum.inr 3625, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem reindexCheck154 : Integer.Sparse.reindex keyMap MixedData.row154 = numericRow154 := by decide +kernel

theorem numericCheck154 (x : Master → ℝ) : Integer.Sparse.eval numericRow154 x =
    (1 : ℝ) * reducedSource154 x := by
  norm_num [numericRow154, reducedSource154, Integer.Sparse.eval, Sparse.eval, nodeValue2253, nodeValue2513, nodeValue3528, nodeValue3577, nodeValue3625, nodeValue3626, nodeValue4084]

noncomputable def reducedSource155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1028 x + ((1 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue1030 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow155 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 1029, 1), (Sum.inr 1030, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 2253, 1), (Sum.inr 4084, -1)]

theorem reindexCheck155 : Integer.Sparse.reindex keyMap MixedData.row155 = numericRow155 := by decide +kernel

theorem numericCheck155 (x : Master → ℝ) : Integer.Sparse.eval numericRow155 x =
    (1 : ℝ) * reducedSource155 x := by
  norm_num [numericRow155, reducedSource155, Integer.Sparse.eval, Sparse.eval, nodeValue1028, nodeValue1029, nodeValue1030, nodeValue1042, nodeValue1058, nodeValue2253, nodeValue4084]

noncomputable def reducedSource156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1028 x + ((1 : ℝ) * Sparse.eval nodeValue2095 x + ((1 : ℝ) * Sparse.eval nodeValue2124 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow156 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 2095, 1), (Sum.inr 2124, 1), (Sum.inr 2252, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

theorem reindexCheck156 : Integer.Sparse.reindex keyMap MixedData.row156 = numericRow156 := by decide +kernel

theorem numericCheck156 (x : Master → ℝ) : Integer.Sparse.eval numericRow156 x =
    (1 : ℝ) * reducedSource156 x := by
  norm_num [numericRow156, reducedSource156, Integer.Sparse.eval, Sparse.eval, nodeValue1028, nodeValue2095, nodeValue2124, nodeValue2252, nodeValue2253, nodeValue4084]

noncomputable def reducedSource157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2014 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow157 : Integer.Sparse Master := [(Sum.inr 2013, 1), (Sum.inr 2014, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2253, 1), (Sum.inr 3528, 1), (Sum.inr 4084, -1)]

theorem reindexCheck157 : Integer.Sparse.reindex keyMap MixedData.row157 = numericRow157 := by decide +kernel

theorem numericCheck157 (x : Master → ℝ) : Integer.Sparse.eval numericRow157 x =
    (1 : ℝ) * reducedSource157 x := by
  norm_num [numericRow157, reducedSource157, Integer.Sparse.eval, Sparse.eval, nodeValue2013, nodeValue2014, nodeValue2021, nodeValue2034, nodeValue2253, nodeValue3528, nodeValue4084]

noncomputable def reducedSource158 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow158 : Integer.Sparse Master := [(Sum.inr 1058, 1), (Sum.inr 2034, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2277, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

theorem reindexCheck158 : Integer.Sparse.reindex keyMap MixedData.row158 = numericRow158 := by decide +kernel

theorem numericCheck158 (x : Master → ℝ) : Integer.Sparse.eval numericRow158 x =
    (1 : ℝ) * reducedSource158 x := by
  norm_num [numericRow158, reducedSource158, Integer.Sparse.eval, Sparse.eval, nodeValue1058, nodeValue2034, nodeValue2133, nodeValue2253, nodeValue2277, nodeValue2279, nodeValue4084]

noncomputable def reducedSource159 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2095 x + ((1 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2097 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow159 : Integer.Sparse Master := [(Sum.inr 2095, 1), (Sum.inr 2096, 1), (Sum.inr 2097, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 3577, 1), (Sum.inr 4084, -1)]

theorem reindexCheck159 : Integer.Sparse.reindex keyMap MixedData.row159 = numericRow159 := by decide +kernel

theorem numericCheck159 (x : Master → ℝ) : Integer.Sparse.eval numericRow159 x =
    (1 : ℝ) * reducedSource159 x := by
  norm_num [numericRow159, reducedSource159, Integer.Sparse.eval, Sparse.eval, nodeValue2095, nodeValue2096, nodeValue2097, nodeValue2108, nodeValue2253, nodeValue3577, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
