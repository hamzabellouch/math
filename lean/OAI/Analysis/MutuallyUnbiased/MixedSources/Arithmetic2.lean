import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource32 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1067 x + ((2 : ℝ) * Sparse.eval nodeValue2041 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow32 : Integer.Sparse Master := [(Sum.inr 1067, 2), (Sum.inr 2041, 2), (Sum.inr 2284, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem reindexCheck32 : Integer.Sparse.reindex keyMap MixedData.row32 = numericRow32 := by decide +kernel

theorem numericCheck32 (x : Master → ℝ) : Integer.Sparse.eval numericRow32 x =
    (1 : ℝ) * reducedSource32 x := by
  norm_num [numericRow32, reducedSource32, Integer.Sparse.eval, Sparse.eval, nodeValue1067, nodeValue2041, nodeValue2284, nodeValue2285, nodeValue4085]

noncomputable def reducedSource33 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1459 x + ((2 : ℝ) * Sparse.eval nodeValue2041 x + ((2 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow33 : Integer.Sparse Master := [(Sum.inr 1459, 1), (Sum.inr 2041, 2), (Sum.inr 2063, 2), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem reindexCheck33 : Integer.Sparse.reindex keyMap MixedData.row33 = numericRow33 := by decide +kernel

theorem numericCheck33 (x : Master → ℝ) : Integer.Sparse.eval numericRow33 x =
    (1 : ℝ) * reducedSource33 x := by
  norm_num [numericRow33, reducedSource33, Integer.Sparse.eval, Sparse.eval, nodeValue1459, nodeValue2041, nodeValue2063, nodeValue2285, nodeValue4085]

noncomputable def reducedSource34 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1069 x + ((3 : ℝ) * Sparse.eval nodeValue1459 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow34 : Integer.Sparse Master := [(Sum.inr 1069, 2), (Sum.inr 1459, 3), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem reindexCheck34 : Integer.Sparse.reindex keyMap MixedData.row34 = numericRow34 := by decide +kernel

theorem numericCheck34 (x : Master → ℝ) : Integer.Sparse.eval numericRow34 x =
    (1 : ℝ) * reducedSource34 x := by
  norm_num [numericRow34, reducedSource34, Integer.Sparse.eval, Sparse.eval, nodeValue1069, nodeValue1459, nodeValue2285, nodeValue4085]

noncomputable def reducedSource35 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue795 x + ((1 : ℝ) * Sparse.eval nodeValue797 x + ((1 : ℝ) * Sparse.eval nodeValue814 x + ((1 : ℝ) * Sparse.eval nodeValue829 x + ((2 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue1903 x + ((2 : ℝ) * Sparse.eval nodeValue1916 x + ((2 : ℝ) * Sparse.eval nodeValue1927 x + ((2 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

def numericRow35 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, 70), (Sum.inl 3, 80), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 25), (Sum.inr 795, 4320), (Sum.inr 797, 2160), (Sum.inr 814, 2160), (Sum.inr 829, 2160), (Sum.inr 1355, 4320), (Sum.inr 1369, 2160), (Sum.inr 1408, 2160), (Sum.inr 1903, 4320), (Sum.inr 1916, 4320), (Sum.inr 1927, 4320), (Sum.inr 2037, 4320), (Sum.inr 2063, 2160), (Sum.inr 2092, 4320), (Sum.inr 2113, 2160), (Sum.inr 2254, 4320), (Sum.inr 2267, 2160), (Sum.inr 2280, 2160), (Sum.inr 3054, 2160), (Sum.inr 3222, 4320)]

theorem reindexCheck35 : Integer.Sparse.reindex keyMap MixedData.row35 = numericRow35 := by decide +kernel

theorem numericCheck35 (x : Master → ℝ) : Integer.Sparse.eval numericRow35 x =
    (2160 : ℝ) * reducedSource35 x := by
  norm_num [numericRow35, reducedSource35, Integer.Sparse.eval, Sparse.eval, nodeValue795, nodeValue797, nodeValue814, nodeValue829, nodeValue1355, nodeValue1369, nodeValue1408, nodeValue1903, nodeValue1916, nodeValue1927, nodeValue2037, nodeValue2063, nodeValue2092, nodeValue2113, nodeValue2254, nodeValue2267, nodeValue2280, nodeValue3054, nodeValue3222, nodeValue3224, nodeValue3225]
  ring

noncomputable def reducedSource36 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow36 : Integer.Sparse Master := [(Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem reindexCheck36 : Integer.Sparse.reindex keyMap MixedData.row36 = numericRow36 := by decide +kernel

theorem numericCheck36 (x : Master → ℝ) : Integer.Sparse.eval numericRow36 x =
    (1 : ℝ) * reducedSource36 x := by
  norm_num [numericRow36, reducedSource36, Integer.Sparse.eval, Sparse.eval, nodeValue2255, nodeValue2520, nodeValue3156, nodeValue3161, nodeValue3626, nodeValue4084]

noncomputable def reducedSource37 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue1031 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow37 : Integer.Sparse Master := [(Sum.inr 1029, 2), (Sum.inr 1031, 1), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem reindexCheck37 : Integer.Sparse.reindex keyMap MixedData.row37 = numericRow37 := by decide +kernel

theorem numericCheck37 (x : Master → ℝ) : Integer.Sparse.eval numericRow37 x =
    (1 : ℝ) * reducedSource37 x := by
  norm_num [numericRow37, reducedSource37, Integer.Sparse.eval, Sparse.eval, nodeValue1029, nodeValue1031, nodeValue1047, nodeValue1061, nodeValue2255, nodeValue4084]

noncomputable def reducedSource38 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow38 : Integer.Sparse Master := [(Sum.inr 1029, 1), (Sum.inr 2013, 1), (Sum.inr 2096, 1), (Sum.inr 2125, 1), (Sum.inr 2253, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem reindexCheck38 : Integer.Sparse.reindex keyMap MixedData.row38 = numericRow38 := by decide +kernel

theorem numericCheck38 (x : Master → ℝ) : Integer.Sparse.eval numericRow38 x =
    (1 : ℝ) * reducedSource38 x := by
  norm_num [numericRow38, reducedSource38, Integer.Sparse.eval, Sparse.eval, nodeValue1029, nodeValue2013, nodeValue2096, nodeValue2125, nodeValue2253, nodeValue2255, nodeValue4084]

noncomputable def reducedSource39 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1458 x + ((1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow39 : Integer.Sparse Master := [(Sum.inr 1458, 1), (Sum.inr 2013, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2255, 1), (Sum.inr 3156, 1), (Sum.inr 4084, -1)]

theorem reindexCheck39 : Integer.Sparse.reindex keyMap MixedData.row39 = numericRow39 := by decide +kernel

theorem numericCheck39 (x : Master → ℝ) : Integer.Sparse.eval numericRow39 x =
    (1 : ℝ) * reducedSource39 x := by
  norm_num [numericRow39, reducedSource39, Integer.Sparse.eval, Sparse.eval, nodeValue1458, nodeValue2013, nodeValue2026, nodeValue2037, nodeValue2255, nodeValue3156, nodeValue4084]

noncomputable def reducedSource40 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1061 x + ((2 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow40 : Integer.Sparse Master := [(Sum.inr 1061, 1), (Sum.inr 2037, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

theorem reindexCheck40 : Integer.Sparse.reindex keyMap MixedData.row40 = numericRow40 := by decide +kernel

theorem numericCheck40 (x : Master → ℝ) : Integer.Sparse.eval numericRow40 x =
    (1 : ℝ) * reducedSource40 x := by
  norm_num [numericRow40, reducedSource40, Integer.Sparse.eval, Sparse.eval, nodeValue1061, nodeValue2037, nodeValue2136, nodeValue2255, nodeValue2279, nodeValue4084]

noncomputable def reducedSource41 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1462 x + ((2 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow41 : Integer.Sparse Master := [(Sum.inr 1462, 1), (Sum.inr 2096, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3161, 1), (Sum.inr 4084, -1)]

theorem reindexCheck41 : Integer.Sparse.reindex keyMap MixedData.row41 = numericRow41 := by decide +kernel

theorem numericCheck41 (x : Master → ℝ) : Integer.Sparse.eval numericRow41 x =
    (1 : ℝ) * reducedSource41 x := by
  norm_num [numericRow41, reducedSource41, Integer.Sparse.eval, Sparse.eval, nodeValue1462, nodeValue2096, nodeValue2113, nodeValue2255, nodeValue3161, nodeValue4084]

noncomputable def reducedSource42 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1047 x + ((2 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow42 : Integer.Sparse Master := [(Sum.inr 1047, 1), (Sum.inr 2026, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem reindexCheck42 : Integer.Sparse.reindex keyMap MixedData.row42 = numericRow42 := by decide +kernel

theorem numericCheck42 (x : Master → ℝ) : Integer.Sparse.eval numericRow42 x =
    (1 : ℝ) * reducedSource42 x := by
  norm_num [numericRow42, reducedSource42, Integer.Sparse.eval, Sparse.eval, nodeValue1047, nodeValue2026, nodeValue2113, nodeValue2255, nodeValue2266, nodeValue4084]

noncomputable def reducedSource43 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1461 x + ((2 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow43 : Integer.Sparse Master := [(Sum.inr 1461, 1), (Sum.inr 2125, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 4084, -1)]

theorem reindexCheck43 : Integer.Sparse.reindex keyMap MixedData.row43 = numericRow43 := by decide +kernel

theorem numericCheck43 (x : Master → ℝ) : Integer.Sparse.eval numericRow43 x =
    (1 : ℝ) * reducedSource43 x := by
  norm_num [numericRow43, reducedSource43, Integer.Sparse.eval, Sparse.eval, nodeValue1461, nodeValue2125, nodeValue2136, nodeValue2255, nodeValue2520, nodeValue4084]

noncomputable def reducedSource44 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1031 x + ((2 : ℝ) * Sparse.eval nodeValue1458 x + ((1 : ℝ) * Sparse.eval nodeValue1461 x + ((1 : ℝ) * Sparse.eval nodeValue1462 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow44 : Integer.Sparse Master := [(Sum.inr 1031, 1), (Sum.inr 1458, 2), (Sum.inr 1461, 1), (Sum.inr 1462, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem reindexCheck44 : Integer.Sparse.reindex keyMap MixedData.row44 = numericRow44 := by decide +kernel

theorem numericCheck44 (x : Master → ℝ) : Integer.Sparse.eval numericRow44 x =
    (1 : ℝ) * reducedSource44 x := by
  norm_num [numericRow44, reducedSource44, Integer.Sparse.eval, Sparse.eval, nodeValue1031, nodeValue1458, nodeValue1461, nodeValue1462, nodeValue2255, nodeValue4084]

noncomputable def reducedSource45 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow45 : Integer.Sparse Master := [(Sum.inr 1084, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 2290, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem reindexCheck45 : Integer.Sparse.reindex keyMap MixedData.row45 = numericRow45 := by decide +kernel

theorem numericCheck45 (x : Master → ℝ) : Integer.Sparse.eval numericRow45 x =
    (1 : ℝ) * reducedSource45 x := by
  norm_num [numericRow45, reducedSource45, Integer.Sparse.eval, Sparse.eval, nodeValue1084, nodeValue2055, nodeValue2284, nodeValue2290, nodeValue2294, nodeValue4085]

noncomputable def reducedSource46 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1066 x + ((1 : ℝ) * Sparse.eval nodeValue1067 x + ((1 : ℝ) * Sparse.eval nodeValue1068 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow46 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 1067, 1), (Sum.inr 1068, 1), (Sum.inr 1084, 1), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

theorem reindexCheck46 : Integer.Sparse.reindex keyMap MixedData.row46 = numericRow46 := by decide +kernel

theorem numericCheck46 (x : Master → ℝ) : Integer.Sparse.eval numericRow46 x =
    (1 : ℝ) * reducedSource46 x := by
  norm_num [numericRow46, reducedSource46, Integer.Sparse.eval, Sparse.eval, nodeValue1066, nodeValue1067, nodeValue1068, nodeValue1084, nodeValue2284, nodeValue4085]

noncomputable def reducedSource47 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1066 x + ((1 : ℝ) * Sparse.eval nodeValue2040 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((2 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow47 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 2040, 1), (Sum.inr 2283, 1), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

theorem reindexCheck47 : Integer.Sparse.reindex keyMap MixedData.row47 = numericRow47 := by decide +kernel

theorem numericCheck47 (x : Master → ℝ) : Integer.Sparse.eval numericRow47 x =
    (1 : ℝ) * reducedSource47 x := by
  norm_num [numericRow47, reducedSource47, Integer.Sparse.eval, Sparse.eval, nodeValue1066, nodeValue2040, nodeValue2283, nodeValue2284, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
