import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Boundary0

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2160 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2160 : Integer.Sparse Master := [(Sum.inr 2165, 1), (Sum.inr 2186, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 2), (Sum.inr 3510, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2160 : Integer.Sparse.reindex keyMap MixedData.row2160 = numericRow2160 := by decide +kernel

theorem numericCheck2160 (x : Master → ℝ) : Integer.Sparse.eval numericRow2160 x =
    (1 : ℝ) * reducedSource2160 x := by
  norm_num [numericRow2160, reducedSource2160, Integer.Sparse.eval, Sparse.eval, nodeValue2165, nodeValue2186, nodeValue3420, nodeValue3457, nodeValue3510, nodeValue4074]

noncomputable def reducedSource2161 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2249 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0))))))

def numericRow2161 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2146, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2249, 1), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

theorem reindexCheck2161 : Integer.Sparse.reindex keyMap MixedData.row2161 = numericRow2161 := by decide +kernel

theorem numericCheck2161 (x : Master → ℝ) : Integer.Sparse.eval numericRow2161 x =
    (1 : ℝ) * reducedSource2161 x := by
  norm_num [numericRow2161, reducedSource2161, Integer.Sparse.eval, Sparse.eval, nodeValue2144, nodeValue2146, nodeValue2152, nodeValue2157, nodeValue2249, nodeValue3591, nodeValue4075]

noncomputable def reducedSource2162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0))))))

def numericRow2162 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2166, 1), (Sum.inr 2272, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

theorem reindexCheck2162 : Integer.Sparse.reindex keyMap MixedData.row2162 = numericRow2162 := by decide +kernel

theorem numericCheck2162 (x : Master → ℝ) : Integer.Sparse.eval numericRow2162 x =
    (1 : ℝ) * reducedSource2162 x := by
  norm_num [numericRow2162, reducedSource2162, Integer.Sparse.eval, Sparse.eval, nodeValue2154, nodeValue2157, nodeValue2158, nodeValue2166, nodeValue2272, nodeValue3595, nodeValue4075]

noncomputable def reducedSource2163 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2148 x + ((2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2257 x + ((1 : ℝ) * Sparse.eval nodeValue3592 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0)))))

def numericRow2163 : Integer.Sparse Master := [(Sum.inr 2148, 1), (Sum.inr 2152, 2), (Sum.inr 2166, 1), (Sum.inr 2257, 1), (Sum.inr 3592, 1), (Sum.inr 4075, -1)]

theorem reindexCheck2163 : Integer.Sparse.reindex keyMap MixedData.row2163 = numericRow2163 := by decide +kernel

theorem numericCheck2163 (x : Master → ℝ) : Integer.Sparse.eval numericRow2163 x =
    (1 : ℝ) * reducedSource2163 x := by
  norm_num [numericRow2163, reducedSource2163, Integer.Sparse.eval, Sparse.eval, nodeValue2148, nodeValue2152, nodeValue2166, nodeValue2257, nodeValue3592, nodeValue4075]

noncomputable def reducedSource2164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3412 x + ((2 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0)))))

def numericRow2164 : Integer.Sparse Master := [(Sum.inr 2658, 1), (Sum.inr 3406, 1), (Sum.inr 3412, 1), (Sum.inr 3417, 2), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

theorem reindexCheck2164 : Integer.Sparse.reindex keyMap MixedData.row2164 = numericRow2164 := by decide +kernel

theorem numericCheck2164 (x : Master → ℝ) : Integer.Sparse.eval numericRow2164 x =
    (1 : ℝ) * reducedSource2164 x := by
  norm_num [numericRow2164, reducedSource2164, Integer.Sparse.eval, Sparse.eval, nodeValue2658, nodeValue3406, nodeValue3412, nodeValue3417, nodeValue3591, nodeValue4075]

noncomputable def reducedSource2165 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2182 x + ((4 : ℝ) * Sparse.eval nodeValue3455 x + ((-1 : ℝ) * Sparse.eval nodeValue4077 x + 0))

def numericRow2165 : Integer.Sparse Master := [(Sum.inr 2182, 2), (Sum.inr 3455, 4), (Sum.inr 4077, -1)]

theorem reindexCheck2165 : Integer.Sparse.reindex keyMap MixedData.row2165 = numericRow2165 := by decide +kernel

theorem numericCheck2165 (x : Master → ℝ) : Integer.Sparse.eval numericRow2165 x =
    (1 : ℝ) * reducedSource2165 x := by
  norm_num [numericRow2165, reducedSource2165, Integer.Sparse.eval, Sparse.eval, nodeValue2182, nodeValue3455, nodeValue4077]

theorem reindexCheck2166 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2166)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow0) := by decide +kernel

theorem reindexCheck2167 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2167)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow1) := by decide +kernel

theorem reindexCheck2168 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2168)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow2) := by decide +kernel

theorem reindexCheck2169 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2169)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow3) := by decide +kernel

theorem reindexCheck2170 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2170)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow4) := by decide +kernel

theorem reindexCheck2171 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2171)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow5) := by decide +kernel

theorem reindexCheck2172 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2172)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow6) := by decide +kernel

theorem reindexCheck2173 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2173)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow7) := by decide +kernel

theorem reindexCheck2174 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2174)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow8) := by decide +kernel

theorem reindexCheck2175 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2175)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow9) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge

end OAI
