import OAI.Analysis.Pureness.Completion.CompletedUniformComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedDiagonalSum (k : ℕ) (a : CornerCompletion A) : A :=
  ∑ i : Fin k, completedCompress A k a i i

lemma completedDiagonalSum_nonneg (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    0 ≤ completedDiagonalSum k a :=
  Finset.sum_nonneg fun i _ => matrix_entry_nonneg _ (completedCompress_nonneg k a ha) i

lemma completedDiagonalSum_mono (k : ℕ) : Monotone (completedDiagonalSum (A := A) k) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  have hp := matrix_entry_nonneg _ (sub_nonneg.mpr (completedCompress_mono k hab)) i
  exact sub_nonneg.mp hp

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrix_diagonalSum_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    (∑ i : Fin l, corner h a i i) = ∑ i : Fin k, a i i := by
  rw [sum_corner_support h _ (fun i hi => corner_row_zero h a i i hi)]
  simp only [corner_apply_cast]

lemma completedDiagonalSum_monotone (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k => completedDiagonalSum k a) := by
  intro k l h
  change (∑ i : Fin k, completedCompress A k a i i) ≤ ∑ i : Fin l, completedCompress A l a i i
  rw [← completedCompress_compat h a, ← matrix_diagonalSum_corner h]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k
  · simp [corner, compress, hi]
  · simp only [corner_row_zero h _ i i hi]
    exact matrix_entry_nonneg _ (completedCompress_nonneg l a ha) i

lemma trace_completedDiagonalSum (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) :
    ENNReal.ofReal (τ.functional (completedDiagonalSum k a)).re = completedTraceValue τ k a := by
  simp only [completedDiagonalSum, map_sum, completedTraceValue, matrixTrace_apply]

def completedSourceU (a : CornerCompletion A) : ℕ → A
  | 0 => 0
  | j + 1 => completedDiagonalSum (j + 1) (nonUnitalRoot a j)

lemma completedSourceU_nonneg (a : CornerCompletion A) (j : ℕ) : 0 ≤ completedSourceU a j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact completedDiagonalSum_nonneg _ _ (nonUnitalRoot_nonneg a j)

lemma completedSourceU_monotone (a : CornerCompletion A) (ha : 0 ≤ a) : Monotone (completedSourceU a) := by
  apply monotone_nat_of_le_succ
  intro j
  cases j with
  | zero => exact completedSourceU_nonneg a 1
  | succ j =>
    exact (completedDiagonalSum_mono _ (nonUnitalRoot_monotone a ha (Nat.le_succ j))).trans
      (completedDiagonalSum_monotone _ (nonUnitalRoot_nonneg a (j + 1)) (Nat.le_succ (j + 1)))

lemma completedSourceU_trace_le (τ : TracialState A) (a : CornerCompletion A) (j : ℕ) :
    ENNReal.ofReal (τ.functional (completedSourceU a j)).re ≤ completedRootRank τ a := by
  cases j with
  | zero => simp [completedSourceU]
  | succ j =>
    rw [completedSourceU, trace_completedDiagonalSum]
    exact (le_iSup (fun k => completedTraceValue τ k (nonUnitalRoot a j)) (j + 1)).trans
      (le_iSup (fun j => completedDiagonalWeight τ (nonUnitalRoot a j)) j)

theorem completedSourceU_trace_iSup (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    (⨆ j : ℕ, ENNReal.ofReal (τ.functional (completedSourceU a j)).re) = completedRootRank τ a := by
  apply le_antisymm (iSup_le (completedSourceU_trace_le τ a))
  apply iSup_le
  intro j
  apply iSup_le
  intro k
  let m := max j k
  calc
    completedTraceValue τ k (nonUnitalRoot a j) ≤ completedTraceValue τ (m + 1) (nonUnitalRoot a j) :=
      completedTraceValue_monotone τ _ (nonUnitalRoot_nonneg a j) ((le_max_right j k).trans (Nat.le_succ m))
    _ ≤ completedTraceValue τ (m + 1) (nonUnitalRoot a m) :=
      completedTraceValue_mono τ _ (nonUnitalRoot_monotone a ha (le_max_left j k))
    _ = ENNReal.ofReal (τ.functional (completedSourceU a (m + 1))).re :=
      (trace_completedDiagonalSum τ _ _).symm
    _ ≤ _ := le_iSup (fun j => ENNReal.ofReal (τ.functional (completedSourceU a j)).re) (m + 1)

theorem completedSourceU_trace_tendsto (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Tendsto (fun j : ℕ => ENNReal.ofReal (τ.functional (completedSourceU a j)).re)
      atTop (𝓝 (completedRootRank τ a)) := by
  rw [← completedSourceU_trace_iSup τ a ha]
  apply tendsto_atTop_iSup
  intro j k hjk
  exact ENNReal.ofReal_le_ofReal (Complex.le_def.mp
    (τ.functional.monotone (completedSourceU_monotone a ha hjk))).1

theorem completedSourceU_increment_nonneg (a : CornerCompletion A) (ha : 0 ≤ a) (s : ℝ)
    (hs : 0 ≤ s) (j : ℕ) : 0 ≤ s • (completedSourceU a (j + 1) - completedSourceU a j) :=
  smul_nonneg hs (sub_nonneg.mpr (completedSourceU_monotone a ha (Nat.le_succ j)))
end CuntzPureness

end

end OAI
