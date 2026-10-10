import OAI.Analysis.LipschitzHilbert.Trees.HierarchyVariation

namespace OAI

/-! The logarithmic budget for relative drops on an active hierarchy path. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def pathDrop (n : ℕ → ℝ) (i : ℕ) : ℝ := (n i - n (i + 1)) / n i

theorem pathDrop_le_log (n : ℕ → ℝ) (i : ℕ)
    (hi : 0 < n i) (hi' : 0 < n (i + 1)) :
    pathDrop n i ≤ Real.log (n i / n (i + 1)) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hi hi')
  rw [inv_div] at h
  calc
    _ = 1 - n (i + 1) / n i := by unfold pathDrop; field_simp
    _ ≤ _ := h

theorem pathDrop_le_one (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hi' : 0 ≤ n (i + 1)) : pathDrop n i ≤ 1 := by
  exact (div_le_one hi).2 (by linarith)

theorem pathDrop_nonnegative (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hmono : n (i + 1) ≤ n i) : 0 ≤ pathDrop n i :=
  div_nonneg (sub_nonneg.mpr hmono) hi.le

theorem active_path_drop_budget (n : ℕ → ℝ) (N : ℕ) {M : ℝ}
    (hM : 0 < M) (hactive : ∀ i < N, M < n i) (hlast : 0 ≤ n N) :
    (∑ i ∈ Finset.range N, pathDrop n i) ≤ 1 + max 0 (Real.log (n 0 / M)) := by
  cases N with
  | zero => simp only [Finset.sum_range_zero]; positivity
  | succ N =>
    have hn (i : ℕ) (hi : i ≤ N) : 0 < n i := hM.trans (hactive i (by omega))
    have hpre : (∑ i ∈ Finset.range N, pathDrop n i) ≤ Real.log (n 0 / n N) := by
      calc
        _ ≤ ∑ i ∈ Finset.range N, Real.log (n i / n (i + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN := Finset.mem_range.mp hi
          exact pathDrop_le_log n i (hn i (by omega)) (hn (i + 1) (by omega))
        _ = _ := sum_log_ratios n N hn
    have hlog : Real.log (n 0 / n N) ≤ Real.log (n 0 / M) := by
      apply Real.log_le_log (div_pos (hn 0 (Nat.zero_le N)) (hn N le_rfl))
      exact div_le_div_of_nonneg_left (hn 0 (Nat.zero_le N)).le hM
        (hactive N (by omega)).le
    have hlastdrop := pathDrop_le_one n N (hn N le_rfl) hlast
    rw [Finset.sum_range_succ]
    linarith [le_max_right 0 (Real.log (n 0 / M))]

end LipschitzHilbert

end

end OAI
