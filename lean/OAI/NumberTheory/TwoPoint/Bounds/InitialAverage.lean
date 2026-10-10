import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-! Compare a nonnegative average on an initial interval with the average
on an integer multiple of that interval. -/

namespace TwoPointCorrelations

open Finset

lemma uniformAverage_initial_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (l N : ℕ) (hl : 0 < l) (hN : 0 < N) :
    uniformAverage (fun t : Fin N => f t.val) ≤
      (l : ℝ) * uniformAverage (fun t : Fin (l * N) => f t.val) := by
  have hNl : N ≤ l * N := by nlinarith
  have hs : (∑ t ∈ range N, f t) ≤ ∑ t ∈ range (l * N), f t :=
    sum_le_sum_of_subset_of_nonneg (range_mono hNl) (fun t _ _ => hf t)
  have hlr : (l : ℝ) ≠ 0 := by positivity
  have hNr : (N : ℝ) ≠ 0 := by positivity
  simp only [uniformAverage, Fintype.card_fin, Fin.sum_univ_eq_sum_range f,
    Nat.cast_mul]
  calc
    _ ≤ (∑ t ∈ range (l * N), f t) / N :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
    _ = _ := by field_simp

end TwoPointCorrelations

end OAI
