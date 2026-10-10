import OAI.Analysis.LipschitzHilbert.Estimates.SummationByParts

namespace OAI

/-! Increasing nonnegative coefficient deficits are controlled by raw
prefix sums, independently of the number of stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_monotone_coefficient_sum (w : ℕ → ℝ) (f : ℕ → E) (N : ℕ) (B : ℝ)
    (hB0 : 0 ≤ B) (hw : ∀ i ≤ N, 0 ≤ w i)
    (hmono : ∀ i ≤ N, ∀ j ≤ N, i ≤ j → w i ≤ w j)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range (k+1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (N+1), (w i : ℂ) • f i‖ ≤ 2*w N*B := by
  have hnorm : ‖(w N : ℂ)‖ = w N := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw N le_rfl)]
  have hdiff (i : ℕ) (hi : i ∈ Finset.range N) :
      ‖(w (i+1) : ℂ)-(w i : ℂ)‖ = w (i+1)-w i := by
    have hiN := Finset.mem_range.mp hi
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hmono i (by omega) (i+1) (by omega) (by omega)))]
  have hvariation : ‖(w N : ℂ)‖ +
      ∑ i ∈ Finset.range N, ‖(w (i+1) : ℂ)-(w i : ℂ)‖ ≤ 2*w N := by
    rw [hnorm,Finset.sum_congr rfl hdiff,Finset.sum_range_sub]
    linarith [hw 0 (Nat.zero_le N)]
  exact (norm_weighted_sum_le_variation (fun i => (w i : ℂ)) f N B hB).trans
    (mul_le_mul_of_nonneg_right hvariation hB0)

end LipschitzHilbert

end

end OAI
