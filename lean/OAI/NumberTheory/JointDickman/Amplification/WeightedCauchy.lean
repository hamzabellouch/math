import OAI.NumberTheory.JointDickman.Probability.ResidueHilbert

namespace OAI

/-! # The weighted Cauchy inequality used to eliminate the first label -/

namespace JointDickman
open Finset

/-- The first label needs only the unit-disc bound; its multiplicativity
is used solely in the preceding divisor reindexing. -/
theorem weighted_complex_cauchy {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (g F : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∑ i ∈ s, (w i : ℂ) * g i * F i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖F i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, (w i : ℂ) * g i * F i‖ ≤ ∑ i ∈ s, w i * ‖F i‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    nlinarith [norm_nonneg (F i), mul_nonneg (hw i hi) (norm_nonneg (F i)), hg i hi]
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := w) (g := fun i => w i * ‖F i‖^2) (r := fun i => w i * ‖F i‖)
    hw (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i _ => by ring_nf; exact le_rfl)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs

/-- Factoring a common positive normalization from the finite inequality. -/
theorem normalized_weighted_complex_cauchy {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (g F : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) {N : ℝ} (hN : 0 ≤ N) :
    ‖(∑ i ∈ s, (w i : ℂ) * g i * F i) / (N : ℂ)‖ ^ 2 ≤
      ((∑ i ∈ s, w i) / N) * ((∑ i ∈ s, w i * ‖F i‖ ^ 2) / N) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    div_pow, div_mul_div_comm, ← pow_two]
  exact div_le_div_of_nonneg_right (weighted_complex_cauchy s w g F hw hg) (sq_nonneg N)

end JointDickman

end OAI
