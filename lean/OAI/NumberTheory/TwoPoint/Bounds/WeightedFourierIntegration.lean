import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Exact finite-sum interchange and the two `L¹` costs in the cutoff
Fourier inversion step. The uniform estimate is used after summing in the
integer variable, so no frequency supremum enters the short sum. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Filter
open scoped Classical

theorem finite_two_integrals {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (A B : ι → ℝ → ℂ) (hA : ∀ i ∈ S, Integrable (A i))
    (hB : ∀ i ∈ S, Integrable (B i)) :
    (∑ i ∈ S, c i * (∫ t, A i t) * (∫ s, B i s)) =
      ∫ t, ∫ s, ∑ i ∈ S, c i * A i t * B i s := by
  symm
  calc
    _ = ∫ t, ∑ i ∈ S, (c i * A i t) * (∫ s, B i s) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [integral_finsetSum _ (fun i hi => (hB i hi).const_mul (c i * A i t))]
        apply sum_congr rfl
        intro i _
        exact integral_const_mul _ _)
    _ = ∑ i ∈ S, ∫ t, (c i * A i t) * (∫ s, B i s) := by
      exact integral_finsetSum _ (fun i hi =>
        ((hA i hi).const_mul (c i)).mul_const (∫ s, B i s))
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [integral_mul_const, integral_const_mul]

/-- A bound uniform in both Fourier parameters incurs exactly the product
of the two `L¹` coefficient masses. -/
theorem norm_two_weighted_integrals (w₁ w₂ : ℝ → ℂ)
    (hw₁ : Integrable w₁) (hw₂ : Integrable w₂)
    (F : ℝ → ℝ → ℂ) (E : ℝ)
    (hF : ∀ t s, ‖F t s‖ ≤ E) :
    ‖∫ t, ∫ s, w₁ t * w₂ s * F t s‖ ≤
      E * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  have hinner (t : ℝ) : ‖∫ s, w₁ t * w₂ s * F t s‖ ≤
      (‖w₁ t‖ * E) * (∫ s, ‖w₂ s‖) := by
    calc
      _ ≤ ∫ s, (‖w₁ t‖ * E) * ‖w₂ s‖ := by
        apply norm_integral_le_of_norm_le (hw₂.norm.const_mul (‖w₁ t‖ * E))
        exact Eventually.of_forall (fun s => by
          rw [norm_mul, norm_mul]
          calc
            _ ≤ ‖w₁ t‖ * ‖w₂ s‖ * E :=
              mul_le_mul_of_nonneg_left (hF t s) (by positivity)
            _ = _ := by ring)
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∫ t, (‖w₁ t‖ * E) * (∫ s, ‖w₂ s‖) := by
      apply norm_integral_le_of_norm_le
        ((hw₁.norm.mul_const E).mul_const (∫ s, ‖w₂ s‖))
      exact Eventually.of_forall hinner
    _ = _ := by rw [integral_mul_const, integral_mul_const]; ring

end TwoPointCorrelations

end OAI
