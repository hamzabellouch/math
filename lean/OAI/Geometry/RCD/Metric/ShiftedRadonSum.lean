import OAI.Geometry.RCD.Metric.ShiftedRadonBounds

namespace OAI

/-! # Integrating two full Bochner density contributions -/

open MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integral_shifted_radon_sum_le (σ τ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (S : Set X) [IsFiniteMeasure (μ.restrict S)] (c A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    Integrable (fun x => A*((σ.rnDeriv μ x).toReal-c)+B*(τ.rnDeriv μ x).toReal) (μ.restrict S) ∧
    (∫ x in S, (A*((σ.rnDeriv μ x).toReal-c)+B*(τ.rnDeriv μ x).toReal) ∂μ)≤
      A*(σ.real S-c*μ.real S)+B*τ.real S := by
  have hσ := Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)
  have hτ := Measure.integrableOn_toReal_rnDeriv (μ := τ) (ν := μ) (measure_ne_top τ S)
  have hfirst : Integrable (fun x => A*((σ.rnDeriv μ x).toReal-c)) (μ.restrict S) :=
    (hσ.sub (integrable_const c)).const_mul A
  have hsecond : Integrable (fun x => B*(τ.rnDeriv μ x).toReal) (μ.restrict S) := hτ.const_mul B
  refine ⟨hfirst.add hsecond,?_⟩
  rw [integral_add hfirst hsecond,integral_const_mul,integral_const_mul,
    integral_sub hσ (integrable_const c)]
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
  rw [mul_comm (μ.real S) c]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sub_le_sub_right
      (Measure.setIntegral_toReal_rnDeriv_le (μ := σ) (ν := μ) (measure_ne_top σ S)) _) hA)
    (mul_le_mul_of_nonneg_left
      (Measure.setIntegral_toReal_rnDeriv_le (μ := τ) (ν := μ) (measure_ne_top τ S)) hB)

end RegularPointCoordinates

end

end OAI
