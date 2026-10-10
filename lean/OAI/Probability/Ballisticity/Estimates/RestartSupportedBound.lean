import Mathlib
import OAI.Probability.Ballisticity.Estimates.RealJointPastRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma countable_restart_supported_bound {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → I) (Y : Ω → S) (κ : I → Measure S) [∀ j, IsProbabilityMeasure (κ j)]
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ j, (μ.restrict (D ⁻¹' {j})).map Y = μ (D ⁻¹' {j}) • κ j)
    (V : I → Prop) (hV : ∀ᵐ a ∂μ, V (D a))
    (f : I → ℝ) (g : I → S → ℝ) (hg : ∀ j, Measurable (g j))
    (C M B : ℝ) (hC : 0≤C) (hB : 0≤B)
    (hf : ∀ j, ‖f j‖≤C) (hM : ∀ j z, ‖g j z‖≤M)
    (hbound : ∀ j, V j → f j ≠ 0 → |∫ z, g j z ∂κ j|≤B) :
    |∫ a, f (D a)*g (D a) (Y a) ∂μ|≤C*B := by
  rw [integral_countable_restart μ D Y κ hD hY hrestart
    (fun j z => f j*g j z) (fun j => (hg j).const_mul _) (C*M)
    (fun j z => by rw [norm_mul]; exact mul_le_mul (hf j) (hM j z) (norm_nonneg _) hC)]
  simp only [integral_const_mul]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun a => f (D a)*(∫ z, g (D a) z ∂κ (D a))) (C := C*B)
    (hV.mono fun a ha => by
      rw [norm_mul]
      by_cases hz : f (D a)=0
      · simp only [hz,norm_zero,zero_mul]; exact mul_nonneg hC hB
      · rw [Real.norm_eq_abs]
        exact mul_le_mul (hf _) (hbound _ ha hz) (abs_nonneg _) hC)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h

end DirectionalTransience

end

end

end OAI
