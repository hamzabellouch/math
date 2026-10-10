import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

/-!
Normalized indicators weight a measurable set by the reciprocal of its real mass.
Finite set mass gives integrability and L² membership for these averaging functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

def normalizedSetIndicator (μ : Measure X) (A : Set X) : X → ℝ :=
  A.indicator (fun _ => (μ.real A)⁻¹)

theorem normalizedSetIndicator_of_mem (μ : Measure X) (A : Set X) (x : X) (hx : x ∈ A) :
    normalizedSetIndicator μ A x = (μ.real A)⁻¹ := indicator_of_mem hx _

theorem normalizedSetIndicator_of_notMem (μ : Measure X) (A : Set X) (x : X) (hx : x ∉ A) :
    normalizedSetIndicator μ A x = 0 := indicator_of_notMem hx _

theorem normalizedSetIndicator_memLp (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hfin : μ A < ∞) : MemLp (normalizedSetIndicator μ A) 2 μ := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  exact (memLp_indicator_iff_restrict hA).mpr (memLp_const _)

theorem normalizedSetIndicator_integrable (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hfin : μ A < ∞) : Integrable (normalizedSetIndicator μ A) μ :=
  (integrable_indicator_iff hA).mpr (integrableOn_const hfin.ne)

theorem normalizedSetIndicator_integral (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x ∂μ) = 1 := by
  rw [normalizedSetIndicator, integral_indicator hA, setIntegral_const, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

theorem normalizedSetIndicator_pairing (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (f : X → ℝ) :
    (∫ x, normalizedSetIndicator μ A x * f x ∂μ) = cellMean (μ.restrict A) f := by
  have heq : (fun x => normalizedSetIndicator μ A x * f x) =
      A.indicator (fun x => (μ.real A)⁻¹ * f x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [normalizedSetIndicator, hx]
  rw [heq, integral_indicator hA, integral_const_mul]
  simp only [cellMean, Measure.real, Measure.restrict_apply_univ, div_eq_mul_inv, mul_comm]

theorem normalizedSetIndicator_sq_integral (μ : Measure X) (A : Set X)
    (hA : MeasurableSet A) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x ^ 2 ∂μ) = (μ.real A)⁻¹ := by
  have heq : (fun x => normalizedSetIndicator μ A x ^ 2) =
      A.indicator (fun _ => ((μ.real A)⁻¹) ^ 2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [normalizedSetIndicator, hx]
  rw [heq, integral_indicator hA, setIntegral_const, smul_eq_mul]
  field_simp

theorem normalizedSetIndicator_nested_product_integral (μ : Measure X) (A B : Set X)
    (hA : MeasurableSet A) (hAB : A ⊆ B) (hpos : 0 < μ.real A) :
    (∫ x, normalizedSetIndicator μ A x * normalizedSetIndicator μ B x ∂μ) = (μ.real B)⁻¹ := by
  have heq : (fun x => normalizedSetIndicator μ A x * normalizedSetIndicator μ B x) =
      A.indicator (fun _ => (μ.real A)⁻¹ * (μ.real B)⁻¹) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [normalizedSetIndicator_of_mem μ A x hx,
        normalizedSetIndicator_of_mem μ B x (hAB hx), indicator_of_mem hx]
    · simp only [normalizedSetIndicator_of_notMem μ A x hx, zero_mul, indicator_of_notMem hx]
  rw [heq, integral_indicator hA, setIntegral_const, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul]

end

end RieszRectifiability

end OAI
