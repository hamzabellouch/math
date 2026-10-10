import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MomentRepair

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

def meanCorrection (μ : Measure X) (φ η : X → ℝ) : X → ℝ :=
  fun x => φ x - ((∫ y, φ y ∂μ) / (∫ y, η y ∂μ)) * η x

theorem meanCorrection_integrable (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) :
    Integrable (meanCorrection μ φ η) μ :=
  hφ.sub (hη.const_mul _)

theorem meanCorrection_integral_zero (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) (hne : (∫ x, η x ∂μ) ≠ 0) :
    (∫ x, meanCorrection μ φ η x ∂μ) = 0 := by
  change (∫ x, φ x - ((∫ y, φ y ∂μ) / (∫ y, η y ∂μ)) * η x ∂μ) = 0
  rw [integral_sub hφ (hη.const_mul _), integral_const_mul,
    div_mul_cancel₀ _ hne, sub_self]

theorem meanCorrection_coefficient_tendsto_zero
    (μ : ℕ → Measure X) (φ η : X → ℝ) (b : ℝ) (hb : b ≠ 0)
    (hφ : Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 0))
    (hη : Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 b)) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) := by
  simpa only [zero_div] using! hφ.div hη hb

end

end RieszRectifiability

end OAI
