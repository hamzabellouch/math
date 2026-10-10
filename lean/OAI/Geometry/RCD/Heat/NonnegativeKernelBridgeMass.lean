import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # The mass identity for forward and backward kernel factors

Tonelli identifies their product mass with the composed endpoint kernel.
This form permits noncompact intermediate spaces and needs no integrability
assumption before the endpoint normalization is applied.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
  (μ : Measure A) (ν : Measure B) (σ : Measure Z)
  [SFinite μ] [SFinite ν] [SFinite σ]

theorem nonnegative_kernel_bridge_mass {L : A × Z → ℝ≥0∞} {R : Z × B → ℝ≥0∞}
    (hL : Measurable L) (hR : Measurable R) :
    (∫⁻ z, (∫⁻ a, L (a,z) ∂μ)*(∫⁻ b, R (z,b) ∂ν) ∂σ) =
      ∫⁻ a, ∫⁻ b, ∫⁻ z, L (a,z)*R (z,b) ∂σ ∂ν ∂μ := by
  let S := fun z => ∫⁻ b, R (z,b) ∂ν
  have hS : Measurable S := hR.lintegral_prod_right'
  calc
    _ = ∫⁻ z, ∫⁻ a, L (a,z)*S z ∂μ ∂σ := by
      apply lintegral_congr
      intro z
      exact (lintegral_mul_const (S z)
        (hL.comp (measurable_id.prodMk measurable_const))).symm
    _ = ∫⁻ a, ∫⁻ z, L (a,z)*S z ∂σ ∂μ :=
      lintegral_lintegral_swap
        ((hL.comp measurable_swap).mul (hS.comp measurable_fst)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro a
      calc
        _ = ∫⁻ z, ∫⁻ b, L (a,z)*R (z,b) ∂ν ∂σ := by
          apply lintegral_congr
          intro z
          exact (lintegral_const_mul (L (a,z))
            (hR.comp (measurable_const.prodMk measurable_id))).symm
        _ = _ := lintegral_lintegral_swap
          (((hL.comp (measurable_const.prodMk measurable_fst))).mul hR).aemeasurable

end RegularPointCoordinates

end

end OAI
