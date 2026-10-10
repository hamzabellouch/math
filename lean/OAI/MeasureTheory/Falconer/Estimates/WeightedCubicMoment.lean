import OAI.MeasureTheory.Falconer.Incidence.CubicIncidence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # The cubic incidence inequality with the original point-slice density -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]

theorem weighted_cubic_incidence_moment (ξ : Measure P) (μ : Measure X)
    [SFinite ξ] [SFinite μ] (w F : P × X → ℝ≥0∞)
    (hw : Measurable w) (hF : Measurable F) :
    (∫⁻ p, ∫⁻ x, w (p,x)*F (p,x) ∂μ ∂ξ)^3 ≤
      (∫⁻ p, ∫⁻ x, w (p,x)*(F (p,x))^3 ∂μ ∂ξ)*
        (∫⁻ p, ∫⁻ x, w (p,x) ∂μ ∂ξ)^2 := by
  let η := (ξ.prod μ).withDensity w
  have hh := cubic_incidence_moment η F hF.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF,
    lintegral_withDensity_eq_lintegral_mul _ hw (hF.pow_const 3)] at hh
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  rw [lintegral_prod _ (hw.mul hF).aemeasurable,
    lintegral_prod _ (hw.mul (hF.pow_const 3)).aemeasurable,
    lintegral_prod _ hw.aemeasurable] at hh
  exact hh

end Falconer

end OAI
