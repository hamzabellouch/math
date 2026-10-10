import OAI.Geometry.RCD.Harmonic.BoundedScalarProduct

namespace OAI

/-! # The bounded Sobolev product with a shifted factor -/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem SobolevSpace.shifted_product_coe (u w : SobolevSpace μ hQ) (ε : ℝ) (A C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C) :
    SobolevSpace.toLp μ hQ (ε • w+SobolevSpace.product μ hQ u w A C) =ᵐ[μ]
      fun x => (ε+SobolevSpace.toLp μ hQ u x)*SobolevSpace.toLp μ hQ w x := by
  filter_upwards [SobolevSpace.product_coe μ hQ u w A C hu hw,
    Lp.coeFn_add (ε • SobolevSpace.toLp μ hQ w)
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u w A C)),
    Lp.coeFn_smul ε (SobolevSpace.toLp μ hQ w)] with x hp ha hs
  change (ε • SobolevSpace.toLp μ hQ w+
    SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u w A C)) x = _
  simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hp]
  ring

end RegularPointCoordinates

end

end OAI
