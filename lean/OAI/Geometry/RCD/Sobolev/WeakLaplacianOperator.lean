import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # The actual L² Laplacian as a linear operator on its domain -/

open MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- Uniqueness in L² makes the weak Laplacian a linear operator. No
continuity on the whole Sobolev domain is claimed. -/
def weakLaplacianOperator : weakLaplacianDomain μ hQ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := Classical.choose f.property
  map_add' f g := by
    apply IsWeakLaplacian.unique μ hQ (Classical.choose_spec (f+g).property)
    exact (Classical.choose_spec f.property).add μ hQ (Classical.choose_spec g.property)
  map_smul' c f := by
    apply IsWeakLaplacian.unique μ hQ (Classical.choose_spec (c • f).property)
    exact (Classical.choose_spec f.property).smul μ hQ c

@[simp] theorem weakLaplacianOperator_spec (f : weakLaplacianDomain μ hQ) :
    IsWeakLaplacian μ hQ f.val (weakLaplacianOperator μ hQ f) :=
  Classical.choose_spec f.property

end RegularPointCoordinates

end

end OAI
