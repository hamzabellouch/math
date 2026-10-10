import OAI.Geometry.RCD.Sobolev.SobolevQuadraticEnergy

namespace OAI

/-! # Restricting a mixed energy to the support of its test -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem supported_gamma_integral (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) (A : Set X)
    (hg : ∀ᵐ x ∂μ, x∉A → SobolevSpace.toLp μ hQ g x=0) :
    (∫ x in A, localGamma μ hQ f g x ∂μ)=∫ x, localGamma μ hQ f g x ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hg,localGamma_zero_on_level μ hQ g f 0,localGamma_comm μ hQ f g]
    with x hx hz hc hnot
  rw [hc,hz (hx hnot)]

end RegularPointCoordinates

end

end OAI
