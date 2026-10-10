import OAI.Geometry.RCD.Sobolev.LocalHessianAction

namespace OAI

/-! # The Hessian action obeys the product rule in a gradient direction -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The extra first-order terms cancel in the three-term Hessian formula.
All products are genuine Sobolev products of bounded representatives. -/
theorem localHessianAction_product {Ω : Set X}
    (f a u v fa fu fv au av : SobolevSpace μ hQ)
    (A B C D E F : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x|≤B)
    (hfuB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ fu x|≤C)
    (hfvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ fv x|≤D)
    (hauB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ au x|≤E)
    (havB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ av x|≤F)
    (hfu : SobolevSpace.toLp μ hQ fu =ᵐ[μ.restrict Ω] localGamma μ hQ f u)
    (hfv : SobolevSpace.toLp μ hQ fv =ᵐ[μ.restrict Ω] localGamma μ hQ f v)
    (hau : SobolevSpace.toLp μ hQ au =ᵐ[μ.restrict Ω] localGamma μ hQ a u)
    (hav : SobolevSpace.toLp μ hQ av =ᵐ[μ.restrict Ω] localGamma μ hQ a v) :
    let uv := SobolevSpace.product μ hQ u v A B
    let fuv := SobolevSpace.product μ hQ u fv A D+SobolevSpace.product μ hQ v fu B C
    let auv := SobolevSpace.product μ hQ u av A F+SobolevSpace.product μ hQ v au B E
    localHessianAction μ hQ f a uv fa fuv auv =ᵐ[μ.restrict Ω] fun x =>
      SobolevSpace.toLp μ hQ u x*localHessianAction μ hQ f a v fa fv av x+
      SobolevSpace.toLp μ hQ v x*localHessianAction μ hQ f a u fa fu au x := by
  dsimp only
  filter_upwards [
    ae_restrict_of_ae (localGamma_add_right μ hQ a
      (SobolevSpace.product μ hQ u fv A D) (SobolevSpace.product μ hQ v fu B C)),
    ae_restrict_of_ae (localGamma_add_right μ hQ f
      (SobolevSpace.product μ hQ u av A F) (SobolevSpace.product μ hQ v au B E)),
    ae_restrict_of_ae (localGamma_product_right μ hQ a u fv A D hu hfvB),
    ae_restrict_of_ae (localGamma_product_right μ hQ a v fu B C hv hfuB),
    ae_restrict_of_ae (localGamma_product_left μ hQ u v fa A B hu hv),
    ae_restrict_of_ae (localGamma_product_right μ hQ f u av A F hu havB),
    ae_restrict_of_ae (localGamma_product_right μ hQ f v au B E hv hauB),
    hfu,hfv,hau,hav] with x ha hf hauv havu huv hfuv hfvu hfu hfv hau hav
  dsimp only [localHessianAction]
  rw [ha,hf,hauv,havu,huv,hfuv,hfvu,hfu,hfv,hau,hav]
  ring

end RegularPointCoordinates

end

end OAI
