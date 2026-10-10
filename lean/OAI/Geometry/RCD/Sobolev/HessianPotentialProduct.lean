import OAI.Geometry.RCD.Sobolev.HessianActionProduct

namespace OAI

/-! # The Hessian product rule in its potential argument -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The Hessian of a product has the two expected gradient cross terms.
Every entry is the actual three-term Sobolev action. -/
theorem localHessianAction_potential_product {Ω : Set X}
    (f g u v fu fv gu gv uv : SobolevSpace μ hQ)
    (A B C D E F : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x|≤A)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤B)
    (hfuB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ fu x|≤C)
    (hfvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ fv x|≤D)
    (hguB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ gu x|≤E)
    (hgvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ gv x|≤F)
    (hfu : SobolevSpace.toLp μ hQ fu =ᵐ[μ.restrict Ω] localGamma μ hQ f u)
    (hfv : SobolevSpace.toLp μ hQ fv =ᵐ[μ.restrict Ω] localGamma μ hQ f v)
    (hgu : SobolevSpace.toLp μ hQ gu =ᵐ[μ.restrict Ω] localGamma μ hQ g u)
    (hgv : SobolevSpace.toLp μ hQ gv =ᵐ[μ.restrict Ω] localGamma μ hQ g v) :
    let fg := SobolevSpace.product μ hQ f g A B
    let fgU := SobolevSpace.product μ hQ f gu A E+SobolevSpace.product μ hQ g fu B C
    let fgV := SobolevSpace.product μ hQ f gv A F+SobolevSpace.product μ hQ g fv B D
    localHessianAction μ hQ fg u v fgU fgV uv =ᵐ[μ.restrict Ω] fun x =>
      SobolevSpace.toLp μ hQ f x*localHessianAction μ hQ g u v gu gv uv x+
      SobolevSpace.toLp μ hQ g x*localHessianAction μ hQ f u v fu fv uv x+
      localGamma μ hQ f u x*localGamma μ hQ g v x+
      localGamma μ hQ g u x*localGamma μ hQ f v x := by
  dsimp only
  filter_upwards [
    ae_restrict_of_ae (localGamma_add_right μ hQ u
      (SobolevSpace.product μ hQ f gv A F) (SobolevSpace.product μ hQ g fv B D)),
    ae_restrict_of_ae (localGamma_add_right μ hQ v
      (SobolevSpace.product μ hQ f gu A E) (SobolevSpace.product μ hQ g fu B C)),
    ae_restrict_of_ae (localGamma_product_right μ hQ u f gv A F hf hgvB),
    ae_restrict_of_ae (localGamma_product_right μ hQ u g fv B D hg hfvB),
    ae_restrict_of_ae (localGamma_product_right μ hQ v f gu A E hf hguB),
    ae_restrict_of_ae (localGamma_product_right μ hQ v g fu B C hg hfuB),
    ae_restrict_of_ae (localGamma_product_left μ hQ f g uv A B hf hg),
    ae_restrict_of_ae (localGamma_comm μ hQ u f),ae_restrict_of_ae (localGamma_comm μ hQ u g),
    ae_restrict_of_ae (localGamma_comm μ hQ v f),ae_restrict_of_ae (localGamma_comm μ hQ v g),
    hfu,hfv,hgu,hgv] with x ha hb hc hd he hff hhf huf hug hvf hvg hfu hfv hgu hgv
  dsimp only [localHessianAction]
  rw [ha,hb,hc,hd,he,hff,hhf,huf,hug,hvf,hvg,hfu,hfv,hgu,hgv]
  ring

end RegularPointCoordinates

end

end OAI
