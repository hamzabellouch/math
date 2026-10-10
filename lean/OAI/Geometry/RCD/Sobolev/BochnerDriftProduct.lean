import OAI.Geometry.RCD.Sobolev.HessianActionProduct
import OAI.Geometry.RCD.Sobolev.LocalMixedSourceIdentity

namespace OAI

/-! # The drift cancellation in the Bochner product rule -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The absolutely continuous part of the Gram Laplacian after removing
its full Bochner measure. -/
def bochnerDrift (K : ℝ) (f g df dg : SobolevSpace μ hQ) : X → ℝ :=
  fun x => 2*K*localGamma μ hQ f g x+localGamma μ hQ f dg x+localGamma μ hQ g df x

omit [ProperSpace X] in
theorem bochnerDrift_integrable (K : ℝ) (f g df dg : SobolevSpace μ hQ) :
    Integrable (bochnerDrift μ hQ K f g df dg) μ :=
  (((localGamma_memL1 μ hQ f g).const_mul (2*K)).add
    (localGamma_memL1 μ hQ f dg)).add (localGamma_memL1 μ hQ g df)

/-- The source terms of the product Gram equation differ from the
Bochner drift by precisely four times the Hessian action. -/
theorem bochnerDrift_product {Ω : Set X} (K : ℝ)
    (f g h df dg dh Fg Fh Gh : SobolevSpace μ hQ)
    (C D E F : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤C)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x|≤D)
    (hdg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤E)
    (hdh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dh x|≤F)
    (hFg : SobolevSpace.toLp μ hQ Fg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hFh : SobolevSpace.toLp μ hQ Fh =ᵐ[μ.restrict Ω] localGamma μ hQ f h) :
    let gh := SobolevSpace.product μ hQ g h C D
    let dgh := SobolevSpace.product μ hQ g dh C F+
      SobolevSpace.product μ hQ h dg D E+(2 : ℝ) • Gh
    (fun x => SobolevSpace.toLp μ hQ g x*bochnerDrift μ hQ K f h df dh x+
      SobolevSpace.toLp μ hQ h x*bochnerDrift μ hQ K f g df dg x+
      SobolevSpace.toLp μ hQ Fh x*SobolevSpace.toLp μ hQ dg x+
      SobolevSpace.toLp μ hQ Fg x*SobolevSpace.toLp μ hQ dh x+
      2*localGamma μ hQ Fh g x+2*localGamma μ hQ Fg h x) =ᵐ[μ.restrict Ω]
      fun x => bochnerDrift μ hQ K f gh df dgh x+
        4*localHessianAction μ hQ f g h Fg Fh Gh x := by
  dsimp only
  filter_upwards [
    ae_restrict_of_ae (localGamma_add_right μ hQ f
      (SobolevSpace.product μ hQ g dh C F+SobolevSpace.product μ hQ h dg D E) ((2 : ℝ) • Gh)),
    ae_restrict_of_ae (localGamma_add_right μ hQ f
      (SobolevSpace.product μ hQ g dh C F) (SobolevSpace.product μ hQ h dg D E)),
    ae_restrict_of_ae (localGamma_smul_right μ hQ 2 f Gh),
    ae_restrict_of_ae (localGamma_product_right μ hQ f g dh C F hg hdh),
    ae_restrict_of_ae (localGamma_product_right μ hQ f h dg D E hh hdg),
    ae_restrict_of_ae (localGamma_product_right μ hQ f g h C D hg hh),
    ae_restrict_of_ae (localGamma_product_left μ hQ g h df C D hg hh),
    ae_restrict_of_ae (localGamma_comm μ hQ Fh g),
    ae_restrict_of_ae (localGamma_comm μ hQ Fg h),hFg,hFh] with
      x ha hb hc hd he hfg hprod hcomm₁ hcomm₂ hr₁ hr₂
  dsimp only [bochnerDrift,localHessianAction]
  rw [ha,hb,hc,hd,he,hfg,hprod,hcomm₁,hcomm₂,hr₁,hr₂]
  ring

end RegularPointCoordinates

end

end OAI
