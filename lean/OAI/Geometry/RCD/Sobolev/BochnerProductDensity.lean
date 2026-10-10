import OAI.Geometry.RCD.Sobolev.BochnerDriftProduct
import OAI.Geometry.RCD.Sobolev.HessianActionIntegral

namespace OAI

/-! # The integrable density in the Bochner product rule -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def bochnerProductDensity (K : ℝ) (f g h df dg dh Fg Fh : SobolevSpace μ hQ) : X → ℝ :=
  fun x => SobolevSpace.toLp μ hQ g x*bochnerDrift μ hQ K f h df dh x+
    SobolevSpace.toLp μ hQ h x*bochnerDrift μ hQ K f g df dg x+
    SobolevSpace.toLp μ hQ Fh x*SobolevSpace.toLp μ hQ dg x+
    SobolevSpace.toLp μ hQ Fg x*SobolevSpace.toLp μ hQ dh x+
    2*localGamma μ hQ Fh g x+2*localGamma μ hQ Fg h x

omit [ProperSpace X] in
theorem bochnerProductDensity_integrable (K : ℝ)
    (f g h df dg dh Fg Fh : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤C)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x|≤D) :
    Integrable (bochnerProductDensity μ hQ K f g h df dg dh Fg Fh) μ := by
  have hnG : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ g x‖≤(C:ℝ) := by
    simpa only [Real.norm_eq_abs] using hg
  have hnH : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ h x‖≤(D:ℝ) := by
    simpa only [Real.norm_eq_abs] using hh
  have h₁ := (bochnerDrift_integrable μ hQ K f h df dh).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ g)) hnG
  have h₂ := (bochnerDrift_integrable μ hQ K f g df dg).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ h)) hnH
  have h₃ := (Lp.memLp (SobolevSpace.toLp μ hQ Fh)).integrable_mul
    (Lp.memLp (SobolevSpace.toLp μ hQ dg))
  have h₄ := (Lp.memLp (SobolevSpace.toLp μ hQ Fg)).integrable_mul
    (Lp.memLp (SobolevSpace.toLp μ hQ dh))
  simpa only [bochnerProductDensity,Pi.add_apply] using!
    ((((h₁.add h₂).add h₃).add h₄).add ((localGamma_memL1 μ hQ Fh g).const_mul 2)).add
      ((localGamma_memL1 μ hQ Fg h).const_mul 2)

theorem integral_bochnerProductDensity {Ω : Set X} (hΩ : MeasurableSet Ω) (K : ℝ)
    (f g h df dg dh Fg Fh Gh : SobolevSpace μ hQ)
    (C D E F : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤C)
    (hh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ h x|≤D)
    (hdg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤E)
    (hdh : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dh x|≤F)
    (hFg : SobolevSpace.toLp μ hQ Fg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hFh : SobolevSpace.toLp μ hQ Fh =ᵐ[μ.restrict Ω] localGamma μ hQ f h)
    (q : X →ᵇ ℝ) (hqs : tsupport q ⊆ Ω) :
    let gh := SobolevSpace.product μ hQ g h C D
    let dgh := SobolevSpace.product μ hQ g dh C F+
      SobolevSpace.product μ hQ h dg D E+(2 : ℝ) • Gh
    (∫ x, q x*bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x ∂μ) =
      (∫ x, q x*bochnerDrift μ hQ K f gh df dgh x ∂μ)+
      4*(∫ x, q x*localHessianAction μ hQ f g h Fg Fh Gh x ∂μ) := by
  dsimp only
  have hl := (ae_restrict_iff' hΩ).mp
    (bochnerDrift_product μ hQ K f g h df dg dh Fg Fh Gh C D E F hg hh hdg hdh hFg hFh)
  have he : (fun x => q x*bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x) =ᵐ[μ]
      fun x => q x*(bochnerDrift μ hQ K f (SobolevSpace.product μ hQ g h C D) df
        (SobolevSpace.product μ hQ g dh C F+SobolevSpace.product μ hQ h dg D E+(2:ℝ) • Gh) x)+
        4*(q x*localHessianAction μ hQ f g h Fg Fh Gh x) := by
    filter_upwards [hl] with x hx
    by_cases hm : x ∈ Ω
    · rw [show bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x = _ from hx hm]
      ring
    · have hz : q x=0 := image_eq_zero_of_notMem_tsupport (fun hs => hm (hqs hs))
      simp only [hz,zero_mul,mul_zero,add_zero]
  have hi₁ := (bochnerDrift_integrable μ hQ K f (SobolevSpace.product μ hQ g h C D) df
    (SobolevSpace.product μ hQ g dh C F+SobolevSpace.product μ hQ h dg D E+(2:ℝ) • Gh)).bdd_mul
    q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  have hi₂ := (localHessianAction_integrable μ hQ f g h Fg Fh Gh).bdd_mul
    q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  rw [integral_congr_ae he,integral_add hi₁ (hi₂.const_mul 4),integral_const_mul]

end RegularPointCoordinates

end

end OAI
