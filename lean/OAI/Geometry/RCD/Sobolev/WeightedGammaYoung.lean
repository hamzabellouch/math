import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # Young's inequality for cutoff-controlled mixed gradient integrals -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weighted_gamma_young_pointwise (f g : SobolevSpace μ hQ)
    {Ω : Set X} {φ χ : X → ℝ} {B t : ℝ} (hB : 0≤B) (ht : 0≤t)
    (hφ : ∀ᵐ x ∂μ.restrict Ω, |φ x|≤B*|χ x|) :
    ∀ᵐ x ∂μ.restrict Ω, 2*t*|φ x*localGamma μ hQ f g x|≤
      (χ x)^2*localGamma μ hQ f f x+t^2*B^2*localGamma μ hQ g g x := by
  filter_upwards [hφ,ae_restrict_of_ae (localGamma_abs_le μ hQ f g),
    ae_restrict_of_ae (localGamma_self μ hQ f),ae_restrict_of_ae (localGamma_self μ hQ g),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g))]
    with x hx hfg hff hgg hfn hgn
  have hb := mul_le_mul hx hfg (abs_nonneg _) (mul_nonneg hB (abs_nonneg _))
  rw [← abs_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ)≤2) ht)
  have hs := sq_nonneg (|χ x| *SobolevSpace.minimalSlope μ hQ f x-
    t*B*SobolevSpace.minimalSlope μ hQ g x)
  rw [hff,hgg]
  nlinarith only [hm,hs,sq_abs (χ x)]

theorem weighted_gamma_young_integral (f g : SobolevSpace μ hQ)
    {Ω : Set X} {φ χ : X → ℝ} {B t C D : ℝ} (hB : 0≤B) (ht : 0≤t)
    (hφ : AEStronglyMeasurable φ (μ.restrict Ω))
    (hχ : AEStronglyMeasurable χ (μ.restrict Ω))
    (hφb : ∀ᵐ x ∂μ.restrict Ω, |φ x|≤D) (hχb : ∀ᵐ x ∂μ.restrict Ω, |χ x|≤C)
    (hdom : ∀ᵐ x ∂μ.restrict Ω, |φ x|≤B*|χ x|) :
    2*t*|∫ x in Ω, φ x*localGamma μ hQ f g x ∂μ|≤
      (∫ x in Ω, (χ x)^2*localGamma μ hQ f f x ∂μ)+
        t^2*B^2*(∫ x in Ω, localGamma μ hQ g g x ∂μ) := by
  have hi := (localGamma_memL1 μ hQ f g).restrict.bdd_mul hφ
    (hφb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hχnorm : ∀ᵐ x ∂μ.restrict Ω, ‖(χ x)^2‖≤C^2 := hχb.mono fun x hx => by
    simpa only [norm_pow,Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hj : Integrable (fun x => (χ x)^2*localGamma μ hQ f f x) (μ.restrict Ω) :=
    (localGamma_memL1 μ hQ f f).restrict.bdd_mul (hχ.pow 2) hχnorm
  have hg : IntegrableOn (localGamma μ hQ g g) Ω μ := (localGamma_memL1 μ hQ g g).restrict
  have hb := integral_mono_ae (hi.abs.const_mul (2*t)) (hj.add (hg.const_mul (t^2*B^2)))
    (weighted_gamma_young_pointwise μ hQ f g hB ht hdom)
  change (∫ x in Ω, 2*t*|φ x*localGamma μ hQ f g x| ∂μ)≤
    ∫ x in Ω, (χ x)^2*localGamma μ hQ f f x+t^2*B^2*localGamma μ hQ g g x ∂μ at hb
  rw [integral_const_mul,integral_add hj (hg.const_mul (t^2*B^2)),integral_const_mul] at hb
  exact (mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) ht)).trans hb

end RegularPointCoordinates

end

end OAI
