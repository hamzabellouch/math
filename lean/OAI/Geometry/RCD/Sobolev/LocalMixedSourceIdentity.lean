import OAI.Geometry.RCD.Sobolev.MeasureProductEnergy
import OAI.Geometry.RCD.Sobolev.WeightedGammaL2Algebra

namespace OAI

/-! # Integration by parts with a local Sobolev source -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Only the source representative near the test support matters. In
particular, derivatives of a compact extension outside that region vanish
from the mixed Bochner formula. -/
theorem weakLaplacian_local_mixed_identity {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f b ψ : SobolevSpace μ hQ) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d)
    (he : e =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ b)
    (A C : ℝ≥0)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x|≤A)
    (hψb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ ψ x|≤C)
    (q : X → ℝ) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q)
    (hq : tsupport q ⊆ Ω) :
    (∫ x, q x*d x*e x ∂μ)+weightedGamma μ hQ e f ψ =
      -(∫ x, q x*localGamma μ hQ f b x ∂μ) := by
  let B := SobolevSpace.toLp μ hQ b
  let P := SobolevSpace.toLp μ hQ ψ
  have hnB : ∀ᵐ x ∂μ, ‖B x‖≤(A:ℝ) := by simpa only [Real.norm_eq_abs] using hb
  have hnP : ∀ᵐ x ∂μ, ‖P x‖≤(C:ℝ) := by simpa only [Real.norm_eq_abs] using hψb
  have hi := (localGamma_memL1 μ hQ f ψ).bdd_mul (Lp.aestronglyMeasurable B) hnB
  have hj := (localGamma_memL1 μ hQ f b).bdd_mul (Lp.aestronglyMeasurable P) hnP
  have hleft : energyForm μ hQ f (SobolevSpace.product μ hQ b ψ A C) =
      weightedGamma μ hQ B f ψ+weightedGamma μ hQ P f b := by
    rw [← integral_localGamma_eq_energyForm]
    unfold weightedGamma
    rw [← integral_add hi hj]
    exact integral_congr_ae (localGamma_product_right μ hQ f b ψ A C hb hψb)
  have hzero (x : X) (hx : x ∉ Ω) : q x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hq hs))
  have he' := (ae_restrict_iff' hΩ).mp he
  have hsource : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ b ψ A C)) =
      ∫ x, q x*d x*e x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ b ψ A C hb hψb,hψ,he'] with x hx hpx hex
    simp only [Real.inner_apply,hx,hpx]
    by_cases hmem : x ∈ Ω
    · rw [hex hmem]; ring
    · rw [hzero x hmem]; ring
  have hweight : weightedGamma μ hQ e f ψ = weightedGamma μ hQ B f ψ := by
    unfold weightedGamma
    apply integral_congr_ae
    filter_upwards [he',hψ,localGamma_zero_on_level μ hQ ψ f 0,
      localGamma_comm μ hQ f ψ] with x hex hpx hz hc
    by_cases hmem : x ∈ Ω
    · rw [hex hmem]
    · rw [hc,hz (hpx.trans (hzero x hmem)),mul_zero,mul_zero]
  have htest : weightedGamma μ hQ B f ψ+weightedGamma μ hQ P f b =
      -(∫ x, q x*d x*e x ∂μ) := by
    rw [← hleft,hd,hsource]
  have hqΓ : weightedGamma μ hQ P f b = ∫ x, q x*localGamma μ hQ f b x ∂μ := by
    apply integral_congr_ae
    exact hψ.mono fun x hx => congrArg (fun z => z*localGamma μ hQ f b x) hx
  rw [hweight]
  rw [hqΓ] at htest
  linarith only [htest]

end RegularPointCoordinates

end

end OAI
