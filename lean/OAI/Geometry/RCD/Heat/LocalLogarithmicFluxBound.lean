import OAI.Geometry.RCD.Sobolev.LocalProbabilityGammaBound

namespace OAI

/-! # The cutoff error in the logarithmic heat-density equation -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_logarithmic_flux_bound {Ω : Set X} (hΩ : MeasurableSet Ω)
    (F G : X → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF : ∀ x ∈ Ω, 0 < F x) (hG : ∀ x ∈ Ω, 0 < G x)
    {A B : ℝ} (hFB : ∀ᵐ x ∂μ, |F x| ≤ A) (hGB : ∀ᵐ x ∂μ, |G x| ≤ B)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (F x*G x)))]
    (u v U V w : SobolevSpace μ Q) (c : ℝ)
    (hU : localGamma μ Q U w =ᵐ[μ.restrict Ω] fun x => localGamma μ Q u w x/F x)
    (hV : localGamma μ Q V w =ᵐ[μ.restrict Ω] fun x => localGamma μ Q v w x/G x)
    {L M : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ Q (c • (U+V)) x ≤ L)
    (hM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q w x ≤ M)
    (hw : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q w x = 0) :
    |c*(weightedGamma μ Q G u w+weightedGamma μ Q F v w)| ≤ L*M := by
  have hgi : Integrable (fun x => G x*localGamma μ Q u w x) μ := by
    simpa only [Pi.mul_apply] using (localGamma_memL1 μ Q u w).bdd_mul
      hGm.aestronglyMeasurable (hGB.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  have hfi : Integrable (fun x => F x*localGamma μ Q v w x) μ := by
    simpa only [Pi.mul_apply] using (localGamma_memL1 μ Q v w).bdd_mul
      hFm.aestronglyMeasurable (hFB.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  have he : c*(weightedGamma μ Q G u w+weightedGamma μ Q F v w) =
      ∫ x, localGamma μ Q (c • (U+V)) w x*(F x*G x) ∂μ := by
    rw [weightedGamma,weightedGamma,← integral_add hgi hfi,← integral_const_mul]
    apply integral_congr_ae
    exact (local_logarithmic_sum_flux μ Q hΩ F G hF hG u v U V w c hU hV hw).mono
      fun x hx => hx.trans (by ring)
  rw [he]
  exact local_probability_gamma_bound μ Q hΩ (fun x => F x*G x) (hFm.mul hGm)
    (fun x => mul_nonneg (hF0 x) (hG0 x)) _ w hL0 hL hM hw

end RegularPointCoordinates

end

end OAI
