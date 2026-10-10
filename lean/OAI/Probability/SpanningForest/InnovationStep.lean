import OAI.Probability.SpanningForest.InnovationAdapted
import OAI.Probability.SpanningForest.ConditionalInnovation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem336.Innovation

theorem conditional_martingale_increment_error
    {τ Ω : Type*} [Preorder τ] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (ℱ : Filtration τ mΩ) {M : τ → Ω → ℝ}
    (hM : Martingale M ℱ P) {u v : τ} (huv : u ≤ v)
    {Q : Ω → ℝ} {variance : ℝ≥0} {h L σ : ℝ}
    (hQ : HasLaw Q (gaussianReal 0 variance) P) (hQmeas : Measurable Q)
    (hindep : Indep (MeasurableSpace.comap Q (inferInstance : MeasurableSpace ℝ)) (ℱ u) P)
    (hh : 0 ≤ h) (hh₁ : h ≤ 1) (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hvariance : (variance : ℝ) = h * σ ^ 2)
    (hcorrection : ∀ᵐ ω ∂P, |M v ω - M u ω - Q ω| ≤ h * L)
    (hv : (variance : ℝ) ≤ 2) :
    ∀ᵐ ω ∂P,
      ‖P[fun ω => Complex.exp (((M v ω - M u ω : ℝ) : ℂ) * Complex.I) | ℱ u] ω -
        Complex.exp (-(variance : ℂ) / 2)‖ ≤
      (16 * (σ ^ 3 * GaussianBoundedCorrection.standardGaussianAbsMoment 3 + L ^ 3) +
        L * σ + L ^ 2 / 2 + σ ^ 4 / 4) * (h * Real.sqrt h) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  let R : Ω → ℝ := fun ω => M v ω - M u ω - Q ω
  have hD : Integrable (fun ω => M v ω - M u ω) P := by
    simpa only [Pi.sub_def] using (hM.integrable v).sub (hM.integrable u)
  have hR : AEStronglyMeasurable R P := by
    have hr := hD.sub hQ.hasGaussianLaw.integrable
    simpa only [R, Pi.sub_def] using hr.aestronglyMeasurable
  have hcenterD : P[(fun ω => M v ω - M u ω) | ℱ u] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable v) (hM.integrable u) (ℱ u)
    filter_upwards [hsub, hM.condExp_ae_eq huv, hM.condExp_ae_eq (le_refl u)]
      with ω hω hvω huω
    simpa only [Pi.sub_def, Pi.zero_apply, hvω, huω, sub_self] using hω
  have hQR (ω : Ω) : Q ω + R ω = M v ω - M u ω := by
    dsimp only [R]
    ring
  have hcenter : P[(fun ω => Q ω + R ω) | ℱ u] =ᵐ[P] 0 := by
    simp_rw [hQR]
    exact hcenterD
  have hlocal := conditional_gaussian_increment_error (ℱ.le u) hQ hQmeas hindep hR
    hh hh₁ hL hσ hvariance hcorrection hcenter hv
  simpa only [hQR] using hlocal

theorem conditional_nnInnovation_increment_error
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) {b : ℝ → Ω → ℝ}
    (hM : Martingale (nnInnovation X B b) ℱ P)
    (hb : Measurable (Function.uncurry b))
    (hXbound : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (hbbound : ∀ t ω, b t ω ∈ Set.Icc (0 : ℝ) 1)
    {u v : ℝ≥0} (huv : u ≤ v) (hshort : (v : ℝ) - u ≤ 1)
    (hQ : HasLaw (fun ω => B v ω - B u ω) (gaussianReal 0 (v - u)) P)
    (hQmeas : Measurable (fun ω => B v ω - B u ω))
    (hindep : Indep
      (MeasurableSpace.comap (fun ω => B v ω - B u ω) (inferInstance : MeasurableSpace ℝ))
      (ℱ u) P) :
    ∀ᵐ ω ∂P,
      ‖P[fun ω => Complex.exp
          (((nnInnovation X B b v ω - nnInnovation X B b u ω : ℝ) : ℂ) * Complex.I) |
          ℱ u] ω - Complex.exp (-((v - u : ℝ≥0) : ℂ) / 2)‖ ≤
      (16 * (GaussianBoundedCorrection.standardGaussianAbsMoment 3 + 1) + 1 +
        (1 : ℝ) / 2 + 1 / 4) * (((v : ℝ) - u) * Real.sqrt ((v : ℝ) - u)) := by
  have hnonneg : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr huv
  have hvariance : ((v - u : ℝ≥0) : ℝ) = ((v : ℝ) - u) * (1 : ℝ) ^ 2 := by
    simp only [NNReal.coe_sub huv, one_pow, mul_one]
  have hbound : ∀ᵐ ω ∂P,
      |nnInnovation X B b v ω - nnInnovation X B b u ω - (B v ω - B u ω)| ≤
        ((v : ℝ) - u) * 1 := by
    apply Eventually.of_forall
    intro ω
    simpa only [nnInnovation, Real.toNNReal_coe, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, mul_one] using
      innovation_sub_noise_bound X (fun t => B t.toNNReal) hb hXbound hbbound u v ω
  have hv : ((v - u : ℝ≥0) : ℝ) ≤ 2 := by
    rw [NNReal.coe_sub huv]
    linarith
  have hlocal := conditional_martingale_increment_error P ℱ hM huv hQ hQmeas hindep
    hnonneg hshort (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    hvariance hbound hv
  simpa only [one_pow, one_mul] using hlocal

end Problem336.Innovation

end

end OAI
