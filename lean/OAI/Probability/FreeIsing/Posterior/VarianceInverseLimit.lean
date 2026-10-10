import OAI.Probability.FreeIsing.Posterior.FieldL2Limit
import OAI.Probability.FreeIsing.Posterior.FinitePosteriorVarianceInverse

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

theorem tendsto_integral_sq_sub_cosh_sq_of_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : ℕ → Ω → ℝ} {G R : Ω → ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (hbF : ∀ n, ∀ᵐ ω ∂μ, |F n ω| ≤ R ω)
    (hbG : ∀ᵐ ω ∂μ, |G ω| ≤ R ω)
    (hdom : Integrable (fun ω => Real.exp (4 * R ω)) μ) :
    Tendsto (fun n => ∫ ω,
      ((Real.cosh (F n ω)) ^ 2 - (Real.cosh (G ω)) ^ 2) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hfour {x r : ℝ} (hx : |x| ≤ r) :
      (Real.cosh x) ^ 4 ≤ Real.exp (4 * r) := by
    calc
      (Real.cosh x) ^ 4 ≤ (Real.exp r) ^ 4 :=
        pow_le_pow_left₀ (Real.cosh_pos x).le
          ((cosh_le_exp_abs x).trans (Real.exp_le_exp.mpr hx)) 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖((Real.cosh (F n ω)) ^ 2 - (Real.cosh (G ω)) ^ 2) ^ 2‖ ≤
        4 * Real.exp (4 * R ω) := by
    filter_upwards [hbF n, hbG] with ω hf hg
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hfour hf, hfour hg,
      sq_nonneg ((Real.cosh (F n ω)) ^ 2 + (Real.cosh (G ω)) ^ 2)]
  have hzero : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ((Real.cosh (F n ω)) ^ 2 - (Real.cosh (G ω)) ^ 2) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    have hc : Tendsto (fun n => (Real.cosh (F n ω)) ^ 2) atTop
        (𝓝 ((Real.cosh (G ω)) ^ 2)) :=
      (Real.continuous_cosh.continuousAt.tendsto.comp hω).pow 2
    have hs := (hc.sub_const ((Real.cosh (G ω)) ^ 2)).pow 2
    convert hs using 1; simp
  simpa using tendsto_integral_of_dominated_convergence
    (fun ω => 4 * Real.exp (4 * R ω))
    (fun n => ((((Real.continuous_cosh.measurable.comp (hF n)).pow_const 2).sub
      ((Real.continuous_cosh.measurable.comp hG).pow_const 2)).pow_const 2).aestronglyMeasurable)
    (hdom.const_mul 4) hbound hzero

private theorem measurable_artanh_inverseLimit : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

open PlantedSymmetry

theorem HasFreeIsingLaw.finiteGibbsInverseVariance_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      ((1 - (finiteGibbsSpinMean beta v n (observation t p)) ^ 2)⁻¹ -
        (1 - (infiniteGibbsSpinMean beta v (observation t p)) ^ 2)⁻¹) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hF (n : ℕ) : Measurable (fun p =>
      Real.artanh (finiteGibbsSpinMean beta v n (observation t p))) :=
    measurable_artanh_inverseLimit.comp
      ((continuous_finiteGibbsSpinMean beta v n).measurable.comp (measurable_observation t))
  have hG : Measurable (fun p =>
      Real.artanh (infiniteGibbsSpinMean beta v (observation t p))) :=
    measurable_artanh_inverseLimit.comp
      ((measurable_infiniteGibbsSpinMean beta v).comp (measurable_observation t))
  have hbF (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |Real.artanh (finiteGibbsSpinMean beta v n (observation t p))| ≤
        (d : ℝ) * beta + (t : ℝ) + |p.2 v| :=
    Filter.Eventually.of_forall (FinitePosteriorVariance.field_abs_le_noise hbeta
      (connectedExhaustion v n) ⟨v, mem_connectedExhaustion v n⟩ t)
  have hbG : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |Real.artanh (infiniteGibbsSpinMean beta v (observation t p))| ≤
        (d : ℝ) * beta + (t : ℝ) + |p.2 v| := by
    filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
      hμ.posterior_field_abs_le_noise hbeta t v] with p heq hb
    rwa [heq]
  have hnoise : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      p.2 v) := (measurable_pi_apply v).comp measurable_snd
  have hbase : Integrable (fun p => Real.exp (4 * |p.2 v|))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    integrable_exp_abs_of_gaussian_bound hnoise (PlantedInformation.noise_hasLaw μ t v)
      (K := 0) (by norm_num) (Filter.Eventually.of_forall (fun p => by simp))
  have hdom : Integrable (fun p =>
      Real.exp (4 * ((d : ℝ) * beta + (t : ℝ) + |p.2 v|)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
    simpa only [mul_add, Real.exp_add] using
      hbase.const_mul (Real.exp (4 * ((d : ℝ) * beta + t)))
  have hlim := tendsto_integral_sq_sub_cosh_sq_of_exp_bound hF hG
    (hμ.finiteGibbsField_tendsto_ae hbeta t v) hbF hbG hdom
  convert hlim using 1
  ext n
  apply integral_congr_ae
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hb
  have hfin : finiteGibbsSpinMean beta v n (observation t p) ∈ Set.Ioo (-1 : ℝ) 1 :=
    FinitePosteriorVariance.spinMean_mem_Ioo beta (connectedExhaustion v n)
      ⟨v, mem_connectedExhaustion v n⟩ (observation t p)
  have hinf : infiniteGibbsSpinMean beta v (observation t p) ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa only [heq] using hb.1
  rw [inverse_spin_variance_eq_cosh_sq hfin, inverse_spin_variance_eq_cosh_sq hinf]

theorem HasFreeIsingLaw.finiteGibbsInverseVariance_brownian_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      ((1 - (finiteGibbsSpinMean beta v n y) ^ 2)⁻¹ -
        (1 - (infiniteGibbsSpinMean beta v y) ^ 2)⁻¹) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hlim := hμ.finiteGibbsInverseVariance_tendsto_meanSquare hbeta t v
  convert hlim using 1
  ext n
  let f : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ := fun p =>
    ((1 - (finiteGibbsSpinMean beta v n (observation t p)) ^ 2)⁻¹ -
      (1 - (infiniteGibbsSpinMean beta v (observation t p)) ^ 2)⁻¹) ^ 2
  have hf : Measurable f :=
    (((measurable_const.sub (((continuous_finiteGibbsSpinMean beta v n).measurable.comp
      (measurable_observation t)).pow_const 2)).inv).sub
      ((measurable_const.sub (((measurable_infiniteGibbsSpinMean beta v).comp
        (measurable_observation t)).pow_const 2)).inv)).pow_const 2
  change (∫ p, f (T p) ∂μ.prod (Measure.infinitePi ν)) =
    ∫ p, f p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable]

end Problem367

end

end OAI
