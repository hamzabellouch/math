import OAI.Probability.FreeIsing.Posterior.VarianceInverseLimit
import OAI.Probability.FreeIsing.Posterior.VarianceTimeIntegral
import OAI.Probability.FreeIsing.Stochastic.FinitePosteriorVarianceBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

theorem tendsto_integral_prod_sq_of_integral_sq_bound
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (τ : Measure T) [IsFiniteMeasure τ] (μ : Measure Ω) [SFinite μ]
    {Z : ℕ → T × Ω → ℝ} (hZ : ∀ n, Measurable (Z n)) {C : ℝ}
    (hI : ∀ n, ∀ᵐ t ∂τ, Integrable (fun ω => (Z n (t, ω)) ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ t ∂τ, (∫ ω, (Z n (t, ω)) ^ 2 ∂μ) ≤ C)
    (hlim : ∀ᵐ t ∂τ,
      Tendsto (fun n => ∫ ω, (Z n (t, ω)) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q, (Z n q) ^ 2 ∂τ.prod μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : StronglyMeasurable
      (fun t => ∫ ω, (Z n (t, ω)) ^ 2 ∂μ) :=
    ((hZ n).pow_const 2).stronglyMeasurable.integral_prod_right
  have hb (n : ℕ) : ∀ᵐ t ∂τ,
      ‖∫ ω, (Z n (t, ω)) ^ 2 ∂μ‖ ≤ C := by
    filter_upwards [hbound n] with t ht
    rwa [Real.norm_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  have hout (n : ℕ) : Integrable (fun t => ∫ ω, (Z n (t, ω)) ^ 2 ∂μ) τ :=
    Integrable.of_bound (hm n).aestronglyMeasurable C (hb n)
  have hprod (n : ℕ) : Integrable (fun q => (Z n q) ^ 2) (τ.prod μ) := by
    apply (integrable_prod_iff ((hZ n).pow_const 2).aestronglyMeasurable).mpr
    refine ⟨hI n, ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hout n
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : T => C)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const C) hb hlim
  simp only [integral_zero] at hconv
  convert hconv using 1
  ext n
  exact integral_prod _ (hprod n)

open PlantedSymmetry

theorem HasFreeIsingLaw.finiteGibbsInverseVariance_brownian_error_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    let Z := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      (1 - (finiteGibbsSpinMean beta v n y) ^ 2)⁻¹ -
        (1 - (infiniteGibbsSpinMean beta v y) ^ 2)⁻¹
    Integrable (fun p => (Z p) ^ 2) (μ.prod (Measure.infinitePi ν)) ∧
      (∫ p, (Z p) ^ 2 ∂μ.prod (Measure.infinitePi ν)) ≤
        8 * Real.exp (4 * ((d : ℝ) * beta + (t : ℝ)) + 8 * (t : ℝ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let Y := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
  let A := fun p => (1 - (finiteGibbsSpinMean beta v n (Y p)) ^ 2)⁻¹
  let G := fun p => (1 - (infiniteGibbsSpinMean beta v (Y p)) ^ 2)⁻¹
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  have hA : Measurable A :=
    (measurable_const.sub (((continuous_finiteGibbsSpinMean beta v n).measurable.comp
      hY).pow_const 2)).inv
  have hG : Measurable G :=
    (measurable_const.sub (((measurable_infiniteGibbsSpinMean beta v).comp
      hY).pow_const 2)).inv
  obtain ⟨hAi, hAb⟩ := FinitePosteriorVariance.brownian_inverse_variance_moment
    hbeta μ ν hB hmB (connectedExhaustion v n) ⟨v, mem_connectedExhaustion v n⟩ t 2
  obtain ⟨hGi, hGb⟩ := hμ.brownian_gibbs_posterior_inverse_variance_moment
    hbeta ν hB hmB t v 2
  change Integrable (fun p => (A p) ^ 2) P at hAi
  change Integrable (fun p => (G p) ^ 2) P at hGi
  have hA2 := (memLp_two_iff_integrable_sq hA.aestronglyMeasurable).mpr hAi
  have hG2 := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mpr hGi
  have hZi := (hA2.sub hG2).integrable_sq
  change Integrable (fun p => (A p - G p) ^ 2) P at hZi
  change Integrable (fun p => (A p - G p) ^ 2) P ∧ _
  refine ⟨hZi, ?_⟩
  have hle : (∫ p, (A p - G p) ^ 2 ∂P) ≤
      2 * (∫ p, (A p) ^ 2 ∂P) + 2 * (∫ p, (G p) ^ 2 ∂P) := by
    calc
      _ ≤ ∫ p, 2 * (A p) ^ 2 + 2 * (G p) ^ 2 ∂P :=
        integral_mono hZi ((hAi.const_mul 2).add (hGi.const_mul 2))
          (fun p => by nlinarith [sq_nonneg (A p + G p)])
      _ = _ := by rw [integral_add (hAi.const_mul 2) (hGi.const_mul 2),
        integral_const_mul, integral_const_mul]
  change (∫ p, (A p) ^ 2 ∂P) ≤ 2 * Real.exp
    (2 * (2 : ℝ) * ((d : ℝ) * beta + (t : ℝ)) +
      (t : ℝ) * (2 * (2 : ℝ)) ^ 2 / 2) at hAb
  change (∫ p, (G p) ^ 2 ∂P) ≤ 2 * Real.exp
    (2 * (2 : ℝ) * ((d : ℝ) * beta + (t : ℝ)) +
      (t : ℝ) * (2 * (2 : ℝ)) ^ 2 / 2) at hGb
  have he : 2 * (2 : ℝ) * ((d : ℝ) * beta + (t : ℝ)) +
      (t : ℝ) * (2 * (2 : ℝ)) ^ 2 / 2 =
      4 * ((d : ℝ) * beta + (t : ℝ)) + 8 * (t : ℝ) := by ring
  rw [he] at hAb hGb
  change (∫ p, (A p - G p) ^ 2 ∂P) ≤ _
  linarith

theorem HasFreeIsingLaw.finiteGibbsInverseVariance_brownian_tendsto_time_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (v : TreeVertex d) :
    let Z := fun n (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) =>
      let y := fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) +
        B i p.1.toNNReal (p.2.2 i)
      (1 - (finiteGibbsSpinMean beta v n y) ^ 2)⁻¹ -
        (1 - (infiniteGibbsSpinMean beta v y) ^ 2)⁻¹
    let ρ := (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    (∀ n, MemLp (Z n) 2 ρ) ∧
      Tendsto (fun n => ∫ p, (Z n p) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let τ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let P := μ.prod (Measure.infinitePi ν)
  let Y := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i)
  let Z := fun n p => (1 - (finiteGibbsSpinMean beta v n (Y p)) ^ 2)⁻¹ -
    (1 - (infiniteGibbsSpinMean beta v (Y p)) ^ 2)⁻¹
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    have hb : Measurable (Function.uncurry (B i)) :=
      measurable_uncurry_of_continuous_of_measurable (hcB i) (hmB i)
    have hs : Measurable (fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        spinSign (p.2.1 i)) :=
      (measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    exact (measurable_coe_nnreal_real.comp (measurable_real_toNNReal.comp measurable_fst)).mul hs
      |>.add (hb.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  have hZ (n : ℕ) : Measurable (Z n) :=
    ((measurable_const.sub (((continuous_finiteGibbsSpinMean beta v n).measurable.comp
      hY).pow_const 2)).inv).sub
      ((measurable_const.sub ((measurable_brownian_gibbs_posterior_real_time
        beta v B hmB hcB).pow_const 2)).inv)
  have hI (n : ℕ) : ∀ᵐ t ∂τ, Integrable (fun p => (Z n (t, p)) ^ 2) P :=
    ae_of_all _ (fun t =>
      (hμ.finiteGibbsInverseVariance_brownian_error_bound hbeta ν hB hmB t.toNNReal v n).1)
  let C := 8 * Real.exp (4 * ((d : ℝ) * beta + (T : ℝ)) + 8 * (T : ℝ))
  have hbound (n : ℕ) : ∀ᵐ t ∂τ, (∫ p, (Z n (t, p)) ^ 2 ∂P) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (hμ.finiteGibbsInverseVariance_brownian_error_bound
      hbeta ν hB hmB t.toNNReal v n).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have ht' : (t.toNNReal : ℝ) ≤ (T : ℝ) :=
      Real.toNNReal_le_iff_le_coe.mpr ht.2
    linarith only [ht']
  have hlim : ∀ᵐ t ∂τ,
      Tendsto (fun n => ∫ p, (Z n (t, p)) ^ 2 ∂P) atTop (𝓝 0) :=
    ae_of_all _ (fun t =>
      hμ.finiteGibbsInverseVariance_brownian_tendsto_meanSquare hbeta ν hB hmB t.toNNReal v)
  change (∀ n, MemLp (Z n) 2 (τ.prod P)) ∧ _
  refine ⟨?_, tendsto_integral_prod_sq_of_integral_sq_bound τ P hZ hI hbound hlim⟩
  intro n
  apply (memLp_two_iff_integrable_sq (hZ n).aestronglyMeasurable).mpr
  exact (integrable_prod_of_nonneg_section_bound τ P ((hZ n).pow_const 2)
    (fun p => sq_nonneg _) (hI n) (hbound n)).1

end Problem367

end

end OAI
