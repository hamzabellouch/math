import OAI.Probability.FreeIsing.Posterior.VarianceInverse

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace Problem367

theorem integrable_prod_of_nonneg_section_bound
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (ν : Measure T) (μ : Measure Ω) [IsFiniteMeasure ν] [SFinite μ]
    {f : T × Ω → ℝ} (hf : Measurable f)
    (hpos : ∀ p, 0 ≤ f p)
    (hint : ∀ᵐ t ∂ν, Integrable (fun ω => f (t, ω)) μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂ν, (∫ ω, f (t, ω) ∂μ) ≤ C) :
    Integrable f (ν.prod μ) ∧
      (∫ p, f p ∂ν.prod μ) ≤ ν.real univ * C := by
  have hnorm : (fun t => ∫ ω, ‖f (t, ω)‖ ∂μ) =
      (fun t => ∫ ω, f (t, ω) ∂μ) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => Real.norm_of_nonneg (hpos (t, ω)))
  have hsection : Integrable (fun t => ∫ ω, f (t, ω) ∂μ) ν := by
    apply (integrable_const C).mono' hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hbound] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => hpos (t, ω)))]
    exact ht
  have hi : Integrable f (ν.prod μ) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr ⟨hint, hnorm.symm ▸ hsection⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _t, C ∂ν := integral_mono_ae hsection (integrable_const C) hbound
    _ = _ := by simp [integral_const, smul_eq_mul]

theorem measurable_brownian_gibbs_posterior_real_time
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) :
    Measurable (fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      infiniteGibbsSpinMean beta v (fun i =>
        (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i))) := by
  apply (measurable_infiniteGibbsSpinMean beta v).comp
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

private theorem posterior_moment_bound_mono {a K : ℝ} (ha : 0 ≤ a)
    {s t : ℝ≥0} (hst : s ≤ t) :
    2 * Real.exp (a * (K + s) + (s : ℝ) * a ^ 2 / 2) ≤
      2 * Real.exp (a * (K + t) + (t : ℝ) * a ^ 2 / 2) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hst' : (s : ℝ) ≤ t := hst
  exact add_le_add
    (mul_le_mul_of_nonneg_left (show K + (s : ℝ) ≤ K + t by linarith) ha)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hst' (sq_nonneg a))
      (by norm_num))

theorem HasFreeIsingLaw.brownian_gibbs_posterior_exponential_time_moment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (v : TreeVertex d) {a : ℝ} (ha : 0 ≤ a) :
    let F := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      Real.exp (a * |Real.artanh (infiniteGibbsSpinMean beta v
        (fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) +
          B i p.1.toNNReal (p.2.2 i)))|)
    let ρ := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    Integrable F ρ ∧ (∫ p, F p ∂ρ) ≤
      (T : ℝ) * (2 * Real.exp (a * ((d : ℝ) * beta + T) + (T : ℝ) * a ^ 2 / 2)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hm := measurable_brownian_gibbs_posterior_real_time beta v B hmB hcB
  have hart : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have h := integrable_prod_of_nonneg_section_bound
    (volume.restrict (Ioc (0 : ℝ) T)) (μ.prod (Measure.infinitePi ν))
    (((hart.comp hm).abs.const_mul a).exp) (fun _ => Real.exp_nonneg _)
    (C := 2 * Real.exp (a * ((d : ℝ) * beta + T) + (T : ℝ) * a ^ 2 / 2)) ?_ ?_
  · simpa [measureReal_def] using h
  · exact ae_of_all _ (fun t =>
      (hμ.brownian_gibbs_posterior_exponential_moment hbeta ν hB hmB t.toNNReal v ha).1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hμ.brownian_gibbs_posterior_exponential_moment hbeta ν hB hmB t.toNNReal v ha).2.trans
      (posterior_moment_bound_mono ha (Real.toNNReal_le_iff_le_coe.mpr ht.2))

theorem HasFreeIsingLaw.brownian_gibbs_posterior_inverse_variance_time_moment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    let F := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      ((1 - (infiniteGibbsSpinMean beta v
        (fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) +
          B i p.1.toNNReal (p.2.2 i))) ^ 2)⁻¹) ^ n
    let ρ := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    Integrable F ρ ∧ (∫ p, F p ∂ρ) ≤
      (T : ℝ) * (2 * Real.exp ((2 * (n : ℝ)) * ((d : ℝ) * beta + T) +
        (T : ℝ) * (2 * (n : ℝ)) ^ 2 / 2)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hm := measurable_brownian_gibbs_posterior_real_time beta v B hmB hcB
  have h := integrable_prod_of_nonneg_section_bound
    (volume.restrict (Ioc (0 : ℝ) T)) (μ.prod (Measure.infinitePi ν))
    (((hm.pow_const 2).const_sub 1).inv.pow_const n) ?_
    (C := 2 * Real.exp ((2 * (n : ℝ)) * ((d : ℝ) * beta + T) +
      (T : ℝ) * (2 * (n : ℝ)) ^ 2 / 2)) ?_ ?_
  · simpa [measureReal_def] using h
  · intro p
    apply pow_nonneg
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr
      (infiniteGibbsSpinMean_abs_le_one beta v _))
  · exact ae_of_all _ (fun t =>
      (hμ.brownian_gibbs_posterior_inverse_variance_moment hbeta ν hB hmB t.toNNReal v n).1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hμ.brownian_gibbs_posterior_inverse_variance_moment hbeta ν hB hmB t.toNNReal v n).2.trans
      (posterior_moment_bound_mono (by positivity)
        (Real.toNNReal_le_iff_le_coe.mpr ht.2))

theorem HasFreeIsingLaw.ae_locally_integrable_brownian_inverse_variance_pow
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d) :
    ∀ᵐ x ∂μ.prod (Measure.infinitePi ν), ∀ n : ℕ, ∀ T : ℝ≥0,
      IntegrableOn (fun t : ℝ => ((1 - (infiniteGibbsSpinMean beta v
        (fun i => (t.toNNReal : ℝ) * spinSign (x.1 i) +
          B i t.toNNReal (x.2 i))) ^ 2)⁻¹) ^ n) (Ioc 0 (T : ℝ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hlocal : ∀ n k : ℕ, ∀ᵐ x ∂μ.prod (Measure.infinitePi ν),
      IntegrableOn (fun t : ℝ => ((1 - (infiniteGibbsSpinMean beta v
        (fun i => (t.toNNReal : ℝ) * spinSign (x.1 i) +
          B i t.toNNReal (x.2 i))) ^ 2)⁻¹) ^ n) (Ioc 0 (k : ℝ)) := by
    intro n k
    exact (hμ.brownian_gibbs_posterior_inverse_variance_time_moment
      hbeta ν hB hmB hcB (k : ℝ≥0) v n).1.prod_left_ae
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hlocal n))] with x hx
  intro n T
  obtain ⟨k, hk⟩ := exists_nat_gt (T : ℝ)
  exact (hx n k).mono_set (Ioc_subset_Ioc_right hk.le)

end Problem367

end

end OAI
