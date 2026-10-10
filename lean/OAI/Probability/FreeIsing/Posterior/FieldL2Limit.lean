import OAI.Probability.FreeIsing.Conditioning.CovarianceLimit
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

private theorem measurable_artanh_field : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem tendsto_integral_sq_sub_posterior_fields
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ m) (f X : Ω → ℝ) {K : ℝ}
    (hb : ∀ n, ∀ᵐ ω ∂μ,
      Real.tanh (X ω - K) ≤ (μ[f | F n]) ω ∧
        (μ[f | F n]) ω ≤ Real.tanh (X ω + K)) :
    Tendsto (fun n => ∫ ω,
      (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hs : (⨆ n, F n) ≤ m := iSup_le (fun n => F.le n)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono (F.le n)).measurable).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | ⨆ n, F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono hs).measurable).aestronglyMeasurable
  have hlim := tendsto_posterior_fields_ae μ F f X K hb
  have hbfield (n : ℕ) : ∀ᵐ ω ∂μ,
      |Real.artanh ((μ[f | F n]) ω) - X ω| ≤ K := by
    filter_upwards [hb n] with ω hω
    exact (posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => (μ[f | F n]) ω) tendsto_const_nhds
      (fun _ => hω)).2.1
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖(Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2‖ ≤ (2 * K) ^ 2 := by
    filter_upwards [hbfield n, hlim] with ω hn hω
    have hd : |Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)| ≤ 2 * K := by
      calc
        _ = |(Real.artanh ((μ[f | F n]) ω) - X ω) -
            (Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω)| := by congr 1; ring
        _ ≤ |Real.artanh ((μ[f | F n]) ω) - X ω| +
            |Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hω.2.1]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hzero : ∀ᵐ ω ∂μ, Tendsto
      (fun n => (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    simpa using (hω.2.2.sub_const (Real.artanh ((μ[f | ⨆ n, F n]) ω))).pow 2
  simpa using tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (2 * K) ^ 2) (fun n => ((hm n).sub hm').pow 2)
    (integrable_const _) hbound hzero

open PlantedSymmetry

theorem HasFreeIsingLaw.finiteGibbsField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => Real.artanh (finiteGibbsSpinMean beta v n (observation t p)))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v (observation t p)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta
    (connectedExhaustion v n) (connectedExhaustion_connected v n) t
      ⟨v, mem_connectedExhaustion v n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (finiteObservationFiltration (connectedExhaustion v)
      (connectedExhaustion_monotone v) t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup (connectedExhaustion v)
    (connectedExhaustion_monotone v)
    (fun w => (eventually_mem_connectedExhaustion v w).exists) t] at hlim
  have hce (n : ℕ) := hμ.finiteObservation_condExp (connectedExhaustion v n)
    (connectedExhaustion_connected v n) t
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
  filter_upwards [hlim, ae_all_iff.mpr hce,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp hce hinf
  convert hp.2.2 using 1
  · ext n
    exact congrArg Real.artanh (hce n).symm
  · exact congrArg (fun x : ℝ => 𝓝 (Real.artanh x)) hinf

theorem HasFreeIsingLaw.finiteGibbsField_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (Real.artanh (finiteGibbsSpinMean beta v n (observation t p)) -
        Real.artanh (infiniteGibbsSpinMean beta v (observation t p))) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta
    (connectedExhaustion v n) (connectedExhaustion_connected v n) t
      ⟨v, mem_connectedExhaustion v n⟩
  have hlim := tendsto_integral_sq_sub_posterior_fields
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (finiteObservationFiltration (connectedExhaustion v)
      (connectedExhaustion_monotone v) t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v)
    hb
  rw [finiteObservationFiltration_iSup (connectedExhaustion v)
    (connectedExhaustion_monotone v)
    (fun w => (eventually_mem_connectedExhaustion v w).exists) t] at hlim
  convert hlim using 1
  ext n
  apply integral_congr_ae
  filter_upwards [hμ.finiteObservation_condExp (connectedExhaustion v n)
    (connectedExhaustion_connected v n) t
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩)),
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hfinite hinf
  change _ = (Real.artanh (_) - Real.artanh
    (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)) ^ 2
  rw [hinf]
  congr 2
  exact congrArg Real.artanh hfinite.symm

theorem HasFreeIsingLaw.finiteGibbsField_brownian_tendsto_ae
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      Tendsto (fun n => Real.artanh (finiteGibbsSpinMean beta v n y))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v y))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hlim := hμ.finiteGibbsField_tendsto_ae hbeta t v
  rw [← hT.map_eq] at hlim
  have hlim' := ae_of_ae_map hT.measurable.aemeasurable hlim
  exact hlim'

theorem HasFreeIsingLaw.finiteGibbsField_brownian_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      (Real.artanh (finiteGibbsSpinMean beta v n y) -
        Real.artanh (infiniteGibbsSpinMean beta v y)) ^ 2
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
  have hlim := hμ.finiteGibbsField_tendsto_meanSquare hbeta t v
  convert hlim using 1
  ext n
  let f : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ := fun p =>
    (Real.artanh (finiteGibbsSpinMean beta v n (observation t p)) -
      Real.artanh (infiniteGibbsSpinMean beta v (observation t p))) ^ 2
  have hf : Measurable f :=
    ((measurable_artanh_field.comp ((continuous_finiteGibbsSpinMean beta v n).measurable.comp
      (measurable_observation t))).sub
      (measurable_artanh_field.comp ((measurable_infiniteGibbsSpinMean beta v).comp
        (measurable_observation t)))).pow_const 2
  change (∫ p, f (T p) ∂μ.prod (Measure.infinitePi ν)) =
    ∫ p, f p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable]

theorem HasFreeIsingLaw.finiteGibbsField_brownian_discrepancy_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      |Real.artanh (finiteGibbsSpinMean beta v n y) -
        Real.artanh (infiniteGibbsSpinMean beta v y)| ≤ 2 * ((d : ℝ) * beta) := by
  filter_upwards [hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν hB hmB t v]
    with p hp
  let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
  have hfin := finite_tree_gibbs_field_uniform_bound (connectedExhaustion v n) hbeta
    ((connectedExhaustion v n).restrict y) ⟨v, mem_connectedExhaustion v n⟩
  change |Real.artanh (finiteGibbsSpinMean beta v n y) - y v| ≤ (d : ℝ) * beta at hfin
  change |Real.artanh (finiteGibbsSpinMean beta v n y) -
    Real.artanh (infiniteGibbsSpinMean beta v y)| ≤ _
  have hinf : |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| ≤ (d : ℝ) * beta := hp.2
  calc
    _ = |(Real.artanh (finiteGibbsSpinMean beta v n y) - y v) -
        (Real.artanh (infiniteGibbsSpinMean beta v y) - y v)| := by congr 1; ring
    _ ≤ |Real.artanh (finiteGibbsSpinMean beta v n y) - y v| +
        |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| := abs_sub _ _
    _ ≤ _ := by linarith

theorem HasFreeIsingLaw.finiteGibbsField_brownian_tendsto_timeMeanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] (v : TreeVertex d) :
    Tendsto (fun n => ∫ q,
      let y := fun i => (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i)
      (Real.artanh (finiteGibbsSpinMean beta v n y) -
        Real.artanh (infiniteGibbsSpinMean beta v y)) ^ 2
          ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let Y : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      TreeVertex d → ℝ := fun q i =>
    (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    have hnoise : Measurable (Function.uncurry (B i)) :=
      measurable_uncurry_of_continuous_of_measurable (hcB i) (hmB i)
    have hspin : Measurable (fun q : ℝ≥0 ×
        ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) => spinSign (q.2.1 i)) :=
      (measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    exact ((measurable_subtype_coe.comp measurable_fst).mul hspin).add
      (hnoise.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  let Z n q := Real.artanh (finiteGibbsSpinMean beta v n (Y q)) -
    Real.artanh (infiniteGibbsSpinMean beta v (Y q))
  have hZ (n : ℕ) : Measurable (Z n) :=
    (measurable_artanh_field.comp ((continuous_finiteGibbsSpinMean beta v n).measurable.comp hY)).sub
      (measurable_artanh_field.comp ((measurable_infiniteGibbsSpinMean beta v).comp hY))
  have hbound (n : ℕ) : ∀ᵐ t ∂τ, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      ‖Z n (t, p)‖ ≤ 2 * ((d : ℝ) * beta) := by
    filter_upwards with t
    simpa only [Real.norm_eq_abs] using
      hμ.finiteGibbsField_brownian_discrepancy_bound hbeta ν hB hmB t v n
  have hzero : ∀ᵐ t ∂τ, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => Z n (t, p)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with t
    filter_upwards [hμ.finiteGibbsField_brownian_tendsto_ae hbeta ν hB hmB t v]
      with p hp
    simpa only [Z, Y, sub_self] using hp.sub_const
      (Real.artanh (infiniteGibbsSpinMean beta v (Y (t, p))))
  have hlim := tendsto_integral_prod_sq_sub_of_bounded_ae τ
    (μ.prod (Measure.infinitePi ν)) hZ (measurable_const (a := (0 : ℝ)))
    (show 0 ≤ 2 * ((d : ℝ) * beta) by positivity) hbound
    (by filter_upwards with t; filter_upwards with p; simp; positivity) hzero
  simpa only [sub_zero] using hlim

end Problem367

end

end OAI
