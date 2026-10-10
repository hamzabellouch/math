import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367

private theorem measurable_artanh_variance : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem tendstoInMeasure_comp_measurePreserving_real
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {S : Ω → Ξ}
    (hS : MeasurePreserving S P Q) {l : Filter ι}
    {f : ι → Ξ → ℝ} {g : Ξ → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hgm : Measurable g)
    (hfg : TendstoInMeasure Q f l g) :
    TendstoInMeasure P (fun i ω => f i (S ω)) l (fun ω => g (S ω)) := by
  intro ε hε
  have heq (i : ι) : P {ω | ε ≤ edist (f i (S ω)) (g (S ω))} =
      Q {ξ | ε ≤ edist (f i ξ) (g ξ)} := by
    exact hS.measure_preimage
      ((measurableSet_le measurable_const ((hfm i).edist hgm)).nullMeasurableSet)
  simpa only [heq] using hfg ε hε

theorem tendsto_integral_artanh_difference_sq_of_inMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {l : Filter ι} [l.IsCountablyGenerated]
    {f g : ι → Ω → ℝ} {f₀ g₀ : Ω → ℝ} {C : ℝ}
    (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i))
    (hf : TendstoInMeasure P f l f₀) (hg : TendstoInMeasure P g l g₀)
    (hfi : ∀ᵐ ω ∂P, f₀ ω ∈ Ioo (-1 : ℝ) 1)
    (hgi : ∀ᵐ ω ∂P, g₀ ω ∈ Ioo (-1 : ℝ) 1)
    (hb : ∀ᶠ i in l, ∀ᵐ ω ∂P, |Real.artanh (f i ω) - Real.artanh (g i ω)| ≤ C) :
    Tendsto (fun i => ∫ ω, (Real.artanh (f i ω) - Real.artanh (g i ω)) ^ 2 ∂P)
      l (𝓝 (∫ ω, (Real.artanh (f₀ ω) - Real.artanh (g₀ ω)) ^ 2 ∂P)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hfae⟩ := (hf.comp hns).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hgae⟩ := (hg.comp (hns.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, ?_⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => C ^ 2)
  · filter_upwards [] with n
    exact (((measurable_artanh_variance.comp (hfm _)).sub
      (measurable_artanh_variance.comp (hgm _))).pow_const 2).aestronglyMeasurable
  · filter_upwards [(hns.comp (hms.tendsto_atTop.comp hks.tendsto_atTop)).eventually hb] with n hn
    filter_upwards [hn] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, Function.comp_def] using pow_le_pow_left₀ (abs_nonneg _) hω 2
  · exact integrable_const _
  · filter_upwards [hfae, hgae, hfi, hgi] with ω hωf hωg hωfi hωgi
    have hflim := (hasDerivAt_artanh_interval hωfi).continuousAt.tendsto.comp
      (hωf.comp hks.tendsto_atTop)
    have hglim := (hasDerivAt_artanh_interval hωgi).continuousAt.tendsto.comp hωg
    exact (hflim.sub hglim).pow 2

namespace IsingObservationFactor

open IsingObservationInnovation

theorem continuous_field_difference_energy_of_posterior_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d)
    (htime : ∀ t : ℝ≥0, Tendsto (fun s => ∫ x,
      (posterior beta v s x - posterior beta v t x) ^ 2 ∂observationLaw μ)
      (𝓝 t) (𝓝 0)) :
    Continuous (fun t : ℝ≥0 => ∫ q,
      (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  have : IsProbabilityMeasure (observationLaw μ) := by
    let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
    unfold observationLaw
    infer_instance
  have hm (t : ℝ≥0) : Measurable (posterior beta v t) :=
    (((posterior_progressive beta v).stronglyAdapted t).mono ((filtration d).le t)).measurable
  have hLp (t : ℝ≥0) : MemLp (posterior beta v t) 2 (observationLaw μ) :=
    MemLp.of_bound (hm t).aestronglyMeasurable 1
      (Eventually.of_forall (posterior_norm_le_one beta v t))
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ)
    (rho := (observationLaw μ).map (innovationMap beta)) (eta := kernel beta μ) kernel_graphLaw
  apply continuous_iff_continuousAt.mpr
  intro t
  have hmeasure : TendstoInMeasure (observationLaw μ) (posterior beta v) (𝓝 t)
      (posterior beta v t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare hLp (hLp t) (htime t))
  have hleft := tendstoInMeasure_comp_measurePreserving_real hl hm (hm t) hmeasure
  have hright := tendstoInMeasure_comp_measurePreserving_real hr hm (hm t) hmeasure
  have hleftInterior := hl.quasiMeasurePreserving.ae
    (posterior_mem_Ioo_ae hμ hbeta v t)
  have hrightInterior := hr.quasiMeasurePreserving.ae
    (posterior_mem_Ioo_ae hμ hbeta v t)
  apply tendsto_integral_artanh_difference_sq_of_inMeasure
    (C := 2 * ((t : ℝ) + 1) + 2 * (d : ℝ) * beta)
    (fun s => (hm s).comp hl.measurable) (fun s => (hm s).comp hr.measurable)
    hleft hright hleftInterior hrightInterior
  filter_upwards [(tendsto_id : Tendsto (fun s : ℝ≥0 => s) (𝓝 t) (𝓝 t)).eventually_le_const
    (lt_add_one t)] with s hs
  filter_upwards [IsingConditionalCopyBounds.ae_fieldDifference_bound hμ hbeta
    kernel_graphLaw s v] with q hq
  apply hq.trans
  have hst : (s : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hs
  linarith

end IsingObservationFactor

end Problem367

end

end OAI
