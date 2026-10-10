import OAI.Probability.FreeIsing.Energy.RowEnergyConvergence
import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalEnergy
import OAI.Probability.FreeIsing.Gibbs.CovarianceRowCauchy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.RowEnergyConvergence

theorem tendsto_tsum_norm_sub_sq_of_energy_tendsto
    {ι H : Type*} [NormedAddCommGroup H]
    {f : ℕ → ι → H} {g : ι → H}
    (hf : ∀ n, Summable (fun i => ‖f n i‖ ^ 2))
    (hg : Summable (fun i => ‖g i‖ ^ 2))
    (hcoordinate : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i)))
    (henergy : Tendsto (fun n => ∑' i, ‖f n i‖ ^ 2) atTop
      (𝓝 (∑' i, ‖g i‖ ^ 2))) :
    (∀ n, Summable (fun i => ‖f n i - g i‖ ^ 2)) ∧
      Tendsto (fun n => ∑' i, ‖f n i - g i‖ ^ 2) atTop (𝓝 0) := by
  classical
  have he (n : ℕ) : Summable (fun i => ‖f n i - g i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => norm_sub_sq_le _ _)
      (((hf n).mul_left 2).add (hg.mul_left 2))
  refine ⟨he, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    exact Eventually.of_forall fun n =>
      ha.trans_le (tsum_nonneg fun i => sq_nonneg ‖f n i - g i‖)
  · intro ε hε
    have htail : Tendsto (fun s : Finset ι =>
        (∑' i, ‖g i‖ ^ 2) - ∑ i ∈ s, ‖g i‖ ^ 2) atTop (𝓝 0) := by
      have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖g i‖ ^ 2)
          atTop (𝓝 (∑' i, ‖g i‖ ^ 2)) := hg.hasSum
      have h : Tendsto (fun s : Finset ι =>
          (∑' i, ‖g i‖ ^ 2) - ∑ i ∈ s, ‖g i‖ ^ 2) atTop
          (𝓝 ((∑' i, ‖g i‖ ^ 2) - (∑' i, ‖g i‖ ^ 2))) :=
        tendsto_const_nhds.sub hsum
      simpa only [sub_self] using h
    obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds
      (by positivity : (0 : ℝ) < ε / 8))).exists
    have hgs : (∑' i : {i // i ∉ s}, ‖g i.1‖ ^ 2) < ε / 8 := by
      have hsplit := hg.sum_add_tsum_subtype_compl s
      linarith
    have hftail : Tendsto (fun n =>
        (∑' i, ‖f n i‖ ^ 2) - ∑ i ∈ s, ‖f n i‖ ^ 2) atTop
        (𝓝 ((∑' i, ‖g i‖ ^ 2) - ∑ i ∈ s, ‖g i‖ ^ 2)) :=
      henergy.sub (tendsto_finsetSum s fun i _ => (hcoordinate i).norm.pow 2)
    have hfinite : Tendsto (fun n => ∑ i ∈ s, ‖f n i - g i‖ ^ 2)
        atTop (𝓝 0) := by
      have h := tendsto_finsetSum s fun i _ => ((hcoordinate i).sub_const (g i)).norm.pow 2
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using h
    filter_upwards [hftail.eventually (gt_mem_nhds
      (show (∑' i, ‖g i‖ ^ 2) - ∑ i ∈ s, ‖g i‖ ^ 2 < ε / 4 by linarith)),
      hfinite.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))]
      with n hn hsmall
    have hfs : (∑' i : {i // i ∉ s}, ‖f n i.1‖ ^ 2) < ε / 4 := by
      have hsplit := (hf n).sum_add_tsum_subtype_compl s
      linarith
    have hbound : (∑' i : {i // i ∉ s}, ‖f n i.1 - g i.1‖ ^ 2) ≤
        2 * (∑' i : {i // i ∉ s}, ‖f n i.1‖ ^ 2) +
          2 * (∑' i : {i // i ∉ s}, ‖g i.1‖ ^ 2) := by
      calc
        _ ≤ ∑' i : {i // i ∉ s},
            (2 * ‖f n i.1‖ ^ 2 + 2 * ‖g i.1‖ ^ 2) :=
          Summable.tsum_le_tsum (fun i => norm_sub_sq_le _ _)
            ((he n).subtype _)
            ((((hf n).subtype _).mul_left 2).add ((hg.subtype _).mul_left 2))
        _ = _ := by
          simpa only [Function.comp_apply, tsum_mul_left] using
            ((((hf n).subtype (fun i => i ∉ s)).mul_left 2).tsum_add
              ((hg.subtype (fun i => i ∉ s)).mul_left 2))
    rw [← (he n).sum_add_tsum_subtype_compl s]
    linarith

theorem tendsto_tsum_integral_sq_sub_of_energy_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → ι → Ω → ℝ} {g : ι → Ω → ℝ}
    (hf : ∀ n i, MemLp (f n i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hfs : ∀ n, Summable (fun i => ∫ ω, f n i ω ^ 2 ∂μ))
    (hgs : Summable (fun i => ∫ ω, g i ω ^ 2 ∂μ))
    (hcoordinate : ∀ i, Tendsto (fun n => ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ)
      atTop (𝓝 0))
    (henergy : Tendsto (fun n => ∑' i, ∫ ω, f n i ω ^ 2 ∂μ) atTop
      (𝓝 (∑' i, ∫ ω, g i ω ^ 2 ∂μ))) :
    (∀ n, Summable (fun i => ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ)) ∧
      Tendsto (fun n => ∑' i, ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by
  let F : ℕ → ι → Lp ℝ 2 μ := fun n i => (hf n i).toLp (f n i)
  let G : ι → Lp ℝ 2 μ := fun i => (hg i).toLp (g i)
  have hF (n : ℕ) (i : ι) : ‖F n i‖ ^ 2 = ∫ ω, f n i ω ^ 2 ∂μ :=
    PredictableL2.norm_toLp_sq (hf n i)
  have hG (i : ι) : ‖G i‖ ^ 2 = ∫ ω, g i ω ^ 2 ∂μ :=
    PredictableL2.norm_toLp_sq (hg i)
  have hFG (n : ℕ) (i : ι) :
      ‖F n i - G i‖ ^ 2 = ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ := by
    change ‖(hf n i).toLp (f n i) - (hg i).toLp (g i)‖ ^ 2 = _
    rw [← MemLp.toLp_sub]
    exact PredictableL2.norm_toLp_sq ((hf n i).sub (hg i))
  have hconv (i : ι) : Tendsto (fun n => F n i) atTop (𝓝 (G i)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have h : Tendsto (fun n => ‖F n i - G i‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hFG] using hcoordinate i
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h.sqrt
  have h := tendsto_tsum_norm_sub_sq_of_energy_tendsto
    (f := F) (g := G)
    (fun n => by simpa only [hF] using hfs n)
    (by simpa only [hG] using hgs) hconv
    (by simpa only [hF, hG] using henergy)
  simpa only [hFG] using h

end Problem367.RowEnergyConvergence

namespace Problem367

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_timeMeanSquare_real
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v w : TreeVertex d) (T : ℝ) :
    Tendsto (fun n => ∫ p,
      (finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) -
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hX := measurable_brownianIsingObservationR hmB hcB
  apply tendsto_integral_prod_sq_sub_of_bounded_ae
    (volume.restrict (Ioc (0 : ℝ) T)) (μ.prod (Measure.infinitePi ν))
    (fun n => (continuous_finiteGibbsCovariance beta v w n).measurable.comp hX)
    ((measurable_infiniteGibbsCovariance beta v w).comp hX) (by norm_num : (0 : ℝ) ≤ 2)
  · exact fun n => Eventually.of_forall fun t => Eventually.of_forall fun p =>
      finiteGibbsCovariance_abs_le_two _ _ _ _ _
  · exact Eventually.of_forall fun t => Eventually.of_forall fun p =>
      infiniteGibbsCovariance_abs_le_two _ _ _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t.toNNReal v w
    dsimp only [Function.comp_def]
    unfold brownianIsingObservationR
    simpa only [Real.coe_toNNReal t ht.1.le] using h

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_fullTimeRowMeanSquare
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let err := fun n w p =>
      (finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) -
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)) ^ 2
    (∀ n, Summable (fun w => ∫ p, err n w p ∂P)) ∧
      (∀ n, Integrable (fun p => ∑' w, err n w p) P) ∧
      Tendsto (fun n => ∑' w, ∫ p, err n w p ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ p, ∑' w, err n w p ∂P) atTop (𝓝 0) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hf (n : ℕ) (w : TreeVertex d) : MemLp (Cn n w) 2 P :=
    (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX)
  have hi (w : TreeVertex d) : MemLp (C w) 2 P :=
    (memLp_two_iff_integrable_sq
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w hX)
  have hfs (n : ℕ) : Summable (fun w => ∫ p, Cn n w p ^ 2 ∂P) := by
    apply summable_of_ne_finset_zero (s := connectedExhaustion v n)
    intro w hw
    simp only [Cn, finiteGibbsCovariance, dite_eq_right hw,
      zero_pow (by decide : 2 ≠ 0), integral_zero]
  have hinf := (hμ.infiniteGibbsCovariance_timeEnergy_eq hd hb hcrit
    ν hB hmB hcB v hT).1
  have henergy : Tendsto (fun n => ∑' w, ∫ p, Cn n w p ^ 2 ∂P) atTop
      (𝓝 (∑' w, ∫ p, C w p ^ 2 ∂P)) := by
    rw [hinf.tsum_eq]
    have hterminal : Tendsto (fun n => ∫ p,
        finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) atTop
        (𝓝 (∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
          ∂μ.prod (Measure.infinitePi ν))) := by
      have h := hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB T.toNNReal v
      rw [Real.coe_toNNReal T hT] at h
      convert h using 1 <;> rfl
    exact hterminal.congr' (Eventually.of_forall fun n =>
      (hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n hT).symm)
  obtain ⟨hs, hlim⟩ := RowEnergyConvergence.tendsto_tsum_integral_sq_sub_of_energy_tendsto
    P hf hi hfs hinf.summable
    (fun w => hμ.finiteGibbsCovariance_tendsto_timeMeanSquare_real ν hB hmB hcB v w T)
    henergy
  dsimp only
  refine ⟨hs, ?_, hlim, ?_⟩
  · intro n
    exact (DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
      (fun w => ((hf n w).sub (hi w)).integrable_sq) (hs n)).2
  · have heq (n : ℕ) :
        (∫ p, ∑' w, (Cn n w p - C w p) ^ 2 ∂P) =
          ∑' w, ∫ p, (Cn n w p - C w p) ^ 2 ∂P := by
      exact (integral_tsum_of_summable_integral_norm
        (fun w => ((hf n w).sub (hi w)).integrable_sq)
        (by simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hs n)).symm
    change Tendsto (fun n => ∫ p, ∑' w, (Cn n w p - C w p) ^ 2 ∂P) atTop (𝓝 0)
    simpa only [heq] using hlim

theorem HasFreeIsingLaw.finiteGibbsCovariance_fullTime_energy_cauchy
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
    (∀ n k, Summable (fun w => ∫ p, (Cn n w p - Cn k w p) ^ 2 ∂P)) ∧
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
        (∑' w, ∫ p, (Cn n w p - Cn k w p) ^ 2 ∂P) < ε := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hf (n : ℕ) (w : TreeVertex d) :
      MemLp (fun p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX)
  have hi (w : TreeVertex d) :
      MemLp (fun p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w hX)
  have hr := hμ.finiteGibbsCovariance_tendsto_fullTimeRowMeanSquare
    hd hb hcrit ν hB hmB hcB v hT
  exact PredictableL2.row_meanSquare_cauchy_of_tendsto hf hi hr.1 hr.2.2.1

end Problem367

end

end OAI
