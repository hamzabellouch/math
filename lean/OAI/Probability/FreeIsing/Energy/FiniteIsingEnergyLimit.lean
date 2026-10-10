import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Gibbs.CovarianceL2Limit
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367

def brownianIsingObservationR {d : ℕ} {Ω : Type*}
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : TreeVertex d → ℝ :=
  fun i => p.1 * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i)

lemma measurable_brownianIsingObservationR
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    Measurable (brownianIsingObservationR B) := by
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      t * spinSign (p.1 i) + B i t.toNNReal (p.2 i))
  · intro p
    exact (continuous_id.mul continuous_const).add
      ((hcB i (p.2 i)).comp continuous_real_toNNReal)
  · intro t
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t.toNNReal).comp ((measurable_pi_apply i).comp measurable_snd))

lemma finiteGibbsCovariance_eq_finiteIsingBrownianCovariance
    {d : ℕ} {Ω : Type*} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)))
    (u : connectedExhaustion v n) :
    finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) =
      finiteIsingBrownianCovariance beta (connectedExhaustion v n)
        ⟨v, mem_connectedExhaustion v n⟩ u B p.1 p.2 := by
  classical
  simp only [finiteGibbsCovariance, dite_eq_left u.property]
  rfl

theorem HasFreeIsingLaw.finiteGibbsCovariance_timeEnergy_le_one
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ p, ∑ u ∈ connectedExhaustion v n,
      finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let D := connectedExhaustion v n
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hi (u : TreeVertex d) : Integrable
      (fun p => finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2)
      (τ.prod ρ) := by
    apply Integrable.of_bound
      (((continuous_finiteGibbsCovariance beta v u n).measurable.comp hX).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v u n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    simpa only [Function.comp_def] using hb
  have hsum : Integrable (fun p => ∑ u ∈ D,
      finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2) (τ.prod ρ) :=
    integrable_finsetSum D (fun u _ => hi u)
  have heq (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑ u ∈ D, finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2) =
      ∑ u : D, finiteIsingBrownianCovariance beta D
        ⟨v, mem_connectedExhaustion v n⟩ u B p.1 p.2 ^ 2 := by
    rw [← Finset.sum_attach D]
    apply Finset.sum_congr rfl
    intro u _
    rw [finiteGibbsCovariance_eq_finiteIsingBrownianCovariance]
  have he := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D
    (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ hT
  dsimp only at he
  calc
    (∫ p, ∑ u ∈ D,
        finiteGibbsCovariance beta v u n (brownianIsingObservationR B p) ^ 2 ∂τ.prod ρ) =
      ∫ t, ∫ p, ∑ u ∈ D,
        finiteGibbsCovariance beta v u n (brownianIsingObservationR B (t, p)) ^ 2 ∂ρ ∂τ :=
      integral_prod _ hsum
    _ = ∫ t in (0 : ℝ)..T, ∫ p, ∑ u : D,
        finiteIsingBrownianCovariance beta D ⟨v, mem_connectedExhaustion v n⟩ u B t p ^ 2 ∂ρ := by
      rw [intervalIntegral.integral_of_le hT]
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with p
      exact heq (t, p)
    _ ≤ 1 := he.2.2.2

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_timeSquareIntegral
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v w : TreeVertex d) {T : ℝ} :
    Tendsto (fun n => ∫ p,
      finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) atTop
      (𝓝 (∫ p, infiniteGibbsCovariance beta v w (brownianIsingObservationR B p) ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hm (n : ℕ) := ((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX)
  have hy := (measurable_infiniteGibbsCovariance beta v w).comp hX
  have hlim : ∀ᵐ p ∂τ.prod ρ,
      Tendsto (fun n => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)) atTop
        (𝓝 (infiniteGibbsCovariance beta v w (brownianIsingObservationR B p))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hm hy)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t.toNNReal v w
    unfold brownianIsingObservationR
    simpa only [Function.comp_def, ρ, Real.coe_toNNReal t ht.1.le] using h
  apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
    (fun n => ((hm n).pow_const 2).aestronglyMeasurable) (integrable_const 4)
  · intro n
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v w n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    simpa only [Function.comp_def] using hb
  · exact hlim.mono (fun p hp => hp.pow 2)

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    Summable (fun w => ∫ p, C w p ^ 2 ∂P) ∧
      (∑' w, ∫ p, C w p ^ 2 ∂P) ≤ 1 ∧
      (∀ᵐ p ∂P, Summable (fun w => C w p ^ 2)) ∧
      Integrable (fun p => ∑' w, C w p ^ 2) P ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hm (w : TreeVertex d) : Measurable (C w) :=
    (measurable_infiniteGibbsCovariance beta v w).comp hX
  have hmn (n : ℕ) (w : TreeVertex d) : Measurable (Cn n w) :=
    (continuous_finiteGibbsCovariance beta v w n).measurable.comp hX
  have hi (w : TreeVertex d) : Integrable (fun p => C w p ^ 2) P := by
    apply Integrable.of_bound ((hm w).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := infiniteGibbsCovariance_abs_le_two beta v w (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    exact hb
  have hin (n : ℕ) (w : TreeVertex d) : Integrable (fun p => Cn n w p ^ 2) P := by
    apply Integrable.of_bound ((hmn n w).pow_const 2).aestronglyMeasurable 4
    filter_upwards with p
    have h := finiteGibbsCovariance_abs_le_two beta v w n (brownianIsingObservationR B p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
    norm_num only [sq_abs] at hb
    exact hb
  have hevent (S : Finset (TreeVertex d)) :
      ∀ᶠ n in atTop, S ⊆ connectedExhaustion v n := by
    induction S using Finset.induction_on with
    | empty => exact Eventually.of_forall fun _ => Finset.empty_subset _
    | @insert w S hw ih =>
      filter_upwards [eventually_mem_connectedExhaustion v w, ih] with n hn hS
      exact Finset.insert_subset hn hS
  have hpartial (S : Finset (TreeVertex d)) (n : ℕ)
      (hS : S ⊆ connectedExhaustion v n) :
      (∑ w ∈ S, ∫ p, Cn n w p ^ 2 ∂P) ≤ 1 := by
    rw [← integral_finsetSum S (fun w _ => hin n w)]
    apply le_trans (integral_mono_ae
      (integrable_finsetSum S (fun w _ => hin n w))
      (integrable_finsetSum (connectedExhaustion v n) (fun w _ => hin n w))
      (Eventually.of_forall (fun p =>
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun w _ _ => sq_nonneg (Cn n w p)))))
    exact hμ.finiteGibbsCovariance_timeEnergy_le_one ν hB hmB hcB v n hT
  have hbound (S : Finset (TreeVertex d)) :
      (∑ w ∈ S, ∫ p, C w p ^ 2 ∂P) ≤ 1 := by
    apply le_of_tendsto
      (tendsto_finsetSum S (fun w _ =>
        hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w))
    exact (hevent S).mono (fun n hn => hpartial S n hn)
  have hs : Summable (fun w => ∫ p, C w p ^ 2 ∂P) :=
    summable_of_sum_le (fun w => integral_nonneg (fun p => sq_nonneg (C w p))) hbound
  have hle : (∑' w, ∫ p, C w p ^ 2 ∂P) ≤ 1 := hs.tsum_le_of_sum_le hbound
  have hrow := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals hi hs
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => (hm w).aestronglyMeasurable) hrow.1 hrow.2
  dsimp only
  refine ⟨hs, hle, hrow.1, hrow.2, ?_⟩
  rw [← hident.tsum_eq]
  exact hle

end Problem367

end

end OAI
