import OAI.Probability.FreeIsing.Brownian.PosteriorBareResponse
import OAI.Probability.FreeIsing.Energy.ProgressiveIsingCovariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Problem367

theorem HasFreeIsingLaw.infiniteGibbsResponse_eq_brownian_response
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u v : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsResponse beta u v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
      μ.prod (Measure.infinitePi ν)] brownianPosteriorResponse μ ν B t u v := by
  filter_upwards [hμ.infiniteGibbsCovariance_eq_brownian_past ν hB hmB t u v,
    hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t u] with p hc hm
  unfold infiniteGibbsResponse brownianPosteriorResponse posteriorResponse
  rw [hc, hm]

theorem HasFreeIsingLaw.infiniteGibbsResponseRow_strict_bound_brownian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      Summable (fun v => infiniteGibbsResponse beta u v y ^ 2) ∧
      infiniteGibbsResponseRow beta u y ∈ Set.Icc 0
        (1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)) := by
  have heq := (ae_all_iff).2
    (fun v => hμ.infiniteGibbsResponse_eq_brownian_response ν hB hmB t u v)
  filter_upwards [heq,
    hμ.brownian_posteriorResponse_row_bound_of_strict hbeta hstrict ν hB hmB t u]
    with p hp hb
  dsimp only
  have hf : (fun v => infiniteGibbsResponse beta u v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2) =
      fun v => brownianPosteriorResponse μ ν B t u v p ^ 2 := by
    funext v
    exact congrArg (fun x : ℝ => x ^ 2) (hp v)
  unfold infiniteGibbsResponseRow
  rw [hf]
  exact ⟨hb.1, tsum_nonneg (fun _ => sq_nonneg _), hb.2.1⟩

theorem HasFreeIsingLaw.integrable_infiniteGibbsResponseRow_time_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hjoint : ∀ i, Measurable (Function.uncurry (B i)))
    (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] (u : TreeVertex d) :
    Integrable
      (fun z : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        infiniteGibbsResponseRow beta u
          (fun i => (z.1 : ℝ) * spinSign (z.2.1 i) + B i z.1 (z.2.2 i)))
      (ρ.prod (μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hmB (i : TreeVertex d) (t : ℝ≥0) : Measurable (B i t) :=
    (hjoint i).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable
      (fun z : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        infiniteGibbsResponseRow beta u
          (fun i => (z.1 : ℝ) * spinSign (z.2.1 i) + B i z.1 (z.2.2 i))) := by
    apply (measurable_infiniteGibbsResponseRow beta u).comp
    apply Measurable.of_eval
    intro i
    exact ((measurable_subtype_coe.comp measurable_fst).mul
      ((measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
      ((hjoint i).comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  apply (integrable_const (1 + (d : ℝ) * Real.tanh beta ^ 2 /
    (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2))).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  apply Filter.Eventually.of_forall
  intro t
  filter_upwards [hμ.infiniteGibbsResponseRow_strict_bound_brownian
    hbeta hstrict ν hB hmB t u] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg hp.2.1]
  exact hp.2.2

theorem HasFreeIsingLaw.lintegral_infiniteGibbsResponseRow_time_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] (u : TreeVertex d) :
    (∫⁻ t, ∫⁻ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      ∑' v, ENNReal.ofReal (infiniteGibbsResponse beta u v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2)
      ∂μ.prod (Measure.infinitePi ν) ∂ρ) ≤
      ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 /
        (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)) * ρ Set.univ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hpoint (t : ℝ≥0) :
      (∫⁻ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
        ∑' v, ENNReal.ofReal (infiniteGibbsResponse beta u v
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2)
        ∂μ.prod (Measure.infinitePi ν)) ≤
        ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)) := by
    calc
      _ ≤ ∫⁻ _ : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
          ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 /
            (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2))
          ∂μ.prod (Measure.infinitePi ν) := by
        apply lintegral_mono_ae
        filter_upwards [hμ.infiniteGibbsResponseRow_strict_bound_brownian
          hbeta hstrict ν hB hmB t u] with p hp
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.1]
        exact ENNReal.ofReal_le_ofReal hp.2.2
      _ = _ := by simp
  calc
    _ ≤ ∫⁻ _ : ℝ≥0, ENNReal.ofReal (1 + (d : ℝ) * Real.tanh beta ^ 2 /
        (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)) ∂ρ :=
      lintegral_mono hpoint
    _ = _ := by rw [lintegral_const]

theorem HasFreeIsingLaw.lintegral_infiniteGibbsResponseRow_time_lt_top_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] (u : TreeVertex d) :
    (∫⁻ t, ∫⁻ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      ∑' v, ENNReal.ofReal (infiniteGibbsResponse beta u v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2)
      ∂μ.prod (Measure.infinitePi ν) ∂ρ) < ∞ ∧
    (∫⁻ z : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      ∑' v, ENNReal.ofReal (infiniteGibbsResponse beta u v
        (fun i => (z.1 : ℝ) * spinSign (z.2.1 i) + B i z.1 (z.2.2 i)) ^ 2)
      ∂ρ.prod (μ.prod (Measure.infinitePi ν))) < ∞ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  have h := (hμ.lintegral_infiniteGibbsResponseRow_time_of_strict
    hbeta hstrict ν hB hmB ρ u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ρ Set.univ))
  exact ⟨h, (lintegral_prod_le _).trans_lt h⟩

end Problem367

end

end OAI
