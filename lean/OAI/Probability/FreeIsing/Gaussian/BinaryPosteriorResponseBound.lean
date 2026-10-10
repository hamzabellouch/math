import OAI.Probability.FreeIsing.Energy.ProgressiveIsingCovariance

namespace OAI

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367
namespace BinaryPosteriorResponseBound

lemma covariance_le_variance_of_pair_bounds {m n p : ℝ}
    (hm : |m| ≤ 1) (hp : |p + n| ≤ 1 + m) (hn : |n - p| ≤ 1 - m) :
    |p - m * n| ≤ 1 - m ^ 2 := by
  have hm0 : 0 ≤ 1 - m := by linarith [(abs_le.mp hm).2]
  have hm1 : 0 ≤ 1 + m := by linarith [(abs_le.mp hm).1]
  have hpU := mul_le_mul_of_nonneg_left (abs_le.mp hp).2 hm0
  have hpL := mul_le_mul_of_nonneg_left (abs_le.mp hp).1 hm0
  have hnU := mul_le_mul_of_nonneg_left (abs_le.mp hn).2 hm1
  have hnL := mul_le_mul_of_nonneg_left (abs_le.mp hn).1 hm1
  rw [abs_le]
  constructor <;> nlinarith

lemma condExp_abs_le_of_abs_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {F : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ omega ∂μ, |f omega| ≤ g omega) :
    ∀ᵐ omega ∂μ, |μ[f | F] omega| ≤ μ[g | F] omega := by
  exact (abs_condExp_ae_le_condExp_abs f).trans (condExp_mono hf.abs hg hfg)

theorem abs_posteriorCovariance_le_one_sub_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable[mΩ] f μ) (hg : AEStronglyMeasurable[mΩ] g μ)
    (hfb : ∀ᵐ omega ∂μ, |f omega| ≤ 1)
    (hgb : ∀ᵐ omega ∂μ, |g omega| ≤ 1) :
    ∀ᵐ omega ∂μ, |posteriorCovariance (mΩ := mΩ) μ F f g omega| ≤ 1 - μ[f | F] omega ^ 2 := by
  have hfi : Integrable f μ := Integrable.of_bound hf 1 (by simpa using hfb)
  have hgi : Integrable g μ := Integrable.of_bound hg 1 (by simpa using hgb)
  have hfg : Integrable (fun omega => f omega * g omega) μ := by
    apply Integrable.of_bound (hf.mul hg) 1
    filter_upwards [hfb, hgb] with omega hf hg
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    simpa using mul_le_mul hf hg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hplus : ∀ᵐ omega ∂μ, |f omega * g omega + g omega| ≤ 1 + f omega := by
    filter_upwards [hfb, hgb] with omega hf hg
    have hnon : 0 ≤ 1 + f omega := by linarith [(abs_le.mp hf).1]
    calc
      |f omega * g omega + g omega| = |(1 + f omega) * g omega| := by congr 1; ring
      _ = (1 + f omega) * |g omega| := by rw [abs_mul, abs_of_nonneg hnon]
      _ ≤ 1 + f omega := by nlinarith
  have hminus : ∀ᵐ omega ∂μ, |g omega - f omega * g omega| ≤ 1 - f omega := by
    filter_upwards [hfb, hgb] with omega hf hg
    have hnon : 0 ≤ 1 - f omega := by linarith [(abs_le.mp hf).2]
    calc
      |g omega - f omega * g omega| = |(1 - f omega) * g omega| := by congr 1; ring
      _ = (1 - f omega) * |g omega| := by rw [abs_mul, abs_of_nonneg hnon]
      _ ≤ 1 - f omega := by nlinarith
  have hp := condExp_abs_le_of_abs_le (mΩ := mΩ) (μ := μ) (F := F) (hfg.add hgi)
    ((integrable_const 1).add hfi) hplus
  have hn := condExp_abs_le_of_abs_le (mΩ := mΩ) (μ := μ) (F := F) (hgi.sub hfg)
    ((integrable_const 1).sub hfi) hminus
  have hm := ae_bdd_norm_condExp_of_ae_bdd_norm (m := F)
    (show ∀ᵐ omega ∂μ, ‖f omega‖ ≤ 1 by simpa using hfb)
  filter_upwards [hp, hn, hm, condExp_add hfg hgi F, condExp_sub hgi hfg F,
    condExp_add (integrable_const (1 : ℝ)) hfi F,
    condExp_sub (integrable_const (1 : ℝ)) hfi F]
    with omega hp hn hm hpa hna hpc hnc
  simp only [Pi.add_apply, Pi.sub_apply, condExp_const hF] at hpa hna hpc hnc
  rw [hpa, hpc] at hp
  rw [hna, hnc] at hn
  exact covariance_le_variance_of_pair_bounds hm hp hn

theorem abs_normalized_posteriorCovariance_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable[mΩ] f μ) (hg : AEStronglyMeasurable[mΩ] g μ)
    (hfb : ∀ᵐ omega ∂μ, |f omega| ≤ 1)
    (hgb : ∀ᵐ omega ∂μ, |g omega| ≤ 1) :
    ∀ᵐ omega ∂μ,
      |posteriorCovariance (mΩ := mΩ) μ F f g omega / (1 - μ[f | F] omega ^ 2)| ≤ 1 := by
  filter_upwards [abs_posteriorCovariance_le_one_sub_sq (mΩ := mΩ) hF hf hg hfb hgb]
    with omega hbound
  have hnon : 0 ≤ 1 - μ[f | F] omega ^ 2 := (abs_nonneg _).trans hbound
  by_cases hzero : 1 - μ[f | F] omega ^ 2 = 0
  · simp [hzero]
  · rw [abs_div, abs_of_nonneg hnon]
    exact (div_le_one (lt_of_le_of_ne hnon (Ne.symm hzero))).mpr hbound

end BinaryPosteriorResponseBound

open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsResponse_abs_le_one_gaussian
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |infiniteGibbsResponse beta v w (observation t p)| ≤ 1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hs : Measurable spinSign := by intro s hs; trivial
  have hm (u : TreeVertex d) : Measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => spinSign (p.1 u)) :=
    hs.comp ((measurable_pi_apply u).comp measurable_fst)
  have hb (u : TreeVertex d) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |spinSign (p.1 u)| ≤ 1 := by
    apply Eventually.of_forall
    intro p
    cases h : p.1 u <;> norm_num [spinSign, h]
  have hc := BinaryPosteriorResponseBound.abs_normalized_posteriorCovariance_le_one
    (observationSigma_le (TreeVertex d) t) (hm v).aestronglyMeasurable
    (hm w).aestronglyMeasurable (hb v) (hb w)
  filter_upwards [hc, hμ.infiniteGibbsCovariance_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hc hcov hmean
  unfold infiniteGibbsResponse
  rw [hcov, hmean]
  exact hc

theorem HasFreeIsingLaw.infiniteGibbsResponse_abs_le_one_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      |infiniteGibbsResponse beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))| ≤ 1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hb := hμ.infiniteGibbsResponse_abs_le_one_gaussian t v w
  rw [← hT.map_eq] at hb
  have hp := ae_of_ae_map hT.measurable.aemeasurable hb
  exact hp

theorem HasFreeIsingLaw.memLp_infiniteGibbsResponse_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) (p : ℝ≥0∞) :
    MemLp (fun q : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsResponse beta v w
        (fun i => (t : ℝ) * spinSign (q.1 i) + B i t (q.2 i))) p
      (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hs : Measurable spinSign := by intro s hs; trivial
  have hobs : Measurable (fun q : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun i => (t : ℝ) * spinSign (q.1 i) + B i t (q.2 i)) :=
    Measurable.of_eval fun i =>
      (measurable_const.mul (hs.comp ((measurable_pi_apply i).comp measurable_fst))).add
        ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  apply MemLp.of_bound ((measurable_infiniteGibbsResponse beta v w).comp hobs).aestronglyMeasurable 1
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    hμ.infiniteGibbsResponse_abs_le_one_brownian ν hB hmB t v w

theorem HasFreeIsingLaw.memLp_infiniteGibbsResponse_time_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (η : Measure ℝ≥0) [IsFiniteMeasure η] (v w : TreeVertex d) (p : ℝ≥0∞) :
    MemLp (fun q : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      infiniteGibbsResponse beta v w
        (fun i => (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i))) p
      (η.prod (μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hs : Measurable spinSign := by intro s hs; trivial
  have hobs : Measurable
      (fun q : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        fun i => (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_subtype_coe.comp measurable_fst).mul
      (hs.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
      ((hjoint i).comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  have hresponse := (measurable_infiniteGibbsResponse beta v w).comp hobs
  apply MemLp.of_bound hresponse.aestronglyMeasurable 1
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le hresponse.norm measurable_const)).mpr
  apply Eventually.of_forall
  intro t
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    hμ.infiniteGibbsResponse_abs_le_one_brownian ν hB hmB t v w

end Problem367

end

end OAI
