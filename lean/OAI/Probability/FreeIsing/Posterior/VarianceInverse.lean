import OAI.Probability.FreeIsing.Conditioning.PlantedInformation
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem exp_mul_abs_le_exp_add_exp_neg (a x : ℝ) :
    Real.exp (a * |x|) ≤ Real.exp (a * x) + Real.exp (-a * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, mul_neg, neg_mul]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

theorem integrable_exp_abs_of_gaussian_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F B : Ω → ℝ} {t : ℝ≥0} {K a : ℝ}
    (hF : Measurable F) (hB : HasLaw B (gaussianReal 0 t) μ)
    (ha : 0 ≤ a) (hbound : ∀ᵐ ω ∂μ, |F ω| ≤ K + |B ω|) :
    Integrable (fun ω => Real.exp (a * |F ω|)) μ := by
  have hi (r : ℝ) : Integrable (fun ω => Real.exp (r * B ω)) μ := by
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := t) r
    rw [← hB.map_eq] at h
    exact h.comp_aemeasurable hB.aemeasurable
  apply ((hi a).add (hi (-a))).const_mul (Real.exp (a * K)) |>.mono'
    ((hF.abs.const_mul a).exp.aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (a * |F ω|) ≤ Real.exp (a * (K + |B ω|)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω ha)
    _ = Real.exp (a * K) * Real.exp (a * |B ω|) := by
      rw [mul_add, Real.exp_add]
    _ ≤ Real.exp (a * K) * (Real.exp (a * B ω) + Real.exp (-a * B ω)) :=
      mul_le_mul_of_nonneg_left (exp_mul_abs_le_exp_add_exp_neg a (B ω))
        (Real.exp_nonneg _)

theorem integral_exp_abs_le_of_gaussian_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F B : Ω → ℝ} {t : ℝ≥0} {K a : ℝ}
    (hF : Measurable F) (hB : HasLaw B (gaussianReal 0 t) μ)
    (ha : 0 ≤ a) (hbound : ∀ᵐ ω ∂μ, |F ω| ≤ K + |B ω|) :
    (∫ ω, Real.exp (a * |F ω|) ∂μ) ≤
      2 * Real.exp (a * K + (t : ℝ) * a ^ 2 / 2) := by
  have hi (r : ℝ) : Integrable (fun ω => Real.exp (r * B ω)) μ := by
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := t) r
    rw [← hB.map_eq] at h
    exact h.comp_aemeasurable hB.aemeasurable
  have he (r : ℝ) : (∫ ω, Real.exp (r * B ω) ∂μ) =
      Real.exp ((t : ℝ) * r ^ 2 / 2) := by
    have h := hB.integral_comp (f := fun x : ℝ => Real.exp (r * x)) (by fun_prop)
    change (∫ ω, Real.exp (r * B ω) ∂μ) = _ at h
    rw [h]
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := t)) r
  calc
    _ ≤ ∫ ω, Real.exp (a * K) *
        (Real.exp (a * B ω) + Real.exp (-a * B ω)) ∂μ := by
      apply integral_mono_ae (integrable_exp_abs_of_gaussian_bound hF hB ha hbound)
        (((hi a).add (hi (-a))).const_mul _)
      filter_upwards [hbound] with ω hω
      calc
        Real.exp (a * |F ω|) ≤ Real.exp (a * (K + |B ω|)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω ha)
        _ = Real.exp (a * K) * Real.exp (a * |B ω|) := by
          rw [mul_add, Real.exp_add]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (exp_mul_abs_le_exp_add_exp_neg a (B ω)) (Real.exp_nonneg _)
    _ = 2 * Real.exp (a * K + (t : ℝ) * a ^ 2 / 2) := by
      rw [integral_const_mul, integral_add (hi a) (hi (-a)), he, he, neg_sq,
        Real.exp_add]
      ring

private theorem measurable_artanh_c939 : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

open PlantedSymmetry

theorem HasFreeIsingLaw.posterior_field_abs_le_noise
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)| ≤
        (d : ℝ) * beta + (t : ℝ) + |p.2 v| := by
  filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v] with p hp
  have ho : |observation t p v| ≤ (t : ℝ) + |p.2 v| := by
    calc
      _ ≤ |(t : ℝ) * spinSign (p.1 v)| + |p.2 v| := abs_add_le _ _
      _ = _ := by
        cases hs : p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)| ≤
        |Real.artanh (posteriorMagnetization
          (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p) - observation t p v| +
          |observation t p v| := by
            simpa using abs_sub_le (Real.artanh (posteriorMagnetization
              (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)) (observation t p v) 0
    _ ≤ (d : ℝ) * beta + ((t : ℝ) + |p.2 v|) := add_le_add hp.2 ho
    _ = _ := by ring

theorem HasFreeIsingLaw.integrable_exp_abs_posterior_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p => Real.exp (a * |Real.artanh (posteriorMagnetization
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)|))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact integrable_exp_abs_of_gaussian_bound
    (measurable_artanh_c939.comp (measurable_posteriorMagnetization _ _ _))
    (PlantedInformation.noise_hasLaw μ t v) ha
    (hμ.posterior_field_abs_le_noise hbeta t v)

theorem HasFreeIsingLaw.integral_exp_abs_posterior_field_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {a : ℝ} (ha : 0 ≤ a) :
    (∫ p, Real.exp (a * |Real.artanh (posteriorMagnetization
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)|)
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * Real.exp (a * ((d : ℝ) * beta + t) + (t : ℝ) * a ^ 2 / 2) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact integral_exp_abs_le_of_gaussian_bound
    (measurable_artanh_c939.comp (measurable_posteriorMagnetization _ _ _))
    (PlantedInformation.noise_hasLaw μ t v) ha
    (hμ.posterior_field_abs_le_noise hbeta t v)

theorem inverse_spin_variance_eq_cosh_sq {m : ℝ}
    (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - m ^ 2)⁻¹ = (Real.cosh (Real.artanh m)) ^ 2 := by
  have hpos : 0 < 1 - m ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hm.2) (show 0 < 1 + m by linarith [hm.1])]
  rw [Real.cosh_artanh hm, div_pow, one_pow, Real.sq_sqrt hpos.le, one_div]

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h₁ := Real.exp_le_exp.mpr (le_abs_self x)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

theorem inverse_spin_variance_pow_le_exp {m : ℝ}
    (hm : m ∈ Set.Ioo (-1 : ℝ) 1) (p : ℕ) :
    ((1 - m ^ 2)⁻¹) ^ p ≤ Real.exp ((2 * (p : ℝ)) * |Real.artanh m|) := by
  calc
    ((1 - m ^ 2)⁻¹) ^ p = (Real.cosh (Real.artanh m)) ^ (2 * p) := by
      rw [inverse_spin_variance_eq_cosh_sq hm, pow_mul]
    _ ≤ (Real.exp |Real.artanh m|) ^ (2 * p) :=
      pow_le_pow_left₀ (Real.cosh_pos _).le (cosh_le_exp_abs _) _
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

theorem HasFreeIsingLaw.integrable_inverse_posterior_variance_pow
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    Integrable (fun x => ((1 - (posteriorMagnetization
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v x) ^ 2)⁻¹) ^ p)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  apply (hμ.integrable_exp_abs_posterior_field hbeta t v
    (a := 2 * (p : ℝ)) (by positivity)).mono'
  · exact ((measurable_const.sub
      ((measurable_posteriorMagnetization _ _ _).pow_const 2)).inv.pow_const p).aestronglyMeasurable
  · filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v] with x hx
    have hpos : 0 < 1 - (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v x) ^ 2 := by
      have hlow := hx.1.1
      have hhigh := hx.1.2
      nlinarith [mul_pos (sub_pos.mpr hhigh) (show 0 < 1 + posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v x by linarith)]
    rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) _)]
    exact inverse_spin_variance_pow_le_exp hx.1 p

theorem HasFreeIsingLaw.integral_inverse_posterior_variance_pow_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    (∫ x, ((1 - (posteriorMagnetization
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v x) ^ 2)⁻¹) ^ p
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * Real.exp ((2 * (p : ℝ)) * ((d : ℝ) * beta + t) +
        (t : ℝ) * (2 * (p : ℝ)) ^ 2 / 2) := by
  calc
    _ ≤ ∫ x, Real.exp ((2 * (p : ℝ)) * |Real.artanh (posteriorMagnetization
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v x)|)
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
      apply integral_mono_ae
        (hμ.integrable_inverse_posterior_variance_pow hbeta t v p)
        (hμ.integrable_exp_abs_posterior_field hbeta t v (by positivity))
      filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v] with x hx
      exact inverse_spin_variance_pow_le_exp hx.1 p
    _ ≤ _ := hμ.integral_exp_abs_posterior_field_le hbeta t v (by positivity)

theorem HasFreeIsingLaw.identDistrib_brownian_gibbs_posterior
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    IdentDistrib
      (fun x : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        infiniteGibbsSpinMean beta v
          (fun i => (t : ℝ) * spinSign (x.1 i) + B i t (x.2 i)))
      (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v)
      (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hid : IdentDistrib T id (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
    refine ⟨hT.measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [hT.map_eq, Measure.map_id]
  have hG := (measurable_infiniteGibbsSpinMean beta v).comp (measurable_observation (t : ℝ))
  have heq := IdentDistrib.of_ae_eq hG.aemeasurable
    (hμ.infiniteGibbsSpinMean_eq_posterior t v)
  convert (hid.comp hG).trans heq using 1
  funext x
  congr 1

theorem HasFreeIsingLaw.brownian_gibbs_posterior_exponential_moment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d)
    {a : ℝ} (ha : 0 ≤ a) :
    let F := fun x : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      Real.exp (a * |Real.artanh (infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (x.1 i) + B i t (x.2 i)))|)
    Integrable F (μ.prod (Measure.infinitePi ν)) ∧
      (∫ x, F x ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * Real.exp (a * ((d : ℝ) * beta + t) + (t : ℝ) * a ^ 2 / 2) := by
  have hd := (hμ.identDistrib_brownian_gibbs_posterior ν hB hmB t v).comp
    ((measurable_artanh_c939.abs.const_mul a).exp)
  refine ⟨hd.integrable_iff.mpr
    (hμ.integrable_exp_abs_posterior_field hbeta t v ha), ?_⟩
  exact hd.integral_eq.trans_le (hμ.integral_exp_abs_posterior_field_le hbeta t v ha)

theorem HasFreeIsingLaw.brownian_gibbs_posterior_inverse_variance_moment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    let F := fun x : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      ((1 - (infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (x.1 i) + B i t (x.2 i))) ^ 2)⁻¹) ^ p
    Integrable F (μ.prod (Measure.infinitePi ν)) ∧
      (∫ x, F x ∂μ.prod (Measure.infinitePi ν)) ≤
        2 * Real.exp ((2 * (p : ℝ)) * ((d : ℝ) * beta + t) +
          (t : ℝ) * (2 * (p : ℝ)) ^ 2 / 2) := by
  have hd := (hμ.identDistrib_brownian_gibbs_posterior ν hB hmB t v).comp
    (u := fun m : ℝ => ((1 - m ^ 2)⁻¹) ^ p) (by fun_prop)
  refine ⟨hd.integrable_iff.mpr
    (hμ.integrable_inverse_posterior_variance_pow hbeta t v p), ?_⟩
  exact hd.integral_eq.trans_le (hμ.integral_inverse_posterior_variance_pow_le hbeta t v p)

end Problem367

end

end OAI
