import OAI.Probability.FreeIsing.Brownian.DriftMoments
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def gaussianPosteriorField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  fun p => Real.artanh
    (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)

theorem measurable_gaussianPosteriorField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) :
    Measurable (gaussianPosteriorField μ t v) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  exact ha.comp (measurable_posteriorMagnetization _ _ _)

theorem gaussianPlanted_noise_hasLaw {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (v : TreeVertex d) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => p.2 v)
      (gaussianReal 0 t) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have h := (measurePreserving_eval_infinitePi
    (fun _ : TreeVertex d => gaussianReal 0 t) v).comp
      (measurePreserving_snd (μ := μ) (ν := gaussianNoiseLaw (TreeVertex d) t))
  exact ⟨h.measurable.aemeasurable, h.map_eq⟩

theorem HasFreeIsingLaw.gaussian_posterior_field_noise_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |gaussianPosteriorField μ t v p - p.2 v| ≤ (d : ℝ) * beta + t := by
  filter_upwards [hμ.gaussian_posterior_field_bound hbeta t v] with p hp
  have hs : |(t : ℝ) * spinSign (p.1 v)| = t := by
    cases he : p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    |gaussianPosteriorField μ t v p - p.2 v| =
        |(gaussianPosteriorField μ t v p - observation t p v) +
          (t : ℝ) * spinSign (p.1 v)| := by
      congr 1
      simp only [observation]
      ring
    _ ≤ |gaussianPosteriorField μ t v p - observation t p v| +
        |(t : ℝ) * spinSign (p.1 v)| := abs_add_le _ _
    _ ≤ (d : ℝ) * beta + t := by rw [hs]; exact add_le_add hp.2 le_rfl

theorem HasFreeIsingLaw.integrable_gaussianPosteriorField_abs_pow
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    Integrable (fun q => |gaussianPosteriorField μ t v q| ^ p)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact integrable_abs_pow_of_bounded_perturbation p (by positivity)
    (measurable_gaussianPosteriorField μ t v).aemeasurable
    (integrable_abs_pow_of_gaussianLaw (gaussianPlanted_noise_hasLaw μ t v) p)
    (hμ.gaussian_posterior_field_noise_bound hbeta t v)

theorem HasFreeIsingLaw.memLp_gaussianPosteriorField_two
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (gaussianPosteriorField μ t v) 2
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_gaussianPosteriorField μ t v).aestronglyMeasurable).mpr
  simpa only [sq_abs] using hμ.integrable_gaussianPosteriorField_abs_pow hbeta t v 2

theorem HasFreeIsingLaw.gaussianPosteriorField_abs_moment_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    (∫ q, |gaussianPosteriorField μ t v q| ^ p
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 ^ (p - 1) * (Real.sqrt (t : ℝ) ^ p *
        (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1) + ((d : ℝ) * beta + t) ^ p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let K : ℝ := (d : ℝ) * beta + t
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnoise := integrable_abs_pow_of_gaussianLaw (gaussianPlanted_noise_hasLaw μ t v) p
  have hdom := (hnoise.add (integrable_const (K ^ p))).const_mul (2 ^ (p - 1) : ℝ)
  have hle : ∀ᵐ q ∂P, |gaussianPosteriorField μ t v q| ^ p ≤
      2 ^ (p - 1) * (|q.2 v| ^ p + K ^ p) := by
    filter_upwards [hμ.gaussian_posterior_field_noise_bound hbeta t v] with q hq
    have hb : |gaussianPosteriorField μ t v q| ≤ |q.2 v| + K := by
      have hh := abs_add_le (gaussianPosteriorField μ t v q - q.2 v) (q.2 v)
      simpa only [sub_add_cancel] using hh.trans (by dsimp [K]; linarith)
    exact (pow_le_pow_left₀ (abs_nonneg _) hb p).trans (add_pow_le (abs_nonneg _) hK p)
  have hmoment := (gaussianPlanted_noise_hasLaw μ t v).integral_comp
    (f := fun x : ℝ => |x| ^ p) (by fun_prop)
  change (∫ q, |q.2 v| ^ p ∂P) = _ at hmoment
  calc
    _ ≤ ∫ q, 2 ^ (p - 1) * (|q.2 v| ^ p + K ^ p) ∂P :=
      integral_mono_ae (hμ.integrable_gaussianPosteriorField_abs_pow hbeta t v p) hdom hle
    _ = 2 ^ (p - 1) * ((∫ q, |q.2 v| ^ p ∂P) + K ^ p) := by
      rw [integral_const_mul, integral_add hnoise (integrable_const _)]; simp [P]
    _ = _ := by rw [hmoment, integral_gaussianReal_abs_pow]

theorem HasFreeIsingLaw.gaussianPosteriorField_second_moment_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ q, (gaussianPosteriorField μ t v q) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * ((t : ℝ) + ((d : ℝ) * beta + t) ^ 2) := by
  have hg : (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 1) = 1 := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := fun x : ℝ => x) (by fun_prop) (by simp)] at hv
    simpa only [sq_abs, NNReal.coe_one] using hv
  have h := hμ.gaussianPosteriorField_abs_moment_le hbeta t v 2
  rw [hg] at h
  simpa only [sq_abs, Real.sq_sqrt t.coe_nonneg, mul_one,
    Nat.reduceSub, pow_one] using h

theorem HasFreeIsingLaw.gaussianPosteriorField_second_moment_le_horizon
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (v : TreeVertex d) :
    (∫ q, (gaussianPosteriorField μ t v q) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * ((T : ℝ) + ((d : ℝ) * beta + T) ^ 2) := by
  apply (hμ.gaussianPosteriorField_second_moment_le hbeta t v).trans
  have ht' : (t : ℝ) ≤ T := ht
  gcongr

end Problem367

end

end OAI
