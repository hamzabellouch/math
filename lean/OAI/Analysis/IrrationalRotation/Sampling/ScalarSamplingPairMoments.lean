import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingFull
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingMomentConsequences
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingNumerics
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelMomentRates
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

def scalarUnitLaw : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

def scalarPairLaw (N : ℝ) : Measure (ℝ × ℝ) :=
  (UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw

instance scalarUnitLaw_probability : IsProbabilityMeasure scalarUnitLaw := by
  constructor
  simp [scalarUnitLaw]

lemma scalarPairLaw_probability {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (scalarPairLaw N) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  dsimp [scalarPairLaw]
  infer_instance

lemma integral_scalarUnitLaw (f : ℝ → ℝ) :
    (∫ s, f s ∂scalarUnitLaw) = ∫ s in (0 : ℝ)..1, f s := by
  simp only [scalarUnitLaw, restrict_Ico_eq_restrict_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma measurable_kernel_mean {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (fun s => ∫ v in (0 : ℝ)..1, u s v) := by
  simpa only [Function.uncurry, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    ((manuscript_kernel_measurable hu).stronglyMeasurable.integral_prod_right').measurable

lemma integrable_kernel_mean {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun s => ∫ v in (0 : ℝ)..1, u s v) scalarUnitLaw := by
  apply Integrable.of_bound (measurable_kernel_mean hu).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro s
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds s
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h2

lemma integrable_kernel_mean_square {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun s => (∫ v in (0 : ℝ)..1, u s v)^2) scalarUnitLaw := by
  apply Integrable.of_bound ((measurable_kernel_mean hu).pow_const 2).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro s
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

lemma integrable_sampled_product {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (n n' : ℝ) :
    Integrable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1)) *
      u p.2 (Int.fract (n' * p.1))) (scalarPairLaw N) := by
  let := scalarPairLaw_probability hN
  have hmeas (k : ℝ) : Measurable (fun p : ℝ × ℝ => u p.2 (Int.fract (k * p.1))) :=
    (manuscript_kernel_measurable hu).comp
      (measurable_snd.prodMk (measurable_fract.comp (measurable_const.mul measurable_fst)))
  apply Integrable.of_bound ((hmeas n).mul (hmeas n')).aestronglyMeasurable
    (((m : ℝ)^(13 / 5 : ℝ))^2)
  apply Filter.Eventually.of_forall
  intro p
  change |u p.2 (Int.fract (n * p.1)) * u p.2 (Int.fract (n' * p.1))| ≤ _
  rw [abs_mul, pow_two]
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.2 _) (manuscript_kernel_abs_le hm hu p.2 _)
    (abs_nonneg _) (by positivity)

lemma integrable_sampled_cross {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (n : ℝ) :
    Integrable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1)) *
      (∫ v in (0 : ℝ)..1, u p.2 v)) (scalarPairLaw N) := by
  let := scalarPairLaw_probability hN
  have hmeas : Measurable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1))) :=
    (manuscript_kernel_measurable hu).comp
      (measurable_snd.prodMk (measurable_fract.comp (measurable_const.mul measurable_fst)))
  apply Integrable.of_bound
    (hmeas.mul ((measurable_kernel_mean hu).comp measurable_snd)).aestronglyMeasurable
    ((m : ℝ)^(13 / 5 : ℝ) * 2)
  apply Filter.Eventually.of_forall
  intro p
  change |u p.2 (Int.fract (n * p.1)) * (∫ v in (0 : ℝ)..1, u p.2 v)| ≤ _
  rw [abs_mul]
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds p.2
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.2 _)
    (by simpa only [abs_of_nonneg h0] using h2) (abs_nonneg _) (by positivity)

lemma scalarPair_error_transfer {N ε : ℝ} (hN : 0 < N)
    {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    (hf : Integrable f (scalarPairLaw N)) (hg : Integrable g scalarUnitLaw)
    (h : ∀ s, |(∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s| ≤ ε) :
    |(∫ p, f p ∂scalarPairLaw N) - ∫ s, g s ∂scalarUnitLaw| ≤ ε := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  change Integrable f ((UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw) at hf
  rw [scalarPairLaw, integral_prod_symm f hf, ← integral_sub hf.integral_prod_right hg]
  have hh := norm_integral_le_of_norm_le_const
    (μ := scalarUnitLaw) (f := fun s => (∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s)
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using h s)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

theorem scalarPair_cross_error {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hNm : N ≤ (m : ℝ)^2) (hn : samplingHorizon m / 2 ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract (n * p.1)) * (∫ v in (0 : ℝ)..1, u p.2 v)
        ∂scalarPairLaw N) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      (m : ℝ)^(-(50 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 0 < n := (half_pos (Real.rpow_pos_of_pos hm0 _)).trans_le hn
  rw [← integral_scalarUnitLaw]
  apply scalarPair_error_transfer hN (integrable_sampled_cross hm hN hu n)
    (integrable_kernel_mean_square hm hu)
  intro s
  exact (one_power_kernel_cross_error hm hN hn0 hu s).trans (cross_error_scale hm hN hNm hn)

theorem scalarPair_offdiag_error {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n')
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract ((n : ℝ) * p.1)) * u p.2 (Int.fract ((n' : ℝ) * p.1))
        ∂scalarPairLaw N₀) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      3509 * (m : ℝ)^(-(60 : ℝ)) := by
  rw [← integral_scalarUnitLaw]
  apply scalarPair_error_transfer h.N₀_pos (integrable_sampled_product hm h.N₀_pos hu n n')
    (integrable_kernel_mean_square hm hu)
  intro s
  convert two_power_kernel_error hm (by norm_num : (0 : ℝ) ≤ 29) (bv_estimate hm h) hu s using 1
  norm_num

lemma integrable_haar_kernel_square {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun p : ℝ × ℝ => (u p.1 p.2)^2) (scalarUnitLaw.prod scalarUnitLaw) := by
  apply Integrable.of_bound ((manuscript_kernel_measurable hu).pow_const 2).aestronglyMeasurable
    (((m : ℝ)^(13 / 5 : ℝ))^2)
  apply Filter.Eventually.of_forall
  intro p
  change |(u p.1 p.2)^2| ≤ _
  rw [abs_pow, pow_two, pow_two]
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.1 p.2)
    (manuscript_kernel_abs_le hm hu p.1 p.2) (abs_nonneg _) (by positivity)

theorem scalarPair_diagonal_le {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hn : N ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    (∫ p, (u p.2 (Int.fract (n * p.1)))^2 ∂scalarPairLaw N) ≤
      2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (u s v)^2) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  have hf : Integrable (fun p : ℝ × ℝ => (u p.2 (Int.fract (n * p.1)))^2)
      ((UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw) := by
    simpa only [pow_two, scalarPairLaw] using integrable_sampled_product hm hN hu n n
  have hg : Integrable (fun s => ∫ v in (0 : ℝ)..1, (u s v)^2) scalarUnitLaw := by
    simpa only [integral_scalarUnitLaw] using (integrable_haar_kernel_square hm hu).integral_prod_left
  rw [scalarPairLaw, integral_prod_symm _ hf]
  calc
    _ ≤ ∫ s, 2 * (∫ v in (0 : ℝ)..1, (u s v)^2) ∂scalarUnitLaw :=
      integral_mono hf.integral_prod_right (hg.const_mul 2)
        (fun s => one_power_kernel_square_le hm hN hn hu s)
    _ = _ := by rw [integral_const_mul, integral_scalarUnitLaw]

theorem scalarPair_offdiag_error_fifty {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n')
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract ((n : ℝ) * p.1)) * u p.2 (Int.fract ((n' : ℝ) * p.1))
        ∂scalarPairLaw N₀) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      3509 * (m : ℝ)^(-(50 : ℝ)) := by
  apply (scalarPair_offdiag_error hm h hu).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)

theorem scalarPair_diagonal_rate {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hn : N ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    (∫ p, (u p.2 (Int.fract (n * p.1)))^2 ∂scalarPairLaw N) ≤
       8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m :=
  (scalarPair_diagonal_le hm hN hn hu).trans
    ((both_kernel_estimates hm hu).twice_square_mass_rate hm)

end Invariant233.ScalarSampling

end

end OAI
