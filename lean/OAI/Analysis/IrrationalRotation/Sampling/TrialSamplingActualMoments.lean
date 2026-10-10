import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingIdealMoments
import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingPowers
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingPairMoments

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

private theorem scalar_orientation_mem (m : ℕ) (endpoint : Bool) :
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptKernel m ∨
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptEndpointKernel m := by
  cases endpoint <;> simp

theorem coordinateSample_diagonal_rate {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) (n : ℕ) (hn : N ≤ (n : ℝ)) :
    (∫ p, (coordinateSample m endpoint n p) ^ 2 ∂pairLaw N) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m := by
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun a _ => (a n) ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_diagonal_rate hm hN hn (scalar_orientation_mem m endpoint)

theorem coordinateSample_cross_error {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (hNm : N ≤ (m : ℝ) ^ 2)
    (endpoint : Bool) (n : ℕ) (hn : ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ)) :
    |(∫ p, coordinateSample m endpoint n p * coordinateIdeal m endpoint p ∂pairLaw N) -
      (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤
      (m : ℝ) ^ (-(50 : ℝ)) := by
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun a b => a n * b),
    integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_cross_error hm hN hNm hn (scalar_orientation_mem m endpoint)

theorem coordinateSample_offdiag_error {m : ℕ} (hm : 200 ≤ m)
    {N₀ N : ℝ} {n n' : ℕ} (h : ScalarSampling.SamplingPair m N₀ N n n')
    (endpoint : Bool) :
    |(∫ p, coordinateSample m endpoint n p * coordinateSample m endpoint n' p ∂pairLaw N₀) -
      (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N₀)| ≤
      3509 * (m : ℝ) ^ (-(50 : ℝ)) := by
  rw [integral_coordinate_moment_eq_scalar hm h.N₀_pos endpoint (fun a _ => a n * a n'),
    integral_coordinateIdeal_comp_eq_scalar hm h.N₀_pos endpoint (fun a => a ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_offdiag_error_fifty hm h (scalar_orientation_mem m endpoint)

theorem scale_le_of_half_horizon {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hNm : N ≤ (m : ℝ) ^ 2) (hn : ScalarSampling.samplingHorizon m / 2 ≤ n) :
    N ≤ n := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : 2 * (m : ℝ) ^ 2 ≤ ScalarSampling.samplingHorizon m := by
    calc
      2 * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith [sq_nonneg (m : ℝ)]
      _ = (m : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ ScalarSampling.samplingHorizon m :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith

theorem expectation_squaredError_le_actual_bound
    {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    (hNm : N ≤ (m : ℝ) ^ 2) (samples : Finset ℕ) (hs : samples.Nonempty)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
    (hrange : ∀ n ∈ samples, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ))
    (hpair : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
      ScalarSampling.SamplingPair m N N n n') (endpoint : Bool) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) := by
  apply expectation_squaredError_le_meanSquareBound m (by omega) hN samples hs endpoint
    3509 (by norm_num) hcard
  · exact integral_coordinateIdeal_eq_kernelMass hm hN endpoint
  · exact integral_coordinateIdeal_sq_le_momentBase hm hN endpoint
  · intro n hn
    exact coordinateSample_diagonal_rate hm hN endpoint n
      (scale_le_of_half_horizon hm hNm (hrange n hn))
  · intro n hn n' hn' hne
    exact coordinateSample_offdiag_error hm (hpair n hn n' hn' hne) endpoint
  · intro n hn
    apply (coordinateSample_cross_error hm hN hNm endpoint n (hrange n hn)).trans
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) (-(50 : ℝ))]

theorem tendsto_actual_squaredError_zero
    (N : ℕ → ℝ) (samples : ℕ → Finset ℕ)
    (hN : ∀ᶠ m in atTop, 0 < N m ∧ N m ≤ (m : ℝ) ^ 2)
    (hs : ∀ᶠ m in atTop, (samples m).Nonempty)
    (hcard : ∀ᶠ (m : ℕ) in atTop,
      (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((samples m).card : ℝ))
    (hrange : ∀ᶠ m in atTop, ∀ n ∈ samples m,
      ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ))
    (hpair : ∀ᶠ m in atTop, ∀ n ∈ samples m, ∀ n' ∈ samples m, n ≠ n' →
      ScalarSampling.SamplingPair m (N m) (N m) n n') (endpoint : Bool) :
    Tendsto (fun m => ∫⁻ phase, squaredError m (samples m) endpoint phase
      ∂phaseLaw m (N m)) atTop (𝓝 0) := by
  apply SamplingAsymptotics.tendsto_zero_of_meanSquareBound 3509 (by norm_num)
  filter_upwards [eventually_ge_atTop (200 : ℕ), hN, hs, hcard, hrange, hpair]
    with m hm hmN hms hmc hmr hmp
  exact expectation_squaredError_le_actual_bound hm hmN.1 hmN.2 (samples m) hms
    hmc hmr hmp endpoint

end Invariant233.TrialSampling

end

end OAI
