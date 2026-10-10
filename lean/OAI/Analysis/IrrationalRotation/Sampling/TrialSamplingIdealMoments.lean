import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingScalar
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelMomentNumerics

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.TrialSampling

private theorem scalar_orientation_estimates {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) : ScalarSampling.KernelEstimates m (fun z v =>
      if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) := by
  cases endpoint
  · exact ScalarSampling.manuscriptKernel_estimates hm
  · exact ScalarSampling.manuscriptEndpointKernel_estimates hm

theorem integral_coordinateIdeal_comp_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) (f : ℝ → ℝ) :
    (∫ p, f (coordinateIdeal m endpoint p) ∂pairLaw N) =
      ∫ z in (0 : ℝ)..1, f (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
        else ScalarSampling.manuscriptKernel m z v) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun _ a => f a)]
  rw [integral_fun_snd (fun z : ℝ => f (∫ v in (0 : ℝ)..1,
    if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
    else ScalarSampling.manuscriptKernel m z v))]
  simp only [probReal_univ, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Ico_eq_integral_Ioc

theorem integral_coordinateIdeal_eq_kernelMass {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, coordinateIdeal m endpoint p ∂pairLaw N) =
      SamplingAsymptotics.kernelMass m := by
  rw [integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a)]
  rw [(scalar_orientation_estimates hm endpoint).mass]
  simp only [SamplingAsymptotics.kernelMass, Real.rpow_neg (Nat.cast_nonneg m),
    Real.rpow_two, div_eq_mul_inv]

theorem integral_coordinateIdeal_sq_le_scalarBound {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N) ≤
      1 + ((m : ℝ) ^ (-(3 / 5 : ℝ))) ^ 2 /
        (1 - (m : ℝ) ^ (-(3 / 5 : ℝ))) ^ 2 := by
  rw [integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a ^ 2)]
  exact (scalar_orientation_estimates hm endpoint).average_square_upper

theorem integral_coordinateIdeal_sq_le_momentBase {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N) ≤
      SamplingAsymptotics.momentBase m := by
  rw [integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a ^ 2)]
  exact ScalarSampling.KernelEstimates.average_square_source_bound hm
    (scalar_orientation_estimates hm endpoint)

end Invariant233.TrialSampling

end

end OAI
