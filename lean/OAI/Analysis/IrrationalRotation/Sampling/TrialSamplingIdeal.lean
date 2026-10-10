import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingScalar

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.TrialSampling

theorem integral_coordinateIdeal {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    (endpoint : Bool) :
    (∫ p, coordinateIdeal m endpoint p ∂pairLaw N) = SamplingAsymptotics.kernelMass m := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  have he := integral_coordinate_moment_eq_scalar hm hN endpoint (fun _ a => a)
  rw [he]
  rw [integral_fun_snd (fun s : ℝ => ∫ v in (0 : ℝ)..1,
    if endpoint then ScalarSampling.manuscriptEndpointKernel m s v
    else ScalarSampling.manuscriptKernel m s v)]
  simp only [probReal_univ, one_smul]
  rw [restrict_Ico_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hmass : (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
      if endpoint then ScalarSampling.manuscriptEndpointKernel m s v
      else ScalarSampling.manuscriptKernel m s v) = 1 - 2 / (m : ℝ)^2 := by
    cases endpoint
    · simpa using (ScalarSampling.manuscriptKernel_estimates hm).mass
    · simpa using (ScalarSampling.manuscriptEndpointKernel_estimates hm).mass
  rw [hmass]
  simp [SamplingAsymptotics.kernelMass, Real.rpow_neg (Nat.cast_nonneg m),
    Real.rpow_ofNat, div_eq_mul_inv]

theorem integral_coordinateIdeal_sq_le_raw {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, (coordinateIdeal m endpoint p)^2 ∂pairLaw N) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  have he := integral_coordinate_moment_eq_scalar hm hN endpoint (fun _ a => a^2)
  rw [he]
  rw [integral_fun_snd (fun s : ℝ => (∫ v in (0 : ℝ)..1,
    if endpoint then ScalarSampling.manuscriptEndpointKernel m s v
    else ScalarSampling.manuscriptKernel m s v)^2)]
  simp only [probReal_univ, one_smul]
  rw [restrict_Ico_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  cases endpoint
  · simpa using (ScalarSampling.manuscriptKernel_estimates hm).average_square_upper
  · simpa using (ScalarSampling.manuscriptEndpointKernel_estimates hm).average_square_upper

theorem integral_coordinateIdeal_sq_le {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, (coordinateIdeal m endpoint p)^2 ∂pairLaw N) ≤
      SamplingAsymptotics.momentBase m := by
  have hh := ScalarSampling.manuscript_width_le_half hm
  let h : ℝ := (m : ℝ)^(-(3 / 5 : ℝ))
  have hh' : h ≤ 1 / 2 := hh
  have hd : 0 < (1 - h)^2 := sq_pos_of_pos (by linarith)
  have hdquarter : (1 / 4 : ℝ) ≤ (1 - h)^2 := by nlinarith
  have hquot : h^2 / (1 - h)^2 ≤ 4 * h^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdquarter (sq_nonneg h)]
  have hp : h^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    dsimp [h]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
  calc
    _ ≤ 1 + h^2 / (1 - h)^2 := integral_coordinateIdeal_sq_le_raw hm hN endpoint
    _ ≤ 1 + 4 * h^2 := by linarith
    _ = SamplingAsymptotics.momentBase m := by rw [hp]; rfl

end Invariant233.TrialSampling

end

end OAI
