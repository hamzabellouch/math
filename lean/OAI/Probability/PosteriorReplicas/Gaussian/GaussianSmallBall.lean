import OAI.Probability.PosteriorReplicas.Gaussian.GaussianPolar

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_density_ball_lower {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-R^2/2)) * volume (closedBall (0 : E) R) ≤ 1 := by
  calc
    _ = ∫⁻ x in closedBall (0 : E) R,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-R^2/2)) ∂volume := by simp
    _ ≤ ∫⁻ x in closedBall (0 : E) R,
      gaussianRadialDensity (Module.finrank ℝ E) ‖x‖ ∂volume := by
      apply setLIntegral_mono' isClosed_closedBall.measurableSet
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
      nlinarith [norm_nonneg x, sq_nonneg (R-‖x‖)]
    _ = stdGaussian E (closedBall (0 : E) R) := by
      rw [stdGaussian_density, withDensity_apply _ isClosed_closedBall.measurableSet]
    _ ≤ 1 := prob_le_one

lemma gaussian_density_ball_upper (a : E) (r : ℝ) :
    stdGaussian E (closedBall a r) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
        volume (closedBall a r) := by
  rw [stdGaussian_density, withDensity_apply _ isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ _ in closedBall a r,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) ∂volume := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (-‖x‖^2/2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg ‖x‖]
      exact mul_le_of_le_one_right (by positivity) he
    _ = _ := by simp

lemma gaussian_closedBall_ratio (a : E) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    stdGaussian E (closedBall a r) ≤
      ENNReal.ofReal (Real.exp (R^2/2) * (r/R)^(Module.finrank ℝ E)) := by
  let c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have hexp : ENNReal.ofReal (Real.exp (R^2/2)) *
      ENNReal.ofReal (Real.exp (-R^2/2)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have he : R^2/2 + -R^2/2 = 0 := by ring
    rw [he, Real.exp_zero, ENNReal.ofReal_one]
  have h := mul_le_mul_right (gaussian_density_ball_lower (E := E) hR.le)
    (ENNReal.ofReal (Real.exp (R^2/2)))
  have hvol : ENNReal.ofReal c * volume (closedBall (0 : E) R) ≤
      ENNReal.ofReal (Real.exp (R^2/2)) := by
    dsimp only [c] at *
    rw [ENNReal.ofReal_mul (by positivity), mul_one] at h
    calc
      _ = (ENNReal.ofReal (Real.exp (R^2/2)) * ENNReal.ofReal (Real.exp (-R^2/2))) *
        (ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
          volume (closedBall (0 : E) R)) := by rw [hexp, one_mul]
      _ ≤ _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hscale : volume (closedBall a r) =
      ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) * volume (closedBall (0 : E) R) := by
    have hh := Measure.addHaar_closedBall_mul (volume : Measure E) a (div_nonneg hr hR.le) hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at hh
    exact hh
  calc
    _ ≤ ENNReal.ofReal c * volume (closedBall a r) := gaussian_density_ball_upper a r
    _ = ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) *
        (ENNReal.ofReal c * volume (closedBall (0 : E) R)) := by rw [hscale]; ac_rfl
    _ ≤ ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) *
        ENNReal.ofReal (Real.exp (R^2/2)) := mul_le_mul_right hvol _
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma gaussian_normalized_inverse_moment (a : E) (k : ℕ) (hk : k+1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal (((‖x-a‖ / R)⁻¹)^k) ∂stdGaussian E) ≤
      1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1) := by
  have h := PosteriorRegression.inverse_moment_of_tube_bound (stdGaussian E)
    (fun x : E => ‖x-a‖/R) k (by fun_prop) (fun x => by positivity)
    (ENNReal.ofReal (Real.exp (R^2/2))) ?_
  · simpa only [measure_univ] using h
  intro r hr hr1
  have hs : {x : E | ‖x-a‖ / R ≤ r} = closedBall a (r*R) := by
    ext x
    simp only [mem_ofPred_eq, mem_closedBall, dist_eq_norm, div_le_iff₀ hR]
  rw [hs]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (R^2/2) * ((r*R)/R)^(Module.finrank ℝ E)) :=
      gaussian_closedBall_ratio a hR (mul_nonneg hr.le hR.le)
    _ ≤ _ := by
      rw [mul_div_cancel_right₀ _ hR.ne', ENNReal.ofReal_mul (by positivity)]
      apply mul_le_mul_right
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)

lemma gaussian_inverse_norm_moment (a : E) (k : ℕ) (hk : k+1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal (‖x-a‖⁻¹^k) ∂stdGaussian E) ≤
      ENNReal.ofReal (R⁻¹^k) * (1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1)) := by
  have he : (∫⁻ x : E, ENNReal.ofReal (‖x-a‖⁻¹^k) ∂stdGaussian E) =
      ENNReal.ofReal (R⁻¹^k) * ∫⁻ x : E, ENNReal.ofReal (((‖x-a‖/R)⁻¹)^k) ∂stdGaussian E := by
    rw [← lintegral_const_mul _ (show Measurable (fun x : E =>
      ENNReal.ofReal (((‖x-a‖/R)⁻¹)^k)) by fun_prop)]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  rw [he]
  exact mul_le_mul_right (gaussian_normalized_inverse_moment a k hk hR) _

end PosteriorReplicas
end

end OAI
