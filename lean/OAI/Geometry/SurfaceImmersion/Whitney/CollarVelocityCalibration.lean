import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityMean

namespace OAI

/-! Calibrate the explicit collar arc to the required tangential mean. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

def amplitude (R v a : ℝ) : ℝ := Real.sqrt 2 * a / (R + v)

lemma amplitude_sq (R v a : ℝ) : amplitude R v a ^ 2 = 2 * a ^ 2 / (R + v) ^ 2 := by
  unfold amplitude
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The mean has exactly the prescribed tangential component. -/
theorem calibrated_mean {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    circleMean (fun t => density (amplitude R v a) t * arcX (amplitude R v a) t) = v / R := by
  rw [mean_density_arcX, amplitude_sq]
  have hp : R + v ≠ 0 := ne_of_gt (add_pos hR hv)
  have hd : (R + v) ^ 2 + a ^ 2 ≠ 0 := by positivity
  have heq : (1 - 2 * a ^ 2 / (R + v) ^ 2 / 2) /
      (1 + 2 * a ^ 2 / (R + v) ^ 2 / 2) =
      ((R + v) ^ 2 - a ^ 2) / ((R + v) ^ 2 + a ^ 2) := by
    field_simp
  rw [heq]
  have hn : (R + v) ^ 2 - a ^ 2 = 2 * v * (R + v) := by nlinarith
  have hd' : (R + v) ^ 2 + a ^ 2 = 2 * R * (R + v) := by nlinarith
  rw [hn, hd']
  field_simp

lemma circleMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    circleMean (fun t => c * f t) = c * circleMean f := by
  unfold circleMean
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Both weighted velocity means are exact before the positive reparametrization. -/
theorem calibrated_velocity_means {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    circleMean (fun t => density (amplitude R v a) t * (R * arcX (amplitude R v a) t)) = v ∧
    circleMean (fun t => density (amplitude R v a) t * (R * arcY (amplitude R v a) t)) = 0 := by
  constructor
  · simp_rw [mul_left_comm _ R]
    rw [circleMean_const_mul, calibrated_mean hR hv hquad]
    field_simp
  · simp_rw [mul_left_comm _ R]
    rw [circleMean_const_mul, mean_density_arcY, mul_zero]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
