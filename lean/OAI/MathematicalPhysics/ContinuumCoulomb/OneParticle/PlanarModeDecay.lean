import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeProperties

namespace OAI

/-! An explicit exponential tail of the actual positive planar mode. Splitting
the Gaussian exponent avoids any assumed asymptotics for a special function. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_double_time (t : ℝ) (b : PlanarPosition) :
    planarHeatKernel t b =
      2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b := by
  unfold planarHeatKernel
  have h1 : -‖b‖ ^ 2 / (4 * t) = -‖b‖ ^ 2 / (8 * t) + -‖b‖ ^ 2 / (8 * t) := by ring
  have h2 : -‖b‖ ^ 2 / (4 * (2 * t)) = -‖b‖ ^ 2 / (8 * t) := by ring
  rw [h1, h2, Real.exp_add]
  ring

theorem planarHeatForcing_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖)
    (b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) * planarHeatKernel (2 * t) b := by
  by_cases hf : planarForcing (r - b) = 0
  · rw [hf, mul_zero]
    exact mul_nonneg (by positivity) (planarHeatKernel_positive (by positivity) b).le
  · have hs : ‖r - b‖ < 1 := lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h))
    have hn : ‖r‖ - 1 ≤ ‖b‖ := by
      have htriangle := norm_add_le (r - b) b
      rw [sub_add_cancel] at htriangle
      linarith
    have hsq : (‖r‖ - 1) ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have he : Real.exp (-‖b‖ ^ 2 / (8 * t)) ≤
        Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    calc
      _ ≤ planarHeatKernel t b :=
        mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)
      _ = 2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b :=
        planarHeatKernel_double_time t b
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
        (planarHeatKernel_positive (by positivity) b).le

theorem planarHeatAverage_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarHeatAverage t r ≤ 2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
  have hi := (planarHeatKernel_integrable (by positivity : 0 < 2 * t)).const_mul
    (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tail ht hr)
  simpa only [integral_const_mul, planarHeatKernel_integral (by positivity : 0 < 2 * t),
    mul_one, planarHeatAverage] using h

theorem planar_heat_tail_exponent {t d : ℝ} (ht : 0 < t) :
    d / 2 ≤ t / 2 + d ^ 2 / (8 * t) := by
  have he : t / 2 + d ^ 2 / (8 * t) - d / 2 = (2 * t - d) ^ 2 / (8 * t) := by
    field_simp
    ring
  have hp : 0 ≤ (2 * t - d) ^ 2 / (8 * t) := by positivity
  linarith

theorem planarHeatResolvent_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    Real.exp (-t) * planarHeatAverage t r ≤
      (2 * Real.exp (-(‖r‖ - 1) / 2)) * Real.exp (-(1 / 2 : ℝ) * t) := by
  have he : -t + (-((‖r‖ - 1) ^ 2) / (8 * t)) ≤ -(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t := by
    have hA : (‖r‖ - 1) / 2 ≤ t / 2 + (‖r‖ - 1) ^ 2 / (8 * t) :=
      planar_heat_tail_exponent ht
    rw [neg_div]
    linarith
  calc
    _ ≤ Real.exp (-t) * (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) :=
      mul_le_mul_of_nonneg_left (planarHeatAverage_tail ht hr) (Real.exp_pos _).le
    _ = 2 * Real.exp (-t + (-((‖r‖ - 1) ^ 2) / (8 * t))) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem planarResolventMode_exponential_tail {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ 4 * Real.exp (-(‖r‖ - 1) / 2) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (2 * Real.exp (-(‖r‖ - 1) / 2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatResolvent_tail ht hr)
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * t)) = 2 := by
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
    norm_num
  rw [integral_const_mul, he] at h
  nlinarith

end ContinuumCoulomb

end

end OAI
