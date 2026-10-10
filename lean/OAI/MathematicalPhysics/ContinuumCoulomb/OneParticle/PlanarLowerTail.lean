import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSharpDecay

namespace OAI

/-! A matching lower exponential tail for the actual planar mode. Only the
positive forcing mass and the heat-time interval `[|r|/2,|r|/2+1]` are used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatAverage_other_integrable {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    Integrable (fun a => planarHeatKernel t (r - a) * planarForcing a) := by
  have h := (planarHeatAverage_integrand_integrable ht r).comp_sub_left r
  convert h using 1
  funext a
  rw [show r - (r - a) = a by abel]

theorem planarHeatAverage_other (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ a, planarHeatKernel t (r - a) * planarForcing a := by
  have h := integral_sub_left_eq_self
    (fun b => planarHeatKernel t b * planarForcing (r - b)) volume r
  unfold planarHeatAverage
  convert h.symm using 1
  congr 1
  funext a
  rw [show r - (r - a) = a by abel]

theorem planar_heat_lower_exponent {R t d : ℝ} (hR : 1 ≤ R)
    (ht₀ : R / 2 ≤ t) (ht₁ : t ≤ R / 2 + 1) (hd₀ : 0 ≤ d) (hd₁ : d ≤ R + 1) :
    t + d ^ 2 / (4 * t) ≤ R + 2 := by
  have ht : 0 < t := by linarith
  have hs : d ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hp : 0 ≤ (t - R / 2) * (R / 2 + 2 - t) :=
    mul_nonneg (by linarith) (by linarith)
  have hd : d ^ 2 / (4 * t) ≤ R + 2 - t :=
    (div_le_iff₀ (by positivity : 0 < 4 * t)).2 (by nlinarith)
  linarith

theorem planarHeatKernel_weighted_lower {r a : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ha : ‖a‖ ≤ 1)
    (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1) :
    Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2)) ≤
      Real.exp (-t) * planarHeatKernel t (r - a) := by
  have ht : 0 < t := by linarith
  have hnorm : ‖r - a‖ ≤ ‖r‖ + 1 := (norm_sub_le r a).trans (by linarith)
  have he : Real.exp (-(‖r‖ + 2)) ≤ Real.exp (-t + -‖r - a‖ ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.mpr
    have h := planar_heat_lower_exponent hr ht₀ ht₁ (norm_nonneg _) hnorm
    rw [neg_div]
    linarith
  have hden : 4 * Real.pi * t ≤ 2 * Real.pi * (‖r‖ + 2) := by
    nlinarith [Real.pi_pos]
  have hinv : (2 * Real.pi * (‖r‖ + 2))⁻¹ ≤ (4 * Real.pi * t)⁻¹ :=
    inv_anti₀ (by positivity) hden
  unfold planarHeatKernel
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-t + -‖r - a‖ ^ 2 / (4 * t)) * (4 * Real.pi * t)⁻¹ :=
      mul_le_mul he hinv (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

theorem planarHeatForcing_weighted_lower {r : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1)
    (a : PlanarPosition) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * planarForcing a ≤
      (Real.exp (-t) * planarHeatKernel t (r - a)) * planarForcing a := by
  by_cases hf : planarForcing a = 0
  · simp only [hf, mul_zero, le_refl]
  have ha : ‖a‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  exact mul_le_mul_of_nonneg_right (planarHeatKernel_weighted_lower hr ha ht₀ ht₁)
    (planarForcing_nonnegative a)

theorem planarHeatAverage_weighted_lower {r : PlanarPosition} {t : ℝ}
    (hr : 1 ≤ ‖r‖) (ht₀ : ‖r‖ / 2 ≤ t) (ht₁ : t ≤ ‖r‖ / 2 + 1) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * (∫ a, planarForcing a) ≤
      Real.exp (-t) * planarHeatAverage t r := by
  have ht : 0 < t := by linarith
  have h := integral_mono
    (planarForcing_integrable.const_mul
      (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))))
    ((planarHeatAverage_other_integrable ht r).const_mul (Real.exp (-t)))
    (fun a => by simpa only [mul_assoc] using planarHeatForcing_weighted_lower hr ht₀ ht₁ a)
  simpa only [integral_const_mul, ← planarHeatAverage_other] using h

theorem planarResolventMode_sharp_lower_raw {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    (Real.exp (-(‖r‖ + 2)) / (2 * Real.pi * (‖r‖ + 2))) * (∫ a, planarForcing a) ≤
      planarResolventMode r := by
  have hsub : Set.Icc (‖r‖ / 2) (‖r‖ / 2 + 1) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    change 0 < t
    linarith [ht.1]
  have hi := (planarResolventMode_heat_integrable r).mono_set hsub
  have hl := setIntegral_ge_of_const_le_real measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne
    (fun t ht => planarHeatAverage_weighted_lower hr ht.1 ht.2) hi
  have hm := setIntegral_mono_set (planarResolventMode_heat_integrable r)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_pos _).le (planarHeatAverage_positive ht r).le)
    (Filter.Eventually.of_forall hsub)
  rw [Real.volume_real_Icc_of_le (by linarith), show ‖r‖ / 2 + 1 - ‖r‖ / 2 = 1 by ring,
    mul_one] at hl
  rw [planarResolventMode_heat_representation]
  exact hl.trans hm

def planarLowerTailConstant : ℝ :=
  Real.exp (-2) * (∫ a, planarForcing a) / (2 * Real.pi)

theorem planarLowerTailConstant_positive : 0 < planarLowerTailConstant := by
  unfold planarLowerTailConstant
  exact div_pos (mul_pos (Real.exp_pos _) planarForcing_integral_positive) (by positivity)

theorem planarResolventMode_sharp_lower {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarLowerTailConstant / (‖r‖ + 2) * Real.exp (-‖r‖) ≤ planarResolventMode r := by
  convert planarResolventMode_sharp_lower_raw hr using 1
  unfold planarLowerTailConstant
  rw [show -(‖r‖ + 2) = -2 + -‖r‖ by ring, Real.exp_add]
  field_simp

end ContinuumCoulomb

end

end OAI
