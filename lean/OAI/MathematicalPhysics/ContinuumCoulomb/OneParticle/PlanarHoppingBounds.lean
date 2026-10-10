import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHopping

namespace OAI

/-! Matching exponential brackets for the actual contact hopping integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planar_contact_distance_bounds {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    d - 1 ≤ ‖r - d • planarAxis 0‖ ∧ ‖r - d • planarAxis 0‖ ≤ d + 1 := by
  have hn : ‖d • planarAxis 0‖ = d := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (by linarith)]
  have h₁ : d ≤ ‖r‖ + ‖r - d • planarAxis 0‖ := by
    calc
      _ = ‖r - (r - d • planarAxis 0)‖ := by rw [show r - (r - d • planarAxis 0) =
        d • planarAxis 0 by abel, hn]
      _ ≤ _ := norm_sub_le _ _
  have h₂ := norm_sub_le r (d • planarAxis 0)
  rw [hn] at h₂
  constructor <;> linarith

theorem planarHopping_mode_upper {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    planarResolventMode (r - d • planarAxis 0) ≤ (d + 1) * Real.exp (3 - d) := by
  obtain ⟨hlo, hhi⟩ := planar_contact_distance_bounds hr hd
  calc
    _ ≤ ‖r - d • planarAxis 0‖ * Real.exp (2 - ‖r - d • planarAxis 0‖) :=
      planarResolventMode_sharp_upper (by linarith)
    _ ≤ _ := mul_le_mul hhi (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_pos _).le (by linarith)

theorem planarHopping_mode_lower {r : PlanarPosition} {d : ℝ}
    (hr : ‖r‖ ≤ 1) (hd : 2 ≤ d) :
    planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1)) ≤
      planarResolventMode (r - d • planarAxis 0) := by
  obtain ⟨hlo, hhi⟩ := planar_contact_distance_bounds hr hd
  have hfrac : planarLowerTailConstant / (d + 3) ≤
      planarLowerTailConstant / (‖r - d • planarAxis 0‖ + 2) :=
    div_le_div_of_nonneg_left planarLowerTailConstant_positive.le (by positivity) (by linarith)
  calc
    _ ≤ planarLowerTailConstant / (‖r - d • planarAxis 0‖ + 2) *
        Real.exp (-‖r - d • planarAxis 0‖) :=
      mul_le_mul hfrac (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (div_nonneg planarLowerTailConstant_positive.le (by positivity))
    _ ≤ _ := planarResolventMode_sharp_lower (by linarith)

def planarHoppingUpperConstant : ℝ :=
  Real.exp 3 * (∫ r, planarForcing r) / (2 * ∫ r, planarResolventMode r ^ 2)

def planarHoppingLowerConstant : ℝ :=
  planarLowerTailConstant * Real.exp (-1) * (∫ r, planarForcing r) /
    (2 * ∫ r, planarResolventMode r ^ 2)

theorem planarHoppingUpperConstant_positive : 0 < planarHoppingUpperConstant := by
  unfold planarHoppingUpperConstant
  exact div_pos (mul_pos (Real.exp_pos _) planarForcing_integral_positive)
    (mul_pos (by norm_num) planarResolventMode_square_integral_positive)

theorem planarHoppingLowerConstant_positive : 0 < planarHoppingLowerConstant := by
  unfold planarHoppingLowerConstant
  exact div_pos (mul_pos (mul_pos planarLowerTailConstant_positive (Real.exp_pos _))
    planarForcing_integral_positive)
    (mul_pos (by norm_num) planarResolventMode_square_integral_positive)

theorem planarHopping_sharp_upper {d : ℝ} (hd : 2 ≤ d) :
    planarHopping d ≤ planarHoppingUpperConstant * (d + 1) * Real.exp (-d) := by
  have hpt (r : PlanarPosition) : planarHoppingIntegrand d r ≤
      planarForcing r * ((d + 1) * Real.exp (3 - d)) := by
    by_cases hf : planarForcing r = 0
    · simp only [planarHoppingIntegrand, hf, zero_mul, le_refl]
    have hr : ‖r‖ ≤ 1 := le_of_lt (lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
    exact mul_le_mul_of_nonneg_left (planarHopping_mode_upper hr hd) (planarForcing_nonnegative r)
  have hi := integral_mono (planarHoppingIntegrand_integrable d)
    (planarForcing_integrable.mul_const ((d + 1) * Real.exp (3 - d))) hpt
  rw [integral_mul_const] at hi
  have hden : 0 ≤ 2 * ∫ r, planarResolventMode r ^ 2 := by
    positivity
  have h := div_le_div_of_nonneg_right hi hden
  unfold planarHopping planarHoppingUpperConstant
  convert h using 1
  rw [show 3 - d = 3 + -d by ring, Real.exp_add]
  ring

theorem planarHopping_sharp_lower {d : ℝ} (hd : 2 ≤ d) :
    planarHoppingLowerConstant / (d + 3) * Real.exp (-d) ≤ planarHopping d := by
  have hpt (r : PlanarPosition) :
      planarForcing r * (planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1))) ≤
        planarHoppingIntegrand d r := by
    by_cases hf : planarForcing r = 0
    · simp only [planarHoppingIntegrand, hf, zero_mul, le_refl]
    have hr : ‖r‖ ≤ 1 := le_of_lt (lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
    exact mul_le_mul_of_nonneg_left (planarHopping_mode_lower hr hd) (planarForcing_nonnegative r)
  have hi := integral_mono
    (planarForcing_integrable.mul_const
      (planarLowerTailConstant / (d + 3) * Real.exp (-(d + 1))))
    (planarHoppingIntegrand_integrable d) hpt
  rw [integral_mul_const] at hi
  have hden : 0 ≤ 2 * ∫ r, planarResolventMode r ^ 2 := by
    positivity
  have h := div_le_div_of_nonneg_right hi hden
  unfold planarHopping planarHoppingLowerConstant
  convert h using 1
  rw [show -(d + 1) = -1 + -d by ring, Real.exp_add]
  ring

end ContinuumCoulomb

end

end OAI
