import OAI.GroupTheory.Thompson.AnalyticOscillator
import OAI.GroupTheory.Thompson.AnalyticScalarDerivatives
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The actual radial oscillating curve

All vectors live in the concrete Euclidean-fiber L² space. The derivative
and squared-speed identities are derived from the scalar profiles and the
frequency curve, including the profile junctions.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

def v (t : ℝ) : Hilbert := wave (theta t)

def gamma (t : ℝ) : Hilbert := a t • v t

def gammaDeriv (t : ℝ) : Hilbert :=
  aDeriv t • v t + (a t * thetaDeriv t) • waveDeriv (theta t)

def u (t : ℝ) : Hilbert := ‖gammaDeriv t‖⁻¹ • gammaDeriv t

theorem v_norm (t : ℝ) : ‖v t‖ = 1 := wave_norm _

theorem continuous_v : Continuous v := continuous_wave.comp continuous_theta

theorem continuous_gamma : Continuous gamma := continuous_a.smul continuous_v

theorem hasDerivAt_v (t : ℝ) :
    HasDerivAt v (thetaDeriv t • waveDeriv (theta t)) t := by
  exact (hasDerivAt_wave (theta t)).scomp t (hasDerivAt_theta t)

theorem hasDerivAt_gamma (t : ℝ) : HasDerivAt gamma (gammaDeriv t) t := by
  have h := (hasDerivAt_a t).fun_smul (hasDerivAt_v t)
  exact h.congr_deriv (by simp only [gammaDeriv, mul_smul, add_comm])

theorem gamma_norm (t : ℝ) : ‖gamma t‖ = |a t| := by
  simp only [gamma, norm_smul, Real.norm_eq_abs, v_norm, mul_one]

@[simp] theorem gamma_zero : gamma 0 = 0 := by
  simp [gamma, a_of_le_two (by norm_num : (0 : ℝ) ≤ 2)]

theorem gamma_of_le_one {t : ℝ} (ht : t ≤ 1) : gamma t = (t / 8) • wave 0 := by
  rw [gamma, a_of_le_two (by linarith), v, theta_of_le_one ht]

theorem gammaDeriv_of_le_one {t : ℝ} (ht : t ≤ 1) :
    gammaDeriv t = (1 / 8 : ℝ) • wave 0 := by
  simp [gammaDeriv, v, aDeriv_of_le_two (by linarith : t ≤ 2),
    theta_of_le_one ht, thetaDeriv_of_le_one ht]

theorem gammaDeriv_norm_sq (t : ℝ) :
    ‖gammaDeriv t‖ ^ 2 = (aDeriv t) ^ 2 + (a t) ^ 2 * (thetaDeriv t) ^ 2 / 3 := by
  rw [gammaDeriv, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_one, mul_pow, sq_abs,
    waveDeriv_norm_sq, real_inner_smul_left, real_inner_smul_right,
    v, wave_norm, wave_inner_waveDeriv, mul_zero, add_zero]
  ring

theorem gammaDeriv_speed_lower (t : ℝ) : (1 / 8 : ℝ) ≤ ‖gammaDeriv t‖ := by
  have heq := gammaDeriv_norm_sq t
  have hn := norm_nonneg (gammaDeriv t)
  by_cases ht : t ≤ 2
  · rw [aDeriv_of_le_two ht] at heq
    nlinarith [mul_nonneg (sq_nonneg (a t)) (sq_nonneg (thetaDeriv t))]
  · have ha := a_lower_of_two_le (le_of_not_ge ht)
    rw [thetaDeriv_of_two_le (le_of_not_ge ht)] at heq
    nlinarith [sq_nonneg (aDeriv t), sq_nonneg (a t - 1 / 4)]

theorem gammaDeriv_norm_pos (t : ℝ) : 0 < ‖gammaDeriv t‖ := by
  have := gammaDeriv_speed_lower t
  linarith

theorem gammaDeriv_ne_zero (t : ℝ) : gammaDeriv t ≠ 0 :=
  norm_pos_iff.mp (gammaDeriv_norm_pos t)

theorem u_norm (t : ℝ) : ‖u t‖ = 1 :=
  norm_smul_inv_norm (gammaDeriv_ne_zero t)

theorem gammaDeriv_eq_norm_smul_u (t : ℝ) :
    gammaDeriv t = ‖gammaDeriv t‖ • u t := by
  simp only [u, smul_smul, mul_inv_cancel₀ (ne_of_gt (gammaDeriv_norm_pos t)), one_smul]

theorem u_of_le_one {t : ℝ} (ht : t ≤ 1) : u t = v t := by
  rw [u, gammaDeriv_of_le_one ht]
  simp [v, theta_of_le_one ht, norm_smul, wave_norm, smul_smul]

theorem gammaDeriv_inner_v (t : ℝ) : inner (𝕜 := ℝ) (gammaDeriv t) (v t) = aDeriv t := by
  have hz : inner (𝕜 := ℝ) (waveDeriv (theta t)) (v t) = 0 := by
    rw [real_inner_comm]
    exact wave_inner_waveDeriv _
  simp [gammaDeriv, inner_add_left, real_inner_smul_left, hz, v_norm]

theorem u_inner_v (t : ℝ) : inner (𝕜 := ℝ) (u t) (v t) = aDeriv t / ‖gammaDeriv t‖ := by
  simp only [u, real_inner_smul_left, gammaDeriv_inner_v, div_eq_mul_inv]
  ring

theorem u_inner_v_nonneg (t : ℝ) : 0 ≤ inner (𝕜 := ℝ) (u t) (v t) := by
  rw [u_inner_v]
  exact div_nonneg (aDeriv_nonneg t) (norm_nonneg _)

theorem v_inner (s t : ℝ) : inner (𝕜 := ℝ) (v s) (v t) = sinc (theta t - theta s) :=
  wave_inner _ _

theorem gamma_inner (s t : ℝ) :
    inner (𝕜 := ℝ) (gamma s) (gamma t) = a s * a t * sinc (theta t - theta s) := by
  simp only [gamma, real_inner_smul_left, real_inner_smul_right, v_inner]
  ring

theorem gamma_sub_norm_sq (s t : ℝ) :
    ‖gamma t - gamma s‖ ^ 2 = (a s) ^ 2 + (a t) ^ 2 -
      2 * (a s * a t * sinc (theta t - theta s)) := by
  rw [norm_sub_rev, norm_sub_sq_real, gamma_norm, gamma_norm, sq_abs, sq_abs,
    gamma_inner]
  ring

theorem gammaDeriv_speed_eq_of_le_one {t : ℝ} (ht : t ≤ 1) :
    ‖gammaDeriv t‖ = 1 / 8 := by
  rw [gammaDeriv_of_le_one ht, norm_smul, Real.norm_eq_abs, wave_norm]
  norm_num

theorem gammaDeriv_speed_inf : sInf (range fun t => ‖gammaDeriv t‖) = 1 / 8 := by
  have hne : (range fun t => ‖gammaDeriv t‖).Nonempty := ⟨_, mem_range_self 0⟩
  have hb : BddBelow (range fun t => ‖gammaDeriv t‖) :=
    ⟨1 / 8, by rintro _ ⟨t, rfl⟩; exact gammaDeriv_speed_lower t⟩
  apply le_antisymm
  · have := csInf_le hb (mem_range_self (f := fun t => ‖gammaDeriv t‖) 0)
    simpa only [gammaDeriv_speed_eq_of_le_one (by norm_num : (0 : ℝ) ≤ 1)] using this
  · apply le_csInf hne
    rintro _ ⟨t, rfl⟩
    exact gammaDeriv_speed_lower t

end ThompsonNonamenability.Analytic

end

end OAI
