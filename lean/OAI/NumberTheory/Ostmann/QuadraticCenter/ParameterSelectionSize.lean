import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries Filter

lemma auxiliaryExponent_pos : 0 < auxiliaryExponent := by norm_num [auxiliaryExponent]
lemma auxiliaryExponent_le_one : auxiliaryExponent ≤ 1 := by norm_num [auxiliaryExponent]

theorem eventually_parameterX_log_bounds :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 1 ≤ Real.log (parameterX T : ℝ) ∧
      T ^ (8 / 5 : ℝ) / 2 ≤ Real.log (parameterX T : ℝ) ∧
      Real.log (parameterX T : ℝ) ≤ T ^ (8 / 5 : ℝ) ∧
      Real.log (Real.log (parameterX T : ℝ)) ≤ (8 / 5 : ℝ) * Real.log T := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).eventually_ge_atTop
      (2 * (Real.log 2 + 1))] with T hT hpow
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht : 0 < T := by linarith
  have hb := log_floor_exp_bounds (show Real.log 2 ≤ T ^ (8 / 5 : ℝ) by linarith)
  unfold parameterX
  have hlog : 1 ≤ Real.log (⌊Real.exp (T ^ (8 / 5 : ℝ))⌋₊ : ℝ) := by linarith [hb.2.1]
  refine ⟨hT, hlog, by linarith [hb.2.1], hb.2.2, ?_⟩
  have h := Real.log_le_log (by linarith : 0 < Real.log (⌊Real.exp (T ^ (8 / 5 : ℝ))⌋₊ : ℝ)) hb.2.2
  rw [Real.log_rpow ht] at h
  exact h

theorem eventually_parameter_cutoff :
    ∀ᶠ T : ℝ in atTop, ⌊Real.exp (2 * T)⌋₊ ≤ collisionScale 4 (parameterX T) := by
  filter_upwards [eventually_parameterX_log_bounds,
    parameterX_tendsto.eventually (eventually_collisionScale_conditions 4),
    eventually_mul_rpow_le_rpow 64 (a := 1) (b := 8 / 5) (by norm_num)]
    with T hb hc hg
  have hT : 0 < T := by linarith [hb.1]
  have hlogT : Real.log T ≤ T := le_trans (Real.log_le_sub_one_of_pos hT) (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hQ, hlogQ, _⟩ := collisionScale_estimates 4 (parameterX T) hc.1 hc.2.1 hc.2.2
  have hQpos : (0 : ℝ) < collisionScale 4 (parameterX T) := by exact_mod_cast hQ
  have hlarge : 2 * T ≤ Real.log (collisionScale 4 (parameterX T) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hlogQ
    rw [Real.rpow_one] at hg
    nlinarith [hb.2.2.1, hb.2.2.2.2]
  have he : Real.exp (2 * T) ≤ (collisionScale 4 (parameterX T) : ℝ) :=
    (Real.le_log_iff_exp_le hQpos).mp hlarge
  exact_mod_cast (Nat.floor_le (Real.exp_pos (2 * T)).le).trans he

lemma auxiliary_power_le_self {T : ℝ} (hT : 1 ≤ T) : T ^ auxiliaryExponent ≤ T := by
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hT auxiliaryExponent_le_one

theorem eventually_auxiliary_band_cutoff :
    ∀ᶠ T : ℝ in atTop,
      ⌊Real.exp (2 * T ^ auxiliaryExponent)⌋₊ ≤ collisionScale 4 (parameterX T) := by
  filter_upwards [eventually_parameter_cutoff, eventually_ge_atTop (1 : ℝ)] with T hQ hT
  exact (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith [auxiliary_power_le_self hT]))).trans hQ

end Ostmann.QuadraticCenter

end

end OAI
