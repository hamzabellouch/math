import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped Topology
open Filter

theorem high_weight_error_budget_eventually (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧
      Real.log 3 + ((1 : ℝ) / 100000 + 1 / 4) * Real.log T +
        T ^ ((1 : ℝ) / 3) * (3 * Real.log T + C) ≤ T ^ ((3 : ℝ) / 4) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hconst := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).eventually_ge_atTop
    (max C (Real.log 3))
  have hsix := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop 6
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlog, hconst, hsix] with T hT hl hc h6
  refine ⟨hT, ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hl' : Real.log T ≤ T ^ ((1 : ℝ) / 12) := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hl0,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)] using hl
  have hC : C ≤ T ^ ((1 : ℝ) / 12) := (le_max_left _ _).trans hc
  have h3 : Real.log 3 ≤ T ^ ((1 : ℝ) / 12) := (le_max_right _ _).trans hc
  have hprod : T ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 12) = T ^ ((5 : ℝ) / 12) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hp : T ^ ((1 : ℝ) / 12) ≤ T ^ ((5 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hlow : ((1 : ℝ) / 100000 + 1 / 4) * Real.log T ≤ T ^ ((1 : ℝ) / 12) := by
    nlinarith
  have hhigh : T ^ ((1 : ℝ) / 3) * (3 * Real.log T + C) ≤
      4 * T ^ ((5 : ℝ) / 12) := by
    have ht := mul_le_mul_of_nonneg_left (show 3 * Real.log T + C ≤
      4 * T ^ ((1 : ℝ) / 12) by linarith) (Real.rpow_nonneg hT0.le ((1 : ℝ) / 3))
    nlinarith [hprod]
  calc
    _ ≤ 6 * T ^ ((5 : ℝ) / 12) := by linarith
    _ ≤ T ^ ((1 : ℝ) / 3) * T ^ ((5 : ℝ) / 12) :=
      mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hT0.le _)
    _ = T ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_add hT0]; norm_num

theorem high_weight_loglog_le {T : ℝ} (hT : 2 ≤ T) {X : ℕ} (hX : 1 ≤ X)
    (hupper : (X : ℝ) ≤ Real.exp (T ^ 2)) :
    Real.log (Real.log (2 * (X : ℝ))) ≤ 3 * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : Real.log (X : ℝ) ≤ T ^ 2 := by
    have hh := Real.log_le_log hX0 hupper
    simpa only [Real.log_exp] using hh
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinner : Real.log (2 * (X : ℝ)) ≤ T ^ 3 := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - 2) (sq_nonneg T)]
  have hi : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos (by
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith)
  have hh := Real.log_le_log hi hinner
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

end Ostmann.QuadraticCenter

end OAI
