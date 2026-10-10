import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyNumericAbsorb

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped Topology
open Filter

theorem quadratic_energy_log_count_le {T : ℝ} {Z : ℕ} (hT : 1 ≤ T)
    (hZu : Real.log Z ≤ 2*T) : ((Nat.log 2 (Z^14)+1 : ℕ) : ℝ) ≤ 100*T := by
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hh := Real.natLog_le_logb (Z^14) 2
  simp only [Real.logb, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hh
  have hm := (le_div_iff₀ hlog2pos).mp hh
  have hn := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Nat.log 2 (Z^14)))
  push_cast
  nlinarith

theorem quadratic_energy_grid_weight_gt_one {T : ℝ} (hT : 1 ≤ T) :
    1 < (((2*gridMomentParameter T)^2 : ℕ) : ℝ) := by
  have hl : 1 ≤ gridMomentParameter T := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hT (by norm_num : (0 : ℝ) ≤ 1/1000000)
  have hl' : (1 : ℝ) ≤ gridMomentParameter T := by exact_mod_cast hl
  push_cast
  nlinarith

theorem quadratic_energy_cutoff_bound {T : ℝ} {Z L : ℕ} (hT : 40 ≤ T)
    (hZ : 1 ≤ Z) (hZu : Real.log Z ≤ 2*T)
    (hL : (L : ℝ) ≤ (Z : ℝ)^((1 : ℝ)/50)) :
    ((2*(Z^14)*L^4 : ℕ) : ℝ) ≤ Real.exp (T^2) := by
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hLZ : (L : ℝ) ≤ Z := hL.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hZr (show (1 : ℝ)/50 ≤ 1 by norm_num))
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log 2+18*Real.log Z ≤ T^2 := by nlinarith
  calc
    _ ≤ 2*(Z : ℝ)^14*(Z : ℝ)^4 := by push_cast; gcongr
    _ = Real.exp (Real.log 2+18*Real.log Z) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        show (18 : ℝ)*Real.log Z = Real.log ((Z : ℝ)^18) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hZ0 18)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem eventually_quadratic_energy_sqrt_z :
    ∀ᶠ T : ℝ in atTop, ∀ z : ℕ, 1 ≤ z →
      T^auxiliaryExponent/2 ≤ Real.log z → 2000 ≤ Real.sqrt (z : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop auxiliaryExponent_pos).eventually_ge_atTop
    (2*Real.log ((2000 : ℝ)^2))] with T hT
  intro z hz hzl
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hh : Real.log ((2000 : ℝ)^2) ≤ Real.log z := by linarith
  have hsq : (2000 : ℝ)^2 ≤ z := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < (2000 : ℝ)^2), Real.exp_log hz0]
      using Real.exp_le_exp.mpr hh
  exact Real.le_sqrt_of_sq_le hsq

end Ostmann.QuadraticCenter

end

end OAI
