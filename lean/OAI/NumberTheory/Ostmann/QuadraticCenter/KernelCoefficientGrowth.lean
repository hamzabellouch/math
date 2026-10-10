import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientScaleLower
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped Topology
open Filter

theorem commonCenterCutoff_exp_lower {T : ℝ} {Z : ℕ}
    (hT : 1 ≤ T) (hTlog : 20*Real.log 2 ≤ T) (hZl : T/2 ≤ Real.log Z) :
    Real.exp (T/4) ≤ (commonCenterCutoff Z : ℝ) := by
  have hZne : Z ≠ 0 := by
    intro hZ
    simp only [hZ, Nat.cast_zero, Real.log_zero] at hZl
    linarith
  have hZ0 : (0 : ℝ) < Z := by exact_mod_cast Nat.pos_of_ne_zero hZne
  have he : 2*Real.exp (T/4) ≤ (Z : ℝ)^(3/5 : ℝ) := by
    calc
      _ = Real.exp (Real.log 2+T/4) := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (Real.log Z*(3/5 : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := (Real.rpow_def_of_pos hZ0 _).symm
  have hone : 1 ≤ Real.exp (T/4) := Real.one_le_exp_iff.mpr (by linarith)
  have hf := Nat.lt_floor_add_one ((Z : ℝ)^(3/5 : ℝ))
  change (Z : ℝ)^(3/5 : ℝ) < (commonCenterCutoff Z : ℝ)+1 at hf
  linarith

theorem eventually_kernel_polynomial_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, (16/c)^2*T^4 ≤ Real.exp (T/4) := by
  let C : ℝ := (16/c)^2
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_const_add_log_le_rpow (4*Real.log C) 16 (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with T hlog hT
  have hT0 : 0 < T := by linarith
  rw [Real.rpow_one] at hlog
  have he : Real.log C+4*Real.log T ≤ T/4 := by linarith
  calc
    _ = Real.exp (Real.log C+4*Real.log T) := by
      rw [Real.exp_add, Real.exp_log hC,
        show (4 : ℝ)*Real.log T = Real.log (T^4) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hT0 4)]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem eventually_kernel_repeat_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z J : ℕ), T/2 ≤ Real.log Z →
      commonCenterCutoff Z ≤ J →
      4*((evenMomentParameter (parameterX T) Z : ℝ)+1)^2 ≤ Real.sqrt (J : ℝ)*c := by
  filter_upwards [eventually_kernel_polynomial_scale c hc,
    eventually_evenMomentParameter_bound,
    eventually_mul_rpow_le_rpow 14 (a := 3/5) (b := 1) (by norm_num),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (20*Real.log 2)]
    with T hpoly hkbound hpow hT hTlog
  intro Z J hZl hJ
  have hJexp : Real.exp (T/4) ≤ (J : ℝ) :=
    (commonCenterCutoff_exp_lower hT hTlog hZl).trans (by exact_mod_cast hJ)
  have hk : (evenMomentParameter (parameterX T) Z : ℝ) ≤ T :=
    (hkbound Z hZl).trans (by simpa only [Real.rpow_one] using hpow)
  have hJpoly := hpoly.trans hJexp
  have hJsq : (16*T^2)^2 ≤ (Real.sqrt (J : ℝ)*c)^2 := by
    have hh := mul_le_mul_of_nonneg_right hJpoly (sq_nonneg c)
    have he : ((16/c)^2*T^4)*c^2 = (16*T^2)^2 := by field_simp
    rw [he] at hh
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg J)] using hh
  have hroot : 16*T^2 ≤ Real.sqrt (J : ℝ)*c :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hJsq
  apply le_trans _ hroot
  have hsq := pow_le_pow_left₀
    (show 0 ≤ (evenMomentParameter (parameterX T) Z : ℝ)+1 by positivity)
    (show (evenMomentParameter (parameterX T) Z : ℝ)+1 ≤ 2*T by linarith) 2
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
