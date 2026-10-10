import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleBranch
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace OAI

/-! # The two boundary values on the fractional-power branch cut -/
namespace JointDickman
open Filter Set
open scoped Topology

noncomputable def fractionalPowerKernel (z : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(z:ℂ)*Complex.log w)

theorem fractionalPower_boundary_value (z θ : ℝ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(z:ℂ)*((Real.log t:ℂ)+(θ:ℂ)*Complex.I)) =
      (t^(-z):ℝ)*Complex.exp ((-(z*θ):ℝ)*Complex.I) := by
  rw [Real.rpow_def_of_pos ht,Complex.ofReal_exp]
  push_cast
  rw [show -(z:ℂ)*((Real.log t:ℂ)+(θ:ℂ)*Complex.I) =
    (Real.log t:ℂ)*(-z) + -(z*θ)*Complex.I by ring,Complex.exp_add]

theorem fractionalPower_upper_cut (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fractionalPowerKernel z)
      (𝓝[{w : ℂ | 0 ≤ w.im}] (-(t:ℂ)))
      (𝓝 ((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) := by
  change Tendsto (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _ _
  have hh := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := -(t:ℂ)) (by simpa using neg_neg_of_pos ht) (by simp)
  have h := (hh.const_mul (-(z:ℂ))).cexp
  have hn : ‖-(t:ℂ)‖ = t := by simp [abs_of_pos ht]
  simpa only [hn,fractionalPower_boundary_value z Real.pi ht] using h

theorem fractionalPower_lower_cut (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fractionalPowerKernel z)
      (𝓝[{w : ℂ | w.im < 0}] (-(t:ℂ)))
      (𝓝 ((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I))) := by
  change Tendsto (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _ _
  have hh := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := -(t:ℂ)) (by simpa using neg_neg_of_pos ht) (by simp)
  have h := (hh.const_mul (-(z:ℂ))).cexp
  have hn : ‖-(t:ℂ)‖ = t := by simp [abs_of_pos ht]
  rw [hn,show (Real.log t:ℂ)-(Real.pi:ℂ)*Complex.I =
    (Real.log t:ℂ)+(-Real.pi:ℝ)*Complex.I by push_cast; ring] at h
  simpa only [fractionalPower_boundary_value z (-Real.pi) ht,
    mul_neg,neg_neg] using h

theorem fractionalPower_jump (z t : ℝ) :
    (t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I) -
      (t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I) =
      (2:ℂ)*Complex.I*(Real.sin (Real.pi*z):ℂ)*(t^(-z):ℝ) := by
  rw [←mul_sub,Complex.exp_mul_I,Complex.exp_mul_I]
  simp only [Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg]
  rw [←Complex.ofReal_sin]
  rw [mul_comm Real.pi z]
  ring

theorem fractionalPower_norm (z : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ‖fractionalPowerKernel z w‖ = ‖w‖^(-z) := by
  unfold fractionalPowerKernel
  rw [show -(z:ℂ) = ((-z:ℝ):ℂ) by simp]
  exact norm_exp_real_mul_of_exp_eq (-z) (Complex.exp_log hw)

theorem fractionalPower_horizontal_bound {z : ℝ} (hz : 0 ≤ z) {u v : ℝ} (hu : u ≠ 0) :
    ‖fractionalPowerKernel z ((u:ℂ)+(v:ℂ)*Complex.I)‖ ≤ |u|^(-z) := by
  have hn : |u| ≤ ‖(u:ℂ)+(v:ℂ)*Complex.I‖ := by
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero] using
      Complex.abs_re_le_norm ((u:ℂ)+(v:ℂ)*Complex.I)
  have hw : (u:ℂ)+(v:ℂ)*Complex.I ≠ 0 := by
    intro he
    rw [he,norm_zero] at hn
    exact hu (abs_eq_zero.mp (le_antisymm hn (abs_nonneg u)))
  rw [fractionalPower_norm z hw]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hu) hn (neg_nonpos.mpr hz)

end JointDickman

end OAI
