import OAI.NumberTheory.JointDickman.Analysis.FractionalPowerBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

namespace OAI

/-! # Horizontal approach to the fractional-power cut and its integrable majorant -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalPower_upper_horizontal (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>] 0)
      (𝓝 ((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) := by
  apply (fractionalPower_upper_cut z ht).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have he : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,add_zero] using he.mul_const Complex.I |>.const_add (-(t:ℂ))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Complex.add_im,Complex.neg_im,Complex.ofReal_im,neg_zero,
      Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
      add_zero,zero_add] using hε.le

theorem fractionalPower_lower_horizontal (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => fractionalPowerKernel z (-(t:ℂ)-(ε:ℂ)*Complex.I)) (𝓝[>] 0)
      (𝓝 ((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I))) := by
  apply (fractionalPower_lower_cut z ht).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have he : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (he.mul_const Complex.I)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Complex.sub_im,Complex.neg_im,Complex.ofReal_im,neg_zero,
      Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
      add_zero,zero_sub,neg_lt_zero] using (show 0 < ε from hε)

theorem fractionalPower_positive (z : ℝ) {t : ℝ} (ht : 0 < t) :
    fractionalPowerKernel z (t:ℂ) = (t^(-z):ℝ) := by
  rw [fractionalPowerKernel,←Complex.ofReal_log ht.le,Real.rpow_def_of_pos ht,
    Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  congr 1
  ring

theorem fractionalPower_continuousAt_positive (z : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fractionalPowerKernel z) (t:ℂ) := by
  change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) (t:ℂ)
  have hl := continuousAt_clog (Complex.ofReal_mem_slitPlane.mpr ht)
  exact (continuousAt_const.mul hl).cexp

theorem integrable_abs_rpow_on_bounded_interval {z a b : ℝ} (hz : z < 1) :
    IntegrableOn (fun u : ℝ => |u|^(-z)) (Icc a b) := by
  have hm : AEStronglyMeasurable (fun u : ℝ => |u|^(-z)) volume := by
    exact (continuous_abs.measurable.pow_const (-z)).aestronglyMeasurable
  have hb : IntegrableOn (fun u : ℝ => |u|^(-z)) (Metric.ball 0 (|a|+|b|+1)) := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := z) (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (by simpa using hz) _ hm
    filter_upwards with u
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _),one_mul]
    exact le_rfl
  apply hb.mono_set
  intro u hu
  rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
  have hua : -(|a|+|b|+1) < u := by linarith [neg_abs_le a,abs_nonneg b,hu.1]
  have hub : u < |a|+|b|+1 := by linarith [le_abs_self b,abs_nonneg a,hu.2]
  exact abs_lt.mpr ⟨hua,hub⟩

end JointDickman

end OAI
