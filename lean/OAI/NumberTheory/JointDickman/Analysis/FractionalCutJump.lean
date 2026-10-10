import OAI.NumberTheory.JointDickman.Analysis.FractionalCutIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # The lower side and the sine jump of the local contour integral -/
namespace JointDickman
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology

theorem fractionalPower_conj (z : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    conj (fractionalPowerKernel z w) = fractionalPowerKernel z (conj w) := by
  have ha : w.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi (Or.inr hw)
  rw [fractionalPowerKernel,fractionalPowerKernel,Complex.log_conj w ha,←Complex.exp_conj]
  simp only [map_mul,map_neg,Complex.conj_ofReal]

theorem fractionalCut_lower_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 η,
      F (-(t:ℂ)-(ε:ℂ)*Complex.I)*fractionalPowerKernel z (-(t:ℂ)-(ε:ℂ)*Complex.I))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I)))) := by
  let G : ℂ → ℂ := fun w => conj (F (conj w))
  have hG : ContinuousOn G (Metric.closedBall 0 R) := by
    apply Complex.continuous_conj.comp_continuousOn
    apply hF.comp Complex.continuous_conj.continuousOn
    intro w hw
    simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_conj] using hw
  have h := (Complex.continuous_conj.tendsto _).comp (fractionalCut_upper_integral hz hz1 hη hR hG)
  have hvalue : conj (∫ t : ℝ in Ioc 0 η,
      G (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) =
      ∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I)) := by
    rw [←integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G,map_mul,map_neg,Complex.conj_ofReal,starRingEnd_self_apply,←Complex.exp_conj,
      Complex.conj_I,Complex.ofReal_neg,neg_mul,mul_neg,neg_neg]
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_apply]
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  have him : (-(t:ℂ)+(ε:ℂ)*Complex.I).im ≠ 0 := by
    simpa using (show 0 < ε from hε).ne'
  rw [map_mul,fractionalPower_conj z him]
  simp only [G,map_add,map_mul,map_neg,Complex.conj_ofReal,starRingEnd_self_apply,
    Complex.conj_I,sub_eq_add_neg,mul_neg]

theorem fractionalCut_boundary_integral_phase (z η θ : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))) =
      (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ)))*Complex.exp ((θ:ℂ)*Complex.I) := by
  rw [←integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.real_smul]
  ring

theorem fractionalCut_boundary_difference (z η : ℝ) (F : ℂ → ℂ) :
    (1/(2*(Real.pi:ℂ)*Complex.I)) *
      ((∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I))) -
       (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I)))) =
      (Real.sin (Real.pi*z)/Real.pi) • (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  rw [fractionalCut_boundary_integral_phase,fractionalCut_boundary_integral_phase,←mul_sub]
  have hp : Complex.exp (((z*Real.pi):ℝ)*Complex.I) -
      Complex.exp ((-(z*Real.pi):ℝ)*Complex.I) = (2:ℂ)*Complex.I*(Real.sin (Real.pi*z):ℂ) := by
    simpa only [Real.one_rpow,Complex.ofReal_one,one_mul,mul_one] using fractionalPower_jump z 1
  rw [hp,Complex.real_smul,Complex.ofReal_div]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem fractionalCut_jump_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*Complex.I)) *
      ((∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)-(ε:ℂ)*Complex.I)*
        fractionalPowerKernel z (-(t:ℂ)-(ε:ℂ)*Complex.I)) -
       (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)+(ε:ℂ)*Complex.I)*
        fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))))
      (𝓝[>] 0) (𝓝 ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))))) := by
  have h := ((fractionalCut_lower_integral hz hz1 hη hR hF).sub
    (fractionalCut_upper_integral hz hz1 hη hR hF)).const_mul (1/(2*(Real.pi:ℂ)*Complex.I))
  rwa [fractionalCut_boundary_difference] at h

end JointDickman

end OAI
