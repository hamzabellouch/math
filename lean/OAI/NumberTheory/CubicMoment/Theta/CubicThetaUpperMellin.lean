import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExponential
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! Mellin integration of the genuine cubic Fourier expansion above unit
height, with constants uniform in horizontal position. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaNonconstant_continuous_height {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n) (z : ℂ) :
    ContinuousOn (fun v : ℝ => cubicThetaNonconstant a (z,v)) (Ioi 0) := by
  intro v hv
  exact ((cubicThetaNonconstant_continuousAt hC ha (p := (z,v)) hv).comp
    (f := fun v : ℝ => (z,v)) (by fun_prop)).continuousWithinAt

lemma cubicTheta_upper_integrable {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (z s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*cubicThetaNonconstant a (z,v)) (Ioi 1) :=
  theta_upper_integrable (show 0 < Real.pi/9 by positivity)
    (cubicThetaNonconstant_continuous_height hC ha z)
    (fun v hv => cubicThetaNonconstant_exponential_bound hC ha hv z) s

lemma cubicTheta_upper_mellinConvergent {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (z s : ℂ) :
    MellinConvergent (thetaUpper (fun v : ℝ => cubicThetaNonconstant a (z,v))) s :=
  thetaUpper_mellinConvergent (show 0 < Real.pi/9 by positivity)
    (cubicThetaNonconstant_continuous_height hC ha z)
    (fun v hv => cubicThetaNonconstant_exponential_bound hC ha hv z) s

/-- This is a bound for the constructed cusp integral, with no automorphy
or functional equation required. -/
theorem cubicTheta_upper_mellin_bound {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (z s : ℂ) :
    ‖∫ v : ℝ in Ioi 1, (v:ℂ)^(s-1)*cubicThetaNonconstant a (z,v)‖ ≤
      (18*cubicThetaExpConstant C/Real.pi)*Real.exp (18*(1+‖s‖)^2/Real.pi) := by
  have h := theta_upper_norm_bound (show 0 < Real.pi/9 by positivity)
    (fun v hv => cubicThetaNonconstant_exponential_bound hC ha hv z) s
  convert h using 1; congr 1 <;> ring_nf

lemma cubicTheta_upper_integrable_global {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n) (z : ℂ) :
    Integrable (thetaUpper (fun v : ℝ => cubicThetaNonconstant a (z,v))) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  simpa only [sub_self,Complex.cpow_zero,one_mul] using cubicTheta_upper_integrable hC ha z 1

/-- The upper-half Mellin integral is entire before imposing any modular
transformation law; its lower endpoint is bounded away from zero. -/
theorem cubicTheta_upper_mellin_entire {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n) (z : ℂ) :
    Differentiable ℂ (mellin (thetaUpper (fun v : ℝ => cubicThetaNonconstant a (z,v)))) := by
  intro s
  have htop : thetaUpper (fun v : ℝ => cubicThetaNonconstant a (z,v)) =O[atTop]
      (fun v : ℝ => Real.exp (-(Real.pi/9)*v)) := by
    apply IsBigO.of_bound (cubicThetaExpConstant C)
    filter_upwards [eventually_gt_atTop (1:ℝ)] with v hv
    rw [thetaUpper,indicator_of_mem (show v ∈ Ioi (1:ℝ) from hv),Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact cubicThetaNonconstant_exponential_bound hC ha hv.le z
  have hbot : thetaUpper (fun v : ℝ => cubicThetaNonconstant a (z,v)) =O[𝓝[>] 0]
      (fun v : ℝ => v^(-(s.re-1))) := by
    apply IsBigO.of_bound 0
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with v hv
    rw [thetaUpper,indicator_of_notMem (show v ∉ Ioi (1:ℝ) from not_lt.mpr hv.le),norm_zero]
    simp
  exact mellin_differentiableAt_of_isBigO_rpow_exp (show 0 < Real.pi/9 by positivity)
    ((cubicTheta_upper_integrable_global hC ha z).locallyIntegrable.locallyIntegrableOn _)
    htop hbot (by linarith)

end CubicFirstMoment

end

end OAI
