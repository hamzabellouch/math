import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularUpperMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! Entire upper Mellin tails of every actual angular series at a positive scale. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

def cubicThetaScaledAngularAxis (ℓ : ℤ) (z : ℂ) (r t : ℝ) : ℂ :=
  cubicThetaNonconstant (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (z,r*t)

lemma cubicThetaScaledAngularUpper_locallyIntegrable (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    LocallyIntegrable (thetaUpper (cubicThetaScaledAngularAxis ℓ z r)) := by
  let g : ℝ→ℂ := fun t => cubicThetaNonconstant
    (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (z,r*max (1/2) t)
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cubicThetaAngular_continuousAt (by norm_num : (0:ℝ)≤81)
      cubicThetaArithmeticCoefficient_bound ℓ (by positivity : 0<r*max (1/2) t)).comp
    fun_prop
  have he : thetaUpper (cubicThetaScaledAngularAxis ℓ z r)=(Ioi 1).indicator g := by
    funext t
    by_cases ht : 1<t
    · simp only [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht),cubicThetaScaledAngularAxis,g,
        max_eq_right (by linarith : (1/2:ℝ)≤t)]
    · simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from ht)]
  rw [he]
  exact hg.locallyIntegrable.indicator measurableSet_Ioi

lemma cubicThetaScaledAngularUpper_isBigO (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    thetaUpper (cubicThetaScaledAngularAxis ℓ z r) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi/18*r)*t)) := by
  apply IsBigO.of_bound (cubicThetaAngularExpConstant 81 ℓ)
  filter_upwards [eventually_ge_atTop (max 2 r⁻¹)] with t ht
  have ht1 : 1<t := by linarith [le_trans (le_max_left (2:ℝ) r⁻¹) ht]
  have hrt : 1≤r*t := by
    have hi : r⁻¹≤t := le_trans (le_max_right (2:ℝ) r⁻¹) ht
    have h := mul_le_mul_of_nonneg_left hi hr.le
    simpa only [mul_inv_cancel₀ hr.ne'] using h
  rw [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from ht1),cubicThetaScaledAngularAxis,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc,neg_mul] using
    cubicThetaAngular_exponential_bound (by norm_num : (0:ℝ)≤81)
      cubicThetaArithmeticCoefficient_bound ℓ hrt z

lemma cubicThetaScaledAngularUpper_small (ℓ : ℤ) (z : ℂ) (r : ℝ) (s : ℂ) :
    thetaUpper (cubicThetaScaledAngularAxis ℓ z r) =O[𝓝[>] 0]
      (fun t : ℝ => t^(-(s.re-1))) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  rw [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr ht.le),norm_zero]
  simp

theorem cubicThetaScaledAngularUpper_mellinConvergent (ℓ : ℤ) (z : ℂ) {r : ℝ}
    (hr : 0<r) (s : ℂ) : MellinConvergent (thetaUpper (cubicThetaScaledAngularAxis ℓ z r)) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaScaledAngularUpper_locallyIntegrable ℓ z hr).locallyIntegrableOn _)
    (cubicThetaScaledAngularUpper_isBigO ℓ z hr) (cubicThetaScaledAngularUpper_small ℓ z r s)
    (by linarith)

theorem cubicThetaScaledAngularUpper_entire (ℓ : ℤ) (z : ℂ) {r : ℝ} (hr : 0<r) :
    Differentiable ℂ (mellin (thetaUpper (cubicThetaScaledAngularAxis ℓ z r))) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by positivity : 0<Real.pi/18*r)
    ((cubicThetaScaledAngularUpper_locallyIntegrable ℓ z hr).locallyIntegrableOn _)
    (cubicThetaScaledAngularUpper_isBigO ℓ z hr) (cubicThetaScaledAngularUpper_small ℓ z r s)
    (by linarith)

end CubicFirstMoment

end

end OAI
