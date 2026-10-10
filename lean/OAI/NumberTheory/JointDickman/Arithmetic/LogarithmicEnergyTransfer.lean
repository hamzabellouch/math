import OAI.NumberTheory.JointDickman.Analysis.MellinEnergyTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! # Returning from logarithmic measure to the original short-average variable -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap

/-- On a positive block the Jacobian costs at most the upper endpoint. -/
theorem schwartz_logarithmic_energy_le (P : 𝓢(ℝ, ℂ)) {X Y : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (δ : ℝ) :
    (∫ x in X..Y, ‖P (Real.log x + δ)‖ ^ 2) ≤
      Y * ∫ v : ℝ, ‖P v‖ ^ 2 := by
  let Q : ℝ → ℝ := fun v => ‖P (v + δ)‖ ^ 2
  have hQ : Continuous Q := (P.continuous.comp (continuous_id.add_const δ)).norm.pow 2
  have hlog : ContinuousOn Real.log (Set.uIcc X Y) := by
    rw [Set.uIcc_of_le hXY]
    intro x hx
    exact (Real.continuousAt_log (hX.trans_le hx.1).ne').continuousWithinAt
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc X Y) := by
    apply continuousOn_id.inv₀
    intro x hx
    rw [Set.uIcc_of_le hXY] at hx
    exact (hX.trans_le hx.1).ne'
  have hG : ContinuousOn (fun x => Q (Real.log x)) (Set.uIcc X Y) :=
    hQ.comp_continuousOn hlog
  have hchange : (∫ x in X..Y, Q (Real.log x) * x⁻¹) =
      ∫ v in Real.log X..Real.log Y, Q v := by
    apply intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun x => x⁻¹) (g := Q)
    · intro x hx
      rw [Set.uIcc_of_le hXY] at hx
      exact Real.hasDerivAt_log (hX.trans_le hx.1).ne'
    · exact hinv
    · exact hQ
  have hbound : (∫ x in X..Y, Q (Real.log x)) ≤
      Y * ∫ v in Real.log X..Real.log Y, Q v := by
    rw [← hchange, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hXY hG.intervalIntegrable
      ((continuousOn_const.mul (hG.mul hinv)).intervalIntegrable)
    intro x hx
    have hx0 : 0 < x := hX.trans_le hx.1
    have hratio : 1 ≤ Y * x⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (one_le_div hx0).mpr hx.2
    have hq : 0 ≤ Q (Real.log x) := sq_nonneg _
    change Q (Real.log x) ≤ Y * (Q (Real.log x) * x⁻¹)
    nlinarith [mul_le_mul_of_nonneg_left hratio hq]
  have hI : Integrable Q := by
    have hp := (P.memLp 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact hp.comp_add_right δ
  have hwhole : (∫ v in Real.log X..Real.log Y, Q v) ≤ ∫ v : ℝ, Q v := by
    rw [intervalIntegral.integral_of_le (Real.log_le_log hX hXY)]
    exact setIntegral_le_integral hI (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have heq : (∫ v : ℝ, Q v) = ∫ v : ℝ, ‖P v‖ ^ 2 :=
    integral_add_right_eq_self (fun v : ℝ => ‖P v‖ ^ 2) δ
  exact hbound.trans ((mul_le_mul_of_nonneg_left hwhole (hX.trans_le hXY).le).trans_eq
    (congrArg (Y * ·) heq))

end JointDickman

end OAI
