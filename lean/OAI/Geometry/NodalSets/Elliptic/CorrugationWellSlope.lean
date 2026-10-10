import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def corrugationSlope (a R r : ℝ) : ℝ := a*r*expNegInvGlue (R^2-r^2)

lemma corrugationSlope_smooth (a R : ℝ) : ContDiff ℝ ∞ (corrugationSlope a R) :=
  (contDiff_const.mul contDiff_id).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2)))

lemma corrugationSlope_nonneg {a R r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    0 ≤ corrugationSlope a R r := mul_nonneg (mul_nonneg ha hr) (expNegInvGlue.nonneg _)

lemma corrugationSlope_pos {a R r : ℝ} (ha : 0 < a) (hr : 0 < r) (hR : r < R) :
    0 < corrugationSlope a R r := by
  apply mul_pos (mul_pos ha hr) (expNegInvGlue.pos_of_pos _)
  nlinarith

lemma corrugationSlope_zero {a R r : ℝ} (hR : 0 ≤ R) (hr : R ≤ r) :
    corrugationSlope a R r = 0 := by
  unfold corrugationSlope
  rw [expNegInvGlue.zero_of_nonpos (by nlinarith),mul_zero]

lemma corrugationSlope_center (a R : ℝ) : corrugationSlope a R 0 = 0 := by
  simp [corrugationSlope]

lemma corrugationSlope_formula {a R r : ℝ} (hr : 0 ≤ r) (hR : r < R) :
    corrugationSlope a R r = a*r*Real.exp (-(R^2-r^2)⁻¹) := by
  have ht : 0 < R^2-r^2 := by nlinarith
  simp [corrugationSlope,expNegInvGlue,not_le.mpr ht]

lemma expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue ((t⁻¹)^2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 t

lemma corrugationSlope_hasDerivAt (a R r : ℝ) :
    HasDerivAt (corrugationSlope a R)
      (a * expNegInvGlue (R^2-r^2) * (1-2*r^2*((R^2-r^2)⁻¹)^2)) r := by
  have h := ((hasDerivAt_id r).const_mul a).mul
    ((expNegInvGlue_hasDerivAt (R^2-r^2)).comp r
      ((hasDerivAt_const r (R^2)).sub ((hasDerivAt_id r).pow 2)))
  change HasDerivAt (corrugationSlope a R) _ r at h
  convert h using 1
  dsimp
  ring

lemma corrugationSlope_deriv (a R r : ℝ) :
    deriv (corrugationSlope a R) r =
      a * expNegInvGlue (R^2-r^2) * (1-2*r^2*((R^2-r^2)⁻¹)^2) :=
  (corrugationSlope_hasDerivAt a R r).deriv

lemma corrugationSlope_negative_deriv_le {a R r : ℝ} (ha : 0 ≤ a) :
    max (-(deriv (corrugationSlope a R) r)) 0 ≤
      2*a*r^2*((R^2-r^2)⁻¹)^2*expNegInvGlue (R^2-r^2) := by
  rw [corrugationSlope_deriv]
  apply max_le
  · have h := mul_nonneg ha (expNegInvGlue.nonneg (R^2-r^2))
    nlinarith
  · have h := expNegInvGlue.nonneg (R^2-r^2)
    positivity

lemma expNegInvGlue_le_one (t : ℝ) : expNegInvGlue t ≤ 1 := by
  by_cases ht : t ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos ht]; norm_num
  · have ht' : 0 < t := lt_of_not_ge ht
    simp only [expNegInvGlue,ite_eq_right ht]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr ht'.le))

lemma corrugationSlope_le_one {a R r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hR0 : 0 ≤ R) (hR : R ≤ 1) (hr : 0 ≤ r) : corrugationSlope a R r ≤ 1 := by
  by_cases hrR : r < R
  · have hr1 : r ≤ 1 := hrR.le.trans hR
    calc
      corrugationSlope a R r ≤ a*r*1 :=
        mul_le_mul_of_nonneg_left (expNegInvGlue_le_one _) (mul_nonneg ha hr)
      _ ≤ 1 := by nlinarith
  · rw [corrugationSlope_zero hR0 (le_of_not_gt hrR)]
    norm_num

end
end Yau.Geometry

end OAI
