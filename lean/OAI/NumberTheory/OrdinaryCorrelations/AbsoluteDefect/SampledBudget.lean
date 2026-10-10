import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryBinnedErrorBudget

lemma sampled_budget {A T x e a b c : ℝ} (hA : 0≤A) (hT : T≤x)
    (hx : 1≤x) (he : 0≤e) (he' : 2*e≤x) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    A*(T+1+2*(x+e))*(4*(4*(x+e)*a+c+2*(x+e)*b+6*e)/(x-e)^2) ≤
      512*A*(a+b+e/x+c/x) := by
  let w := a+b+e/x+c/x
  have hx0 : 0<x := by linarith
  have hd : 0<x-e := by linarith
  have hw : 0≤w := by dsimp [w]; positivity
  have hid : x*w=x*a+x*b+e+c := by dsimp [w]; field_simp
  have ho : T+1+2*(x+e)≤5*x := by linarith
  have hn : 4*(4*(x+e)*a+c+2*(x+e)*b+6*e)≤24*x*w := by
    have hae := mul_le_mul_of_nonneg_right he' ha
    have hbe := mul_le_mul_of_nonneg_right he' hb
    have hxb := mul_nonneg hx0.le hb
    nlinarith only [hid,hae,hbe,hxb,hc]
  have hd' : x^2≤4*(x-e)^2 := by nlinarith only [he,he',sq_nonneg (x-2*e)]
  have hf : 4*(4*(x+e)*a+c+2*(x+e)*b+6*e)/(x-e)^2≤96*w/x := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    apply hn.trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hx0).mpr
    have hh := mul_le_mul_of_nonneg_left hd' (show 0≤24*w by positivity)
    nlinarith only [hh]
  have hnn : 0≤4*(4*(x+e)*a+c+2*(x+e)*b+6*e)/(x-e)^2 := by positivity
  calc
    _ ≤ A*(5*x)*(96*w/x) := mul_le_mul (mul_le_mul_of_nonneg_left ho hA) hf hnn (by positivity)
    _ = 480*A*w := by field_simp; ring
    _ ≤ 512*A*w := by nlinarith only [mul_nonneg hA hw]

end OrdinaryBinnedErrorBudget

end

end OAI
