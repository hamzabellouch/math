import Mathlib
import OAI.Combinatorics.KMedian.Analysis.ScalarTransfer

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

private theorem reciprocal_quadratic {c t w γ : ℝ} (ht : 0 < t)
    (hc : γ^2 ≤ (8/5)*c) : γ*w ≤ c/t+(2/5)*w^2*t := by
  have hs := sq_nonneg ((4/5)*w*t-γ)
  have hpoly : γ*w*t ≤ c+(2/5)*w^2*t^2 := by nlinarith only [hs, hc]
  calc
    γ*w ≤ (c+(2/5)*w^2*t^2)/t := (le_div_iff₀ ht).mpr hpoly
    _ = c/t+(2/5)*w^2*t := by field_simp

private theorem first_gap_identity {p x w r : ℝ} (hr : r ≠ 0)
    (hx : 1+x ≠ 0) (hd : 1-p*r ≠ 0) (s : Bool) :
    c p s*(1-p)/(1-p*r) -
      (2*x*(1-p)/(1+x)-2*x*p+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) =
    c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-(2-bit s)*p*w+(2/5)*p^2*w^2+
      p*(c p s*(1-p)/((1-p*r)/r)+(2/5)*w^2*((1-p*r)/r)) := by
  field_simp [hr, hx, hd]
  ring

theorem first_scalar {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
    (hr0 : 0 < r) (hr : r ≤ 1)
    (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
    (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
    m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r) := by
  have hxden : 0 < 1+x := by linarith
  have hpr := mul_le_mul hp hr hr0.le (by norm_num : (0:ℝ) ≤ 1/2)
  have hden : 0 < 1-p*r := by linarith
  have ht : 0 < (1-p*r)/r := div_pos hden hr0
  have hm' : m = 2*x*(1-p)/(1+x)-2*x*p := by
    have he : m+2*x*p = 2*x*(1-p)/(1+x) := (eq_div_iff hxden.ne').mpr (by nlinarith only [hm])
    linarith
  have hgap := first_gap_identity (w := w) (ne_of_gt hr0) hxden.ne' hden.ne' s
  rw [←hm'] at hgap
  have hX0 : 0 ≤ 1-x := sub_nonneg.mpr hx
  have hgam : (if s then 31/50 else 22/25 : ℝ)^2 ≤ (8/5)*(c p s*(1-p)) := by
    cases s <;> norm_num [c, bit] <;> nlinarith [sq_nonneg (p-1/2)]
  have hagm := reciprocal_quadratic (w := w) ht hgam
  have hagmp := mul_le_mul_of_nonneg_left hagm hp0
  have hrest : 0 ≤ c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-
      (2-bit s)*p*w+(2/5)*p^2*w^2+p*((if s then 31/50 else 22/25)*w) := by
    cases s
    · norm_num [c, bit]
      have hsum : w+(1-x) ≤ 2 := by linarith
      have hsum0 : 0 ≤ w+(1-x) := by linarith
      have hpp := mul_le_mul hp hsum hsum0 (by norm_num : (0:ℝ) ≤ 1/2)
      have hquad := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hw))
        (show 0 ≤ 28/25-(2/5)*p*(w+(1-x)) by linarith)
      have hnonneg : 0 ≤ (1-x)*T1 p x/(1+x) := div_nonneg (mul_nonneg hX0 hT1) hxden.le
      have hid : (1-x)*T1 p x/(1+x) =
          (1-p)-2*x*(1-p)/(1+x)-(28/25)*p*(1-x)+(2/5)*p^2*(1-x)^2 := by
        unfold T1
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hquad]
    · norm_num [c, bit]
      have hlin := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 19/50) hp0) (sub_nonneg.mpr hw)
      have hquad : 0 ≤ (2/5)*p^2*w^2 := by positivity
      have hnonneg : 0 ≤ T2 p x/(1+x) := div_nonneg hT2 hxden.le
      have hid : T2 p x/(1+x) = (1-p)^2-2*x*(1-p)/(1+x)+p*x-(19/50)*p*(1-x) := by
        unfold T2
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hlin, hquad]
  have hgd : 0 ≤ c p s*(1-p)/(1-p*r) -
      (m+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) := by
    rw [hgap]
    linarith only [hagmp, hrest]
  have hresult := sub_nonneg.mp hgd
  convert hresult using 1; ring

noncomputable def stdB (p x w : ℝ) (s : Bool) : ℝ := (2-bit s)*p*(x+w)
noncomputable def stdL (p a x w r : ℝ) (s : Bool) : ℝ :=
  (c p s-(a-1-2*x*p)-stdB p x w s)*r+(2/5)*p*w^2
noncomputable def stdM (p a w r : ℝ) (s : Bool) : ℝ :=
  (1-r)*(a+2*p*w)+c p s*p*r
noncomputable def stdK (p k x w r : ℝ) (s : Bool) : ℝ :=
  N p k s-stdB p x w s*r+(8/5)*p*w^2

private theorem Q0_difference (p a k w W : ℝ) (s : Bool) :
    Q0 p a k w s-Q0 p a k W s =
      p*hh s*((w-uZero s)^2-(W-uZero s)^2) := by
  cases s <;> norm_num [Q0, hh, uZero, d] <;> ring

theorem Q0_minimum {p a k x w : ℝ} (hp0 : 0 ≤ p)
    (hw : w ≤ 1-x) (s : Bool) :
    Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s ≤ Q0 p a k w s := by
  have hsq : ((if s then uZero s else min (1-x) (uZero s))-uZero s)^2 ≤ (w-uZero s)^2 := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hcut : 1-x ≤ uZero false
      · rw [min_eq_left hcut]
        nlinarith only [hw, hcut, sq_nonneg (w-(1-x))]
      · rw [min_eq_right (le_of_not_ge hcut), sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
    · simpa only [↓reduceIte, sub_self, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (w-uZero true)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hp := mul_nonneg (mul_nonneg hp0 hh0) (sub_nonneg.mpr hsq)
  rw [←Q0_difference] at hp
  linarith only [hp]

private theorem linear_gap_identity (p a k x w r : ℝ) (s : Bool) :
    stdK p k x w r s-d s*(stdM p a w r s-stdL p a x w r s) =
      (1-r)*Q0 p a k w s+r*(Q1 p a k x s+hh s*p*(w-uOne s)^2) := by
  dsimp only [stdK, stdM, stdL, stdB, Q0, Q1, N, c, ell, uOne, hh]
  cases s <;> norm_num [bit, d] <;> ring

theorem linear_scalar {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
    (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
    (hQ1 : 0 ≤ Q1 p a k x s) :
    d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s := by
  have hzero := hQ0.trans (Q0_minimum hp0 hw s)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hone : 0 ≤ Q1 p a k x s+hh s*p*(w-uOne s)^2 := by positivity
  have hn := add_nonneg (mul_nonneg (sub_nonneg.mpr hr) hzero) (mul_nonneg hr0 hone)
  rw [←linear_gap_identity] at hn
  exact sub_nonneg.mp hn

theorem Y_le_base {p k x w : ℝ} (hp0 : 0 ≤ p) (s : Bool) :
    Y p k x s ≤ N p k s+(8/5)*p*w^2-stdB p x w s := by
  have hn : 0 ≤ (8/5)*p*(w-5*(2-bit s)/16)^2 := by positivity
  have hid : N p k s+(8/5)*p*w^2-stdB p x w s-Y p k x s =
      (8/5)*p*(w-5*(2-bit s)/16)^2 := by unfold Y stdB; ring
  linarith only [hid, hn]

theorem Yprime_le_base {p k x w : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hx : 1-x ≤ 1/2) : Yprime p k x ≤ 1-k+(8/5)*p*w^2-stdB p x w false := by
  have hb : 0 ≤ 2-(8/5)*(w+(1-x)) := by linarith
  have hn := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hw)) hb
  unfold Yprime stdB bit
  norm_num
  nlinarith only [hn]

end MetricKMedian.ScalarTransfer


end
end

end OAI
