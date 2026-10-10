import Mathlib

namespace OAI

/-! Quasilinear Residual Algebra. -/

section

 
namespace HigherJet
lemma affine_residual_bound {c r A B D L : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hA : A ≤ c) (hB : B ≤ c*(c+r)) (hD : D ≤ c^3*r) (hL : L ≤ A+B+D) :
    L ≤ (2*c+c^2+c^3)*(1+r) := by
  have h1 : 0 ≤ c*r := mul_nonneg hc hr
  have h2 : 0 ≤ c^2*r := mul_nonneg (sq_nonneg c) hr
  have h3 : 0 ≤ c+c^3 := by positivity
  nlinarith only [hA,hB,hD,hL,h1,h2,h3]

lemma four_monomial_bound {a b c d r s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (_hr : 0 ≤ r) (hs : 0 ≤ s) :
    a+b*r+c*r^2+d*s ≤ (a+b+c+d)*(1+r^2+s) := by
  have h0 : 1 ≤ 1+r^2+s := by nlinarith only [sq_nonneg r,hs]
  have h1 : r ≤ 1+r^2+s := by nlinarith only [sq_nonneg (r-1),hs]
  have h2 : r^2 ≤ 1+r^2+s := by linarith only [hs]
  have h3 : s ≤ 1+r^2+s := by nlinarith only [sq_nonneg r]
  have a0 := mul_le_mul_of_nonneg_left h0 ha
  have a1 := mul_le_mul_of_nonneg_left h1 hb
  have a2 := mul_le_mul_of_nonneg_left h2 hc
  have a3 := mul_le_mul_of_nonneg_left h3 hd
  nlinarith only [a0,a1,a2,a3]

lemma quadratic_residual_bound {c r s A B D L : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : A ≤ c) (hB : B ≤ c^2*(r+s+(c+r)^2))
    (hD : D ≤ c*(2*c^2*s+c^2*(r+c^2)*r)) (hL : L ≤ A+B+D) :
    L ≤ (c+3*c^2+5*c^3+c^4+c^5)*(1+r^2+s) := by
  have h := four_monomial_bound (a := c+c^4) (b := c^2+2*c^3+c^5)
    (c := c^2+c^3) (d := c^2+2*c^3) (by positivity) (by positivity) (by positivity)
    (by positivity) hr hs
  nlinarith only [hA,hB,hD,hL,h]
end HigherJet

end

end OAI
