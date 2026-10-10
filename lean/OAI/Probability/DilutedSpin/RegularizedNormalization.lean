import OAI.Probability.DilutedSpin.InsertionPoint

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma regularized_ratio_bound {B d e t : ℝ} (hB : 0 ≤ B) (hd : |d|<1)
    (ht0 : 0 ≤ t) (ht : t<1)
    (hl : Real.exp (-B)*(1+d)≤1+e) (hu : 1+e≤Real.exp B*(1+d)) :
    |Real.log ((1+t*e)/(1+t*d))|≤B := by
  have hd' : -1<d := (abs_lt.mp hd).1
  have hden : 0<1+t*d := by nlinarith
  have hexpl : Real.exp (-B)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB)
  have hexpu : 1≤Real.exp B := Real.one_le_exp_iff.mpr hB
  have htl : Real.exp (-B)*(1+t*d)≤1+t*e := by
    have hh := mul_nonneg (sub_nonneg.mpr hexpl) (sub_nonneg.mpr ht.le)
    nlinarith [mul_le_mul_of_nonneg_left hl ht0]
  have htu : 1+t*e≤Real.exp B*(1+t*d) := by
    have hh := mul_nonneg (sub_nonneg.mpr hexpu) (sub_nonneg.mpr ht.le)
    nlinarith [mul_le_mul_of_nonneg_left hu ht0]
  have hlow : Real.exp (-B)≤(1+t*e)/(1+t*d) := (le_div_iff₀ hden).mpr htl
  have hupp : (1+t*e)/(1+t*d)≤Real.exp B := (div_le_iff₀ hden).mpr htu
  have hr : 0<(1+t*e)/(1+t*d) := (Real.exp_pos _).trans_le hlow
  apply abs_le.mpr
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-B)) hlow
  · simpa only [Real.log_exp] using Real.log_le_log hr hupp

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

lemma factor_expect (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (hfac : ∀ s,Real.exp (θ s)=a*(1+D s)) :
    P.expect (fun s => Real.exp (θ s))=a*(1+P.expect D) := by
  simp_rw [hfac]
  rw [expect_mul_left,expect_add,expect_const]

lemma normalized_factor_bounds (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : Ω) {B : ℝ} (hθ : ∀ s,|θ s|≤B) :
    Real.exp (-2*B)*(1+D s₀)≤1+P.expect D ∧
      1+P.expect D≤Real.exp (2*B)*(1+D s₀) := by
  have hl : P.expect (fun _ => Real.exp (-2*B)*Real.exp (θ s₀))≤
      P.expect (fun s => Real.exp (θ s)) := by
    apply P.expect_mono
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := abs_le.mp (hθ s)
    have h2 := abs_le.mp (hθ s₀)
    linarith
  have hu : P.expect (fun s => Real.exp (θ s))≤
      P.expect (fun _ => Real.exp (2*B)*Real.exp (θ s₀)) := by
    apply P.expect_mono
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := abs_le.mp (hθ s)
    have h2 := abs_le.mp (hθ s₀)
    linarith
  rw [expect_const,factor_expect P θ D a hfac,hfac s₀] at hl
  rw [expect_const,factor_expect P θ D a hfac,hfac s₀] at hu
  constructor
  · apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hl]
  · apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hu]

lemma normalized_factor_log_bound (P : FiniteLaw Ω) (θ D : Ω → ℝ) (a : ℝ)
    (ha : 0<a) (hfac : ∀ s,Real.exp (θ s)=a*(1+D s))
    (s₀ : Ω) (hD : |D s₀|<1) {B t : ℝ} (hB : 0 ≤ B)
    (hθ : ∀ s,|θ s|≤B) (ht0 : 0 ≤ t) (ht : t<1) :
    |Real.log ((1+t*P.expect D)/(1+t*D s₀))|≤2*B := by
  have hh := normalized_factor_bounds P θ D a ha hfac s₀ hθ
  exact regularized_ratio_bound (by positivity) hD ht0 ht
    (by simpa only [neg_mul] using hh.1) hh.2

end FiniteLaw
end DilutedSpinGlass

end

end OAI
