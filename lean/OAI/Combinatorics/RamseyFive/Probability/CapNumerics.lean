import Mathlib

namespace OAI

namespace SharpRamseyFive.ReverseCap
lemma ambient_tail (u s q h : ℝ) (hu : 0 < u) (hs : 0 < s) (hq : 0 < q)
    (hh : 20*q*Real.log (u/s) ≤ h) :
    u*Real.exp (-h/(20*q)) ≤ s := by
  have hp : 0 < 20*q := by positivity
  have he : -h/(20*q) ≤ -Real.log (u/s) := by
    have hh' : Real.log (u/s) ≤ h/(20*q) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
    simpa only [neg_div] using neg_le_neg hh'
  calc
    _ ≤ u*Real.exp (-Real.log (u/s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hu.le
    _ = s := by rw [Real.exp_neg,Real.exp_log (div_pos hu hs)]; field_simp

lemma captured_cap_budget (G x c a s u q h : ℝ)
    (hG : 0 ≤ G) (hx : 0 < x) (hc : 0 < c) (ha : 0 < a)
    (hs : 0 < s) (hu : 0 < u) (hq : 0 < q)
    (hcapture : c*x ≤ a) (hproduct : s*x ≤ 16*G)
    (hh : 20*q*Real.log (u/s) ≤ h) :
    16*G/a+u*Real.exp (-h/(20*q)) ≤ ((320/c+320)*G/x)/20 := by
  have ht := ambient_tail u s q h hu hs hq hh
  have hs' : s ≤ 16*G/x := (le_div_iff₀ hx).mpr hproduct
  have ha' : 16*G/a ≤ 16*G/(c*x) :=
    (div_le_div_iff₀ ha (mul_pos hc hx)).mpr
      (mul_le_mul_of_nonneg_left hcapture (by positivity))
  calc
    _ ≤ 16*G/(c*x)+16*G/x := add_le_add ha' (ht.trans hs')
    _ = _ := by field_simp; ring

lemma rejection_from_capture (e x c a s q : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hcapture : c*x ≤ a) (hsparse : 1000*q*e ≤ c*s*x) :
    (5*q/a)*e ≤ s/200 := by
  have hc := mul_le_mul_of_nonneg_left hcapture hs
  have hh : 1000*q*e ≤ s*a := hsparse.trans (by nlinarith)
  calc
    _ = (5*q*e)/a := by ring
    _ ≤ s/200 := (div_le_iff₀ ha).mpr (by nlinarith)

lemma density_half (e s x c q : ℝ) (he : 0 ≤ e) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hq : 0 < q) (hc : c ≤ 1) (hsparse : 1000*q*e ≤ c*s*x) :
    e ≤ s*x/(2*q) := by
  have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hs hx)
  have hg : 0 ≤ q*e := mul_nonneg hq.le he
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*q)).mpr
  nlinarith

end SharpRamseyFive.ReverseCap

end OAI
