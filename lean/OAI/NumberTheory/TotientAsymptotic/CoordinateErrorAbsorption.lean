import OAI.NumberTheory.TotientAsymptotic.CoordinateDeviationExponent

namespace OAI

/-! Scalar estimates for the four contributions to the deviation count. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_power_error {u b δ : ℝ} (hu : 0 < u) (hb : 0 ≤ b)
    (he : Real.log u=b) (hδ : δ ≤ 1/4) :
    u^(-5/4:ℝ) ≤ u⁻¹*Real.exp (-δ*b) := by
  have hlog := Real.exp_log hu
  rw [Real.rpow_def_of_pos hu,he,← hlog,← Real.exp_neg,← Real.exp_add,he]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hδ hb]

lemma coordinate_square_error {b δ D : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hδ : δ ≤ 1) :
    (2+D*b)*Real.exp (-3*b) ≤ (2+D)*Real.exp (-(1+δ)*b) := by
  have hexp1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  have hexpb : b ≤ Real.exp b := by linarith only [Real.add_one_le_exp b]
  have hp : 2+D*b ≤ (2+D)*Real.exp b := by
    nlinarith only [mul_le_mul_of_nonneg_left hexpb hD,hexp1]
  calc
    _ ≤ ((2+D)*Real.exp b)*Real.exp (-3*b) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (2+D)*Real.exp (-2*b) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
      nlinarith only [mul_le_mul_of_nonneg_right hδ hb]

lemma coordinate_power_contribution {C x : ℝ} (hC : 0 ≤ C) (hx : 1 < x)
    {δ : ℝ} (hb : 0 ≤ B x) (hδ : δ ≤ 1/4) :
    C*x*(Real.log x)^(-5/4:ℝ) ≤ C*(x/Real.log x*Real.exp (-δ*B x)) := by
  have hh := coordinate_power_error (Real.log_pos hx) hb (show Real.log (Real.log x)=B x from rfl) hδ
  have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ C*x by positivity)
  simpa only [div_eq_mul_inv,mul_assoc] using hp

lemma coordinate_square_contribution {D x b δ r : ℝ} (hD : 0 ≤ D) (hx : 1 < x)
    (hb : 0 ≤ b) (he : b=B x) (hδ : δ ≤ 1) (_hr : 0 ≤ r)
    (hrecip : 1/r ≤ Real.exp (-3*b)) :
    (2*x+D*x*b)/r ≤ (2+D)*(x/Real.log x*Real.exp (-δ*b)) := by
  have hs := coordinate_square_error hD hb hδ
  calc
    _ = x*(2+D*b)*(1/r) := by ring
    _ ≤ x*((2+D*b)*Real.exp (-3*b)) := by
      have hh := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ x*(2+D*b) by positivity)
      simpa only [mul_assoc] using hh
    _ ≤ x*((2+D)*Real.exp (-(1+δ)*b)) :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    _ = _ := by
      rw [log_normalized_exponential hx]
      rw [← he]
      have hh : -δ*b-b=-(1+δ)*b := by ring
      rw [hh]
      ring

end TotientAsymptotic

end

end OAI
