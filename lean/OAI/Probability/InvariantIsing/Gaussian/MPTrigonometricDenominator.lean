import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace OAI

/-! Elementary positive-denominator identities for the MP density integral. -/
noncomputable section
open Real Set
namespace InvariantIsing

lemma mp_cos_denominator_pos {a b : ℝ} (hab : |b| < a) (x : ℝ) : 0 < a+b*cos x := by
  have hbc : |b*cos x| ≤ |b| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg b) (abs_cos_le_one x)
  have h := neg_abs_le (b*cos x)
  linarith

lemma mp_discriminant_pos {a b : ℝ} (hab : |b| < a) : 0 < a^2-b^2 := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hs := (sq_lt_sq₀ (abs_nonneg b) ha.le).mpr hab
  rw [sq_abs] at hs
  linarith

lemma mp_cos_fraction_identity {a b : ℝ} (hab : |b| < a) (x : ℝ) :
    1-((a*cos x+b)/(a+b*cos x))^2 =
      (a^2-b^2)*(sin x)^2/(a+b*cos x)^2 := by
  have hd := (mp_cos_denominator_pos hab x).ne'
  apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
  rw [div_pow,sub_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  linear_combination -(a^2-b^2)*(sin_sq_add_cos_sq x)

lemma mp_cos_fraction_mem_Ioo {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    (a*cos x+b)/(a+b*cos x) ∈ Ioo (-1) 1 := by
  have hi := mp_cos_fraction_identity hab x
  have hs := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hp : 0 < (a^2-b^2)*(sin x)^2/(a+b*cos x)^2 := by
    exact div_pos (mul_pos (mp_discriminant_pos hab) (sq_pos_of_pos hs))
      (sq_pos_of_pos (mp_cos_denominator_pos hab x))
  constructor <;> nlinarith

lemma mp_cos_fraction_hasDerivAt {a b : ℝ} (hab : |b| < a) (x : ℝ) :
    HasDerivAt (fun y => (a*cos y+b)/(a+b*cos y))
      (-(a^2-b^2)*sin x/(a+b*cos x)^2) x := by
  have h := (((hasDerivAt_cos x).const_mul a).add_const b).div
    ((hasDerivAt_cos x).const_mul b |>.const_add a) (mp_cos_denominator_pos hab x).ne'
  convert h using 1
  ring

end InvariantIsing

end

end OAI
