import OAI.Analysis.KadisonKastler.CornerAngleBound
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Normalized angles in nearly full corners -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_normalize_re (x y : H) :
    (inner ℂ x y).re=‖x‖*‖y‖*(inner ℂ (normalize x) (normalize y)).re := by
  calc
    _ = (inner ℂ (‖x‖ • normalize x) (‖y‖ • normalize y)).re := by
      rw [norm_smul_normalize,norm_smul_normalize]
    _ = _ := by
      change (inner ℂ ((‖x‖ : ℂ) • normalize x) ((‖y‖ : ℂ) • normalize y)).re=_
      rw [inner_smul_left,inner_smul_right]
      simp only [Complex.conj_ofReal,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      ring

omit [CompleteSpace H] in
theorem normalized_angle_lower (x y : H) (hx : x≠0) (hy : y≠0)
    (hnx : ‖x‖≤1) (hny : ‖y‖≤1)
    (hdet : 1/2 ≤ ‖x‖^2*‖y‖^2-(inner ℂ x y).re^2) :
    1/2 ≤ 1-(inner ℂ (normalize x) (normalize y)).re^2 := by
  let c := (inner ℂ (normalize x) (normalize y)).re
  let P := ‖x‖^2*‖y‖^2
  have hab : |c|≤1 := by
    exact (Complex.abs_re_le_norm _).trans (by
      simpa only [norm_normalize hx,norm_normalize hy,mul_one] using
        norm_inner_le_norm (normalize x) (normalize y))
  have hc : c^2≤1 := by nlinarith only [(sq_le_sq₀ (abs_nonneg c) (by norm_num : (0:ℝ)≤1)).mpr hab,sq_abs c]
  have hP : P≤1 := by
    have hxx : ‖x‖^2≤1 := by nlinarith only [norm_nonneg x,hnx]
    have hyy : ‖y‖^2≤1 := by nlinarith only [norm_nonneg y,hny]
    exact (mul_le_mul hxx hyy (sq_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have he : (inner ℂ x y).re^2=P*c^2 := by
    rw [inner_normalize_re]
    dsimp only [P,c]
    ring
  have hh := mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hc)
  change 1/2≤1-c^2
  change 1/2≤P-(inner ℂ x y).re^2 at hdet
  rw [he] at hdet
  nlinarith only [hh,hdet]

omit [CompleteSpace H] in
theorem normalized_angle_noncollinear (x y : H) (hx : x≠0) (_hy : y≠0)
    (hangle : 1/2 ≤ 1-(inner ℂ (normalize x) (normalize y)).re^2) :
    normalize y≠normalize x ∧ normalize y≠-normalize x := by
  have hself : inner ℂ (normalize x) (normalize x)=1 := by
    rw [inner_self_eq_norm_sq_to_K,norm_normalize hx]
    norm_num
  constructor
  · intro he
    rw [he,hself] at hangle
    norm_num at hangle
  · intro he
    rw [he,inner_neg_right,hself] at hangle
    norm_num at hangle

end

end KadisonKastler

end OAI
