import OAI.NumberTheory.CubicMoment.Estimates.DispersionMixedAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeMajorant

namespace OAI

/-! The actual correction model and mixed term in the positive square.
Only its first term is enlarged by the square-divisor majorant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma correction_model_square {a : Eisenstein} (ha : primary a) (w : ℝ) (s : ℂ) :
    (idealMoebius a:ℝ)^2*w*
      ‖(cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s‖^2 =
    (cStar^2*‖s‖^2)*((idealMoebius a:ℝ)^2*w*norm a^(-1/3:ℝ)) := by
  by_cases hsf : Squarefree a
  · have hp : (norm a^(-1/6:ℝ))^2 = norm a^(-1/3:ℝ) := by
      rw [←Real.rpow_natCast (norm a^(-1/6:ℝ)) 2,←Real.rpow_mul (norm_nonneg a)]
      norm_num
    rw [idealMoebius_sq,ite_eq_left hsf]
    simp only [norm_mul,norm_star,norm_gauss ha,ite_eq_left hsf,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos cStar_pos,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _),mul_one,one_mul,mul_pow,hp]
    ring
  · rw [idealMoebius_sq,ite_eq_right hsf]
    simp

lemma correction_mixed_real (a : Eisenstein) (w : ℝ) (s f : ℂ) :
    (idealMoebius a:ℝ)^2*w*
      (star f*((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s)).re =
    ((cStar:ℂ)*star s*((idealMoebius a:ℂ)^2*(w:ℂ)*gauss a*
      ((norm a^(-1/6:ℝ):ℝ):ℂ)*f)).re := by
  calc
    _ = ((((idealMoebius a:ℝ)^2*w:ℝ):ℂ)*
        (star f*((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*s))).re := by
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    _ = (star ((cStar:ℂ)*star s*((idealMoebius a:ℂ)^2*(w:ℂ)*gauss a*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)*f))).re := by
      congr 1
      simp only [star_mul,star_pow,star_star]
      push_cast
      simp; ring
    _ = _ := by rfl

theorem corrected_dispersion_finite_majorant (A C B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (β : Eisenstein → ℂ) (u : ℝ) :
    (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤
      (∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖dispersionPolynomial B β u a‖^2)-
      2*((cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)).re+
      (cStar^2*‖dispersionModel B β u‖^2)*
        ∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ) := by
  have hh := corrected_squarefree_majorant A C hC h1 W hW
    (dispersionPolynomial B β u)
    (fun a => (cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u)
  change (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤ _ at hh
  apply hh.trans_eq
  have hm : (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*
      ‖(cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u‖^2) =
      (cStar^2*‖dispersionModel B β u‖^2)*
        ∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a ha => correction_model_square (hA a ha) _ _)
  have hx : (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*
      (star (dispersionPolynomial B β u a)*
        ((cStar:ℂ)*star (gauss a)*((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionModel B β u)).re) =
      ((cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)).re := by
    rw [Finset.mul_sum,Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _ => correction_mixed_real a _ _ _)
  rw [hm,hx]


/-- The three genuine model terms cancel after the positive and mixed
terms have each been identified with the same squarefree mass. -/
theorem corrected_dispersion_finite_error (A C B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (β : Eisenstein → ℂ) (u E₁ E₂ : ℝ)
    (hpositive : |(∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*
        ‖dispersionPolynomial B β u a‖^2)-
      (cStar^2*‖dispersionModel B β u‖^2)*
        (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ))| ≤ E₁)
    (hmixed : ‖(cStar:ℂ)*star (dispersionModel B β u)*
        (∑ a ∈ A, (idealMoebius a:ℂ)^2*(W a:ℂ)*gauss a*
          ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial B β u a)-
      (((cStar^2*‖dispersionModel B β u‖^2)*
        (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*norm a^(-1/3:ℝ)):ℝ):ℂ)‖ ≤ E₂) :
    (∑ a ∈ A, (idealMoebius a:ℝ)^2*W a*‖correctedDispersionPolynomial B β u a‖^2) ≤
      E₁+2*E₂ := by
  apply (corrected_dispersion_finite_majorant A C B hA hC h1 W hW β u).trans
  have hp := (abs_le.mp hpositive).2
  have hm := (abs_le.mp ((Complex.abs_re_le_norm _).trans hmixed)).1
  simp only [Complex.sub_re,Complex.ofReal_re] at hm
  linarith

end CubicFirstMoment

end

end OAI
