import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorImaginaryProjection

namespace OAI

/-! Three inequalities for the forward matrix on whole rays. -/

namespace DefocusingNLS.ExteriorCertificate
open Polynomial

noncomputable def exteriorForm (b Z : ℝ) (i j : Fin 2) : ℂ :=
  forwardFormEntry 5 (Complex.I*(Z : ℂ))
    (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5) i j

private theorem form_eval_re (z₀ : ℤ) (b Z : ℝ) (i j : Fin 2) :
    ((formPolynomial z₀ b i j).eval ((Z-(z₀ : ℝ)/100000000 : ℝ) : ℂ)).re =
      (100000000 : ℝ)^11*(exteriorForm b Z i j).re := by
  rw [formPolynomial_eval, show (z₀ : ℝ)/100000000+(Z-(z₀ : ℝ)/100000000)=Z by ring]
  change (((100000000 : ℝ)^11 : ℂ)*exteriorForm b Z i j).re = _
  norm_num [Complex.mul_re,Complex.mul_im]

private theorem form_eval_im (z₀ : ℤ) (b Z : ℝ) (i j : Fin 2) :
    ((formPolynomial z₀ b i j).eval ((Z-(z₀ : ℝ)/100000000 : ℝ) : ℂ)).im =
      (100000000 : ℝ)^11*(exteriorForm b Z i j).im := by
  rw [formPolynomial_eval, show (z₀ : ℝ)/100000000+(Z-(z₀ : ℝ)/100000000)=Z by ring]
  change (((100000000 : ℝ)^11 : ℂ)*exteriorForm b Z i j).im = _
  norm_num [Complex.mul_re,Complex.mul_im]

private theorem margin_eval_re (z₀ : ℤ) (Z : ℝ) :
    ((marginPolynomial z₀).eval ((Z-(z₀ : ℝ)/100000000 : ℝ) : ℂ)).re =
      (100000000 : ℝ)^11*(1130*Z) := by
  norm_num [marginPolynomial,Complex.mul_re,Complex.mul_im]
  ring

theorem exterior_diagonal_positive (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 2704/1000 ≤ Z) :
    0 < (exteriorForm b Z 1 1).re := by
  have hv : 0 ≤ Z-(270400000 : ℝ)/100000000 := by norm_num; linarith
  have h := diagonal_polynomial_positive b (Z-270400000/100000000) hb hv
  have he := form_eval_re 270400000 b Z 1 1
  norm_num at h he
  rw [he] at h
  linarith

theorem exterior_real_bound (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 2704/1000 ≤ Z) :
    0 < (43/1000 : ℝ)*(exteriorForm b Z 1 1).re+
      (exteriorForm b Z 1 0).re-1130*Z := by
  have hv : 0 ≤ Z-(270400000 : ℝ)/100000000 := by norm_num; linarith
  have h := real_bound_polynomial_positive b (Z-270400000/100000000) hb hv
  simp only [realBoundPolynomial,eval_add,eval_mul,eval_C,eval_sub,
    realProjection_eval,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im] at h
  norm_num at h
  have hd := form_eval_re 270400000 b Z 1 1
  have hc := form_eval_re 270400000 b Z 1 0
  have hm := margin_eval_re 270400000 Z
  norm_num at hd hc hm
  rw [hd,hc,hm] at h
  nlinarith

theorem exterior_imaginary_bound (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 3 ≤ Z) :
    0 < -(exteriorForm b Z 1 0).im-1130*Z := by
  have hv : 0 ≤ Z-(300000000 : ℝ)/100000000 := by norm_num; linarith
  have h := imaginary_bound_polynomial_positive b (Z-300000000/100000000) hb hv
  simp only [imaginaryBoundPolynomial,eval_sub,negImagProjection_eval,
    Complex.sub_re,Complex.neg_re,Complex.ofReal_re] at h
  have hc := form_eval_im 300000000 b Z 1 0
  have hm := margin_eval_re 300000000 Z
  norm_num at h hc hm
  rw [hc,hm] at h
  nlinarith

end DefocusingNLS.ExteriorCertificate

end OAI
