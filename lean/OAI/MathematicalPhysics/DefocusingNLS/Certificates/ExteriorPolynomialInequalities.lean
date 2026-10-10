import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorPositiveEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorPolynomialDegree

namespace OAI

/-! The first two exterior certificate inequalities for the coherent polynomial family. -/

open Polynomial
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure
open BoundaryCertificate (constant_sound)

noncomputable def marginPolynomial (z₀ : ℤ) : Polynomial ℂ :=
  C ((1130*100000000^10*z₀ : ℤ) : ℂ)+X*C ((1130*100000000^11 : ℤ) : ℂ)

theorem margin_sound (z₀ : ℤ) :
    EnclosesPolynomial (determinantMargin z₀) (marginPolynomial z₀) := by
  refine ⟨((1130*100000000^10*z₀ : ℤ) : ℂ),
    C ((1130*100000000^11 : ℤ) : ℂ),?_,constant_sound _,rfl⟩
  simp [Encloses,BoundaryCertificate.coefficient,GaussianInt.toComplex_def']

noncomputable def realBoundPolynomial (b : ℝ) : Polynomial ℂ :=
  C 43*realProjection (formPolynomial 270400000 b 1 1)+
    C 1000*(realProjection (formPolynomial 270400000 b 1 0)-marginPolynomial 270400000)

theorem realBound_sound (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    EnclosesPolynomial realBound (realBoundPolynomial b) := by
  have hd := realCoefficients_sound (diagonal_sound 270400000 b hb) 11
    ((form_degree 270400000 b 1).trans_lt (by decide))
  have hc := realCoefficients_sound (lowerOffDiagonal_sound 270400000 b hb) 11
    ((form_degree 270400000 b 0).trans_lt (by decide))
  exact addPolynomial_sound (mulPolynomial_sound (constant_sound 43) hd)
    (mulPolynomial_sound (constant_sound 1000) (subPolynomial_sound hc (margin_sound _)))

theorem margin_degree (z₀ : ℤ) : (marginPolynomial z₀).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C _).le.trans (by omega)
  · exact natDegree_mul_le.trans (by simp)

theorem realBoundPolynomial_degree (b : ℝ) : (realBoundPolynomial b).natDegree ≤ 10 := by
  have hd : (realProjection (formPolynomial 270400000 b 1 1)).natDegree ≤ 10 :=
    (realProjection_degree _).trans (form_degree 270400000 b 1)
  have hc : (realProjection (formPolynomial 270400000 b 1 0)).natDegree ≤ 10 :=
    (realProjection_degree _).trans ((form_degree 270400000 b 0).trans (by decide))
  apply natDegree_add_le_of_degree_le ((natDegree_C_mul_le 43 _).trans hd)
  exact (natDegree_C_mul_le 1000 _).trans ((natDegree_sub_le _ _).trans
    (max_le hc ((margin_degree _).trans (by decide))))

theorem diagonal_polynomial_positive (b v : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hv : 0 ≤ v) :
    0 < ((formPolynomial 270400000 b 1 1).eval (v : ℂ)).re := by
  have hd := realCoefficients_sound (diagonal_sound 270400000 b hb) 11
    ((form_degree 270400000 b 1).trans_lt (by decide))
  have h := positive_eval_of_positiveCoefficients
    (realCoefficients (diagonal 270400000) 11)
    (realProjection (formPolynomial 270400000 b 1 1)) 11 (by decide)
    (by simp [realCoefficients]) diagonal_coefficients_positive hd
    (((realProjection_degree _).trans (form_degree 270400000 b 1)).trans_lt (by decide)) v hv
  simpa only [realProjection_eval,Complex.ofReal_re] using h

theorem real_bound_polynomial_positive (b v : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hv : 0 ≤ v) :
    0 < ((realBoundPolynomial b).eval (v : ℂ)).re := by
  exact positive_eval_of_positiveCoefficients realBound (realBoundPolynomial b) 11
    (by decide) (by decide +kernel) real_bound_coefficients_positive
    (realBound_sound b hb) ((realBoundPolynomial_degree b).trans_lt (by decide)) v hv

end DefocusingNLS.ExteriorCertificate

end OAI
