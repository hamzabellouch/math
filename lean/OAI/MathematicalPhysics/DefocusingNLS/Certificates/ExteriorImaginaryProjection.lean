import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorImaginaryDegree
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorPolynomialInequalities

namespace OAI

/-! The final coefficient projection and the third exterior polynomial inequality. -/

open Polynomial
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure

attribute [local irreducible] state polynomialState

private theorem negImagPart_sound {a : GaussianEnclosure} {z : ℂ} (ha : a.Encloses z) :
    (BoundaryCertificate.coefficient (-a.center.im) 0 a.error).Encloses (-z.im : ℂ) := by
  have h := (Complex.abs_im_le_norm (z-(a.center : ℂ))).trans ha
  rw [Complex.sub_im, ← GaussianInt.intCast_im] at h
  change ‖(-z.im : ℂ)-GaussianInt.toComplex ⟨-a.center.im,0⟩‖ ≤ _
  have hc : GaussianInt.toComplex ⟨-a.center.im,0⟩ = ((-(a.center.im : ℝ)) : ℂ) := by
    rw [GaussianInt.toComplex_def',Int.cast_zero,zero_mul,add_zero]
    norm_cast
  rw [hc, ← Complex.ofReal_neg, ← Complex.ofReal_neg, ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  simpa only [BoundaryCertificate.coefficient,neg_sub_neg,abs_sub_comm] using h

theorem negImagCoefficients_sound {as : BoundaryCertificate.EnclosurePolynomial}
    {p : Polynomial ℂ} (hp : EnclosesPolynomial as p) (N : ℕ)
    (hdeg : (negImagProjection p).natDegree < N) :
    EnclosesPolynomial (negImagCoefficients as N) (negImagProjection p) := by
  apply enclosesPolynomial_of_coefficients
  intro n
  by_cases hn : n < N
  · rw [coeff_negImagProjection]
    simpa [negImagCoefficients,List.getElem?_map,hn,BoundaryCertificate.coefficient] using
      negImagPart_sound (coefficient_sound hp n)
  · have hz := coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_lt hn))
    rw [hz]
    simpa [negImagCoefficients,List.getElem?_map,hn] using zero_sound

noncomputable def imaginaryBoundPolynomial (b : ℝ) : Polynomial ℂ :=
  negImagProjection (formPolynomial 300000000 b 1 0)-marginPolynomial 300000000

theorem imaginaryBound_sound (b : ℝ) (hb : |100000000*b-33477607| ≤ 2) :
    EnclosesPolynomial imaginaryBound (imaginaryBoundPolynomial b) :=
  subPolynomial_sound (negImagCoefficients_sound (lowerOffDiagonal_sound _ b hb) 9
    ((imaginary_form_degree _ b).trans_lt (by decide))) (margin_sound _)

theorem imaginaryBoundPolynomial_degree (b : ℝ) :
    (imaginaryBoundPolynomial b).natDegree ≤ 8 :=
  (natDegree_sub_le _ _).trans (max_le (imaginary_form_degree _ b)
    ((margin_degree _).trans (by decide)))

theorem imaginary_bound_polynomial_positive (b v : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hv : 0 ≤ v) :
    0 < ((imaginaryBoundPolynomial b).eval (v : ℂ)).re :=
  positive_eval_of_positiveCoefficients imaginaryBound (imaginaryBoundPolynomial b) 9
    (by decide) (by decide +kernel) imaginary_bound_coefficients_positive
    (imaginaryBound_sound b hb) ((imaginaryBoundPolynomial_degree b).trans_lt (by decide)) v hv

end DefocusingNLS.ExteriorCertificate

end OAI
