import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorFormPolynomial

namespace OAI

/-! Real and negative-imaginary coefficient projection for the exterior checks. -/

open Polynomial
namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure

noncomputable def realProjection (p : Polynomial ℂ) : Polynomial ℂ :=
  C (1/2 : ℂ)*(p+conjugatePolynomial p)

noncomputable def negImagProjection (p : Polynomial ℂ) : Polynomial ℂ :=
  C (Complex.I/2)*(p-conjugatePolynomial p)

theorem coeff_realProjection (p : Polynomial ℂ) (n : ℕ) :
    (realProjection p).coeff n = ((p.coeff n).re : ℂ) := by
  simp only [realProjection,coeff_C_mul,coeff_add,coeff_conjugatePolynomial]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem coeff_negImagProjection (p : Polynomial ℂ) (n : ℕ) :
    (negImagProjection p).coeff n = (-((p.coeff n).im) : ℂ) := by
  simp only [negImagProjection,coeff_C_mul,coeff_sub,coeff_conjugatePolynomial]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem realProjection_degree (p : Polynomial ℂ) :
    (realProjection p).natDegree ≤ p.natDegree :=
  (natDegree_C_mul_le _ _).trans
    (natDegree_add_le_of_degree_le le_rfl (conjugatePolynomial_degree p))

theorem realProjection_eval (p : Polynomial ℂ) (v : ℝ) :
    (realProjection p).eval (v : ℂ) = ((p.eval (v : ℂ)).re : ℂ) := by
  simp only [realProjection,eval_mul,eval_C,eval_add,conjugatePolynomial_eval_real]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem negImagProjection_eval (p : Polynomial ℂ) (v : ℝ) :
    (negImagProjection p).eval (v : ℂ) = (-((p.eval (v : ℂ)).im) : ℂ) := by
  simp only [negImagProjection,eval_mul,eval_C,eval_sub,conjugatePolynomial_eval_real]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

theorem realCoefficients_sound {as : BoundaryCertificate.EnclosurePolynomial}
    {p : Polynomial ℂ} (hp : EnclosesPolynomial as p) (N : ℕ)
    (hdeg : p.natDegree < N) :
    EnclosesPolynomial (realCoefficients as N) (realProjection p) := by
  apply enclosesPolynomial_of_coefficients
  intro n
  rw [coeff_realProjection]
  by_cases hn : n < N
  · simpa [realCoefficients, List.getElem?_map, hn, BoundaryCertificate.coefficient] using
      realPart_sound (coefficient_sound hp n)
  · have hz := coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_lt hn))
    simpa [realCoefficients, List.getElem?_map, hn, hz] using zero_sound

end DefocusingNLS.ExteriorCertificate

end OAI
