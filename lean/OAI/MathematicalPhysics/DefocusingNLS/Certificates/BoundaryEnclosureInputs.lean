import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateSemantics

namespace OAI

/-! # Parameter-box inputs to the exact boundary enclosure -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

def inputReal (ell n : ℕ) : ℤ := 50000000 * ((ell : ℤ) + 2 * (n : ℤ)) - 3125000

noncomputable def inputS (Z : ℝ) : Polynomial ℂ := C (Complex.I * (100000000 * Z : ℝ))

noncomputable def inputT (ell n : ℕ) (b : ℝ) : Polynomial ℂ :=
  C ((inputReal ell n : ℂ) - Complex.I * (100000000 * b : ℝ)) +
    X * C (Complex.I * (100000000 : ℝ))

theorem inputS_sound (Z : ℝ) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    EnclosesPolynomial [coefficient 0 270506819 2] (inputS Z) := by
  refine ⟨Complex.I * (100000000 * Z : ℝ), 0, ?_, rfl, by simp [inputS]⟩
  change ‖Complex.I * (100000000 * Z : ℝ) -
    ((⟨0, 270506819⟩ : GaussianInt) : ℂ)‖ ≤ 2
  have he : Complex.I * (100000000 * Z : ℝ) -
      ((⟨0, 270506819⟩ : GaussianInt) : ℂ) =
      ((100000000 * Z - 270506819 : ℝ) : ℂ) * Complex.I := by
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact hZ

theorem inputT_sound (ell n : ℕ) (b : ℝ) (hb : |100000000 * b - 33477607| ≤ 2) :
    EnclosesPolynomial
      [coefficient (inputReal ell n) (-33477607) 2, coefficient 0 100000000 0]
      (inputT ell n b) := by
  refine ⟨(inputReal ell n : ℂ) - Complex.I * (100000000 * b : ℝ),
    C (Complex.I * (100000000 : ℝ)), ?_, ?_, rfl⟩
  · change ‖(inputReal ell n : ℂ) - Complex.I * (100000000 * b : ℝ) -
      ((⟨inputReal ell n, -33477607⟩ : GaussianInt) : ℂ)‖ ≤ 2
    have he : (inputReal ell n : ℂ) - Complex.I * (100000000 * b : ℝ) -
        ((⟨inputReal ell n, -33477607⟩ : GaussianInt) : ℂ) =
        ((100000000 * b - 33477607 : ℝ) : ℂ) * (-Complex.I) := by
      rw [GaussianInt.toComplex_def']
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_I, mul_one]
    exact hb
  · refine ⟨Complex.I * (100000000 : ℝ), 0, ?_, rfl, by simp⟩
    norm_num [Encloses, coefficient, GaussianInt.toComplex_def', mul_comm]

end DefocusingNLS.BoundaryCertificate

end OAI
