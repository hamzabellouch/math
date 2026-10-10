import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateArithmetic
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryHermitianPolynomial

namespace OAI

/-! # Soundness of the boundary coefficient recipe -/

open Polynomial

namespace DefocusingNLS.GaussianEnclosure

theorem realPart_pos {a : GaussianEnclosure} {z : ℂ} (ha : a.Encloses z)
    (hpos : a.error < a.center.re) : 0 < z.re := by
  have h := (Complex.abs_re_le_norm (z - (a.center : ℂ))).trans ha
  have hp : (a.error : ℝ) < (a.center.re : ℝ) := by exact_mod_cast hpos
  rw [Complex.sub_re, ← GaussianInt.intCast_re] at h
  have hlow := (abs_le.mp h).1
  linarith

theorem realPart_sound {a : GaussianEnclosure} {z : ℂ} (ha : a.Encloses z) :
    (⟨⟨a.center.re, 0⟩, a.error⟩ : GaussianEnclosure).Encloses (z.re : ℂ) := by
  have h := (Complex.abs_re_le_norm (z - (a.center : ℂ))).trans ha
  rw [Complex.sub_re, ← GaussianInt.intCast_re] at h
  change ‖(z.re : ℂ) - (GaussianInt.toComplex ⟨a.center.re, 0⟩)‖ ≤ _
  have hc : GaussianInt.toComplex ⟨a.center.re, 0⟩ = ((a.center.re : ℝ) : ℂ) := by
    rw [GaussianInt.toComplex_def', Int.cast_zero, zero_mul, add_zero]
    norm_cast
  rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h

end DefocusingNLS.GaussianEnclosure

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

theorem constant_sound (n : ℤ) : EnclosesPolynomial (constant n) (C (n : ℂ)) := by
  refine ⟨(n : ℂ), 0, ?_, rfl, by simp⟩
  simp [coefficient, Encloses, GaussianInt.toComplex_def]

theorem sharpPolynomial_cons (z : ℂ) (p : Polynomial ℂ) :
    sharpPolynomial (C z + X * p) = C (star z) - X * sharpPolynomial p := by
  simp only [sharpPolynomial, conjugatePolynomial, Polynomial.map_add, Polynomial.map_mul,
    map_C, map_X, add_comp, mul_comp, C_comp, X_comp]
  simp only [map_neg, map_one, neg_one_mul, starRingEnd_apply]
  ring

theorem sharpAux_sound (b : Bool) {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) :
    EnclosesPolynomial (sharpAux b as) (if b then -sharpPolynomial p else sharpPolynomial p) := by
  induction as generalizing b p with
  | nil =>
    change p = 0 at hp
    subst p
    cases b <;> simp [sharpAux, EnclosesPolynomial, sharpPolynomial, conjugatePolynomial]
  | cons a as ih =>
    obtain ⟨z, q, hz, hq, rfl⟩ := hp
    cases b
    · refine ⟨star z, -sharpPolynomial q, conj_sound hz, ih true hq, ?_⟩
      change sharpPolynomial (C z + X * q) = C (star z) + X * (-sharpPolynomial q)
      rw [sharpPolynomial_cons]
      ring
    · refine ⟨-star z, sharpPolynomial q, neg_sound (conj_sound hz), ih false hq, ?_⟩
      change -sharpPolynomial (C z + X * q) = C (-star z) + X * sharpPolynomial q
      rw [sharpPolynomial_cons, map_neg]
      ring

theorem sharp_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) : EnclosesPolynomial (sharp as) (sharpPolynomial p) :=
  sharpAux_sound false hp

theorem symmetrize_sound {as : List GaussianEnclosure} {p : Polynomial ℂ}
    (hp : EnclosesPolynomial as p) :
    EnclosesPolynomial (symmetrize as) (p + sharpPolynomial p) :=
  addPolynomial_sound hp (sharp_sound hp)

theorem hermitian_sound (ell : ℕ) (s : ℂ)
    (hs : EnclosesPolynomial [coefficient 0 270506819 2] (C s))
    {x y z w : List GaussianEnclosure} {X Y Z W : Polynomial ℂ}
    (hx : EnclosesPolynomial x X) (hy : EnclosesPolynomial y Y)
    (hz : EnclosesPolynomial z Z) (hw : EnclosesPolynomial w W) :
    EnclosesPolynomial (hermitian ell x y z w)
      (C ((100000000 * (ell + 5) : ℤ) : ℂ) * conjugatePolynomial X * Z +
        C s * (conjugatePolynomial X * W - conjugatePolynomial Y * Z)) :=
  addPolynomial_sound
    (mulPolynomial_sound (mulPolynomial_sound (constant_sound _) (conjPolynomial_sound hx)) hz)
    (mulPolynomial_sound hs (subPolynomial_sound
      (mulPolynomial_sound (conjPolynomial_sound hx) hw)
      (mulPolynomial_sound (conjPolynomial_sound hy) hz)))

end DefocusingNLS.BoundaryCertificate

end OAI
