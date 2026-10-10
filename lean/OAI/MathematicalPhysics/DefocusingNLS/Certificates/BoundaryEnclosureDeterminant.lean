import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEnclosureStateLink

namespace OAI

/-! # Structural identities for the determinant enclosed by the certificate -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

attribute [local irreducible] polynomialState state

noncomputable def rawDeterminant (ell : ℕ) (b Z : ℝ) : Polynomial ℂ :=
  let T := stateMatrix (polynomialState ell b Z 8)
  let S := reflectedHermitianPolynomial (scaledMass ell) (scaledShift Z) T
  S 0 0 * S 1 1 - S 0 1 * conjugatePolynomial (S 0 1)

theorem rawDeterminant_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    EnclosesPolynomial (determinant ell) (rawDeterminant ell b Z) := by
  convert determinant_sound ell b Z hb hZ using 1
  simp only [rawDeterminant, reflectedHermitianPolynomial, hermitianPolynomial,
    stateMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    scaledMass, scaledShift]
  norm_cast

theorem conjugatePolynomial_comp_scale (p : Polynomial ℂ) :
    conjugatePolynomial (p.comp variableScale) = (conjugatePolynomial p).comp variableScale := by
  have hc : (starRingEnd ℂ) (100000000 : ℂ) = 100000000 :=
    map_ofNat (starRingEnd ℂ) 100000000
  simp [conjugatePolynomial, variableScale, Polynomial.map_comp, hc]

theorem sharpPolynomial_comp_scale (p : Polynomial ℂ) :
    sharpPolynomial (p.comp variableScale) = (sharpPolynomial p).comp variableScale := by
  rw [sharpPolynomial, conjugatePolynomial_comp_scale, comp_assoc, sharpPolynomial, comp_assoc]
  congr 1
  simp only [variableScale, mul_comp, C_comp, X_comp]
  ring

theorem hermitianPolynomial_comp_scale (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) :
    hermitianPolynomial M s (fun a b => (T a b).comp variableScale) i j =
      (hermitianPolynomial M s T i j).comp variableScale := by
  simp only [hermitianPolynomial, conjugatePolynomial_comp_scale, add_comp, mul_comp,
    sub_comp, C_comp]

theorem reflectedHermitianPolynomial_comp_scale (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) :
    reflectedHermitianPolynomial M s (fun a b => (T a b).comp variableScale) i j =
      (reflectedHermitianPolynomial M s T i j).comp variableScale := by
  simp only [reflectedHermitianPolynomial, hermitianPolynomial_comp_scale,
    sharpPolynomial_comp_scale, add_comp]

theorem rawDeterminant_eq (ell : ℕ) (b Z : ℝ) :
    rawDeterminant ell b Z =
      (boundaryDeterminantPolynomial (scaledMass ell) (scaledShift Z)
        (fun n => scaledConstant ell n b) 8).comp variableScale := by
  have hT : stateMatrix (polynomialState ell b Z 8) =
      fun i j => (boundaryForwardProduct (scaledMass ell) (scaledShift Z)
        (fun n => scaledConstant ell n b) 8 i j).comp variableScale := by
    apply Matrix.ext
    intro i j
    exact polynomialState_matrix ell b Z 8 i j
  simp only [rawDeterminant, hT, reflectedHermitianPolynomial_comp_scale,
    conjugatePolynomial_comp_scale, boundaryDeterminantPolynomial, sub_comp, mul_comp]

theorem rawDeterminant_degree (ell : ℕ) (b Z : ℝ) : (rawDeterminant ell b Z).natDegree ≤ 30 := by
  rw [rawDeterminant_eq]
  have h := boundaryDeterminantPolynomial_degree (scaledMass ell) (scaledShift Z)
    (fun n => scaledConstant ell n b) 8 (by decide) (by simp [scaledShift])
  calc
    _ ≤ (boundaryDeterminantPolynomial (scaledMass ell) (scaledShift Z)
      (fun n => scaledConstant ell n b) 8).natDegree * variableScale.natDegree := natDegree_comp_le
    _ ≤ 30 := by simpa [variableScale] using h

theorem rawDeterminant_coeff_im (ell : ℕ) (b Z : ℝ) (n : ℕ) :
    ((rawDeterminant ell b Z).coeff n).im = 0 := by
  rw [rawDeterminant_eq]
  simp only [variableScale, comp_C_mul_X_coeff]
  have hn : ((100000000 : ℂ) ^ n).im = 0 := by
    have he : (100000000 : ℂ) = ((100000000 : ℝ) : ℂ) := by norm_num
    rw [he, ← Complex.ofReal_pow]
    rfl
  rw [Complex.mul_im]
  rw [boundaryDeterminantPolynomial_coeff_im (scaledMass ell) (scaledShift Z)
    (fun n => scaledConstant ell n b) 8 n (by simp [scaledShift]), hn]
  ring

theorem rawDeterminant_coeff_odd (ell : ℕ) (b Z : ℝ) (n : ℕ) (hn : Odd n) :
    (rawDeterminant ell b Z).coeff n = 0 := by
  rw [rawDeterminant_eq]
  simp only [variableScale, comp_C_mul_X_coeff]
  rw [boundaryDeterminantPolynomial_coeff_odd (scaledMass ell) (scaledShift Z)
    (fun n => scaledConstant ell n b) 8 n (by simp [scaledShift]) hn, zero_mul]

end DefocusingNLS.BoundaryCertificate

end OAI
