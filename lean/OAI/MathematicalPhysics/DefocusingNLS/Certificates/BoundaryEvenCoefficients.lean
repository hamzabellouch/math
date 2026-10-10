import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEnclosureDeterminant
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryHornerTransform
import Mathlib.Data.List.Forall2

namespace OAI

/-! # Extracting the coherent determinant's even coefficients -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

attribute [local irreducible] rawDeterminant determinant state polynomialState

noncomputable def evenValues (ell : ℕ) (b Z : ℝ) : List ℂ :=
  (List.range 16).map fun j => (rawDeterminant ell b Z).coeff (2 * j)

theorem evenCoefficients_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    List.Forall₂ (fun a z => a.Encloses z) (evenCoefficients ell) (evenValues ell b Z) := by
  rw [evenCoefficients, evenValues, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff, List.forall₂_same]
  intro j _
  have h := realPart_sound (coefficient_sound (rawDeterminant_sound ell b Z hb hZ) (2 * j))
  have hr : (((rawDeterminant ell b Z).coeff (2 * j)).re : ℂ) =
      (rawDeterminant ell b Z).coeff (2 * j) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (rawDeterminant_coeff_im ell b Z (2 * j)).symm
  rw [hr] at h
  exact h

attribute [local irreducible] transformAux polynomialTransformAux evenCoefficients evenValues

/-- The actual homogeneous transform is enclosed by precisely the list whose
sixteen coefficient inequalities were checked in the kernel. -/
theorem transformed_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (U V J : ℤ) :
    EnclosesPolynomial (transformed ell U V J)
      (homogeneousHorner U V J (evenValues ell b Z)) := by
  have h := transformAux_sound U V J (q := constant 0) (m := constant 1) (Q := 0) (M := 1)
    (List.forall₂_reverse_iff.mpr (evenCoefficients_sound ell b Z hb hZ))
    (by simpa using constant_sound 0) (by simpa using constant_sound 1)
  rw [polynomialTransformAux_reverse] at h
  exact h.1

end DefocusingNLS.BoundaryCertificate

end OAI
