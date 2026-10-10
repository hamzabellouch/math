import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryDeterminantPositivity

namespace OAI

/-! # A positive first diagonal value for the boundary Hermitian matrix -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

def firstDiagonal (ell : ℕ) : EnclosurePolynomial :=
  let xy := state ell 8
  symmetrize (hermitian ell xy.1.1 xy.2.1 xy.1.1 xy.2.1)

theorem firstDiagonal_zero_positive (ell : Fin 4) :
    ((firstDiagonal ell)[0]?.getD zero).error <
      ((firstDiagonal ell)[0]?.getD zero).center.re := by
  fin_cases ell <;> decide +kernel

noncomputable def rawFirstDiagonal (ell : ℕ) (b Z : ℝ) : Polynomial ℂ :=
  reflectedHermitianPolynomial (scaledMass ell) (scaledShift Z)
    (stateMatrix (polynomialState ell b Z 8)) 0 0

attribute [local irreducible] state polynomialState

theorem rawFirstDiagonal_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    EnclosesPolynomial (firstDiagonal ell) (rawFirstDiagonal ell b Z) := by
  obtain ⟨hx₀, _, hy₀, _⟩ := state_sound ell b Z hb hZ 8
  have h := symmetrize_sound (hermitian_sound ell _ (inputS_sound Z hZ) hx₀ hy₀ hx₀ hy₀)
  convert h using 1 <;>
    simp [firstDiagonal, rawFirstDiagonal, reflectedHermitianPolynomial, hermitianPolynomial,
      stateMatrix, scaledMass, scaledShift]

attribute [local irreducible] EnclosesPolynomial firstDiagonal rawFirstDiagonal

theorem rawFirstDiagonal_at_zero_pos (ell : Fin 4) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    0 < ((rawFirstDiagonal ell b Z).eval 0).re := by
  rw [← coeff_zero_eq_eval_zero]
  exact realPart_pos (coefficient_sound (rawFirstDiagonal_sound ell b Z hb hZ) 0)
    (firstDiagonal_zero_positive ell)

end DefocusingNLS.BoundaryCertificate

end OAI
