import OAI.Combinatorics.ContingencyTables.Dense.DenseScaleMatrixProgram

namespace OAI

/-! # Computing the dense exponent directly from a binary grid matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

def scaledData (z : ExponentData) : ExponentData := ((z.1.1,scaleMatrix z),z.2)

def scaledDataRealizer : Realizer scaledData :=
  pair (pair (composition first first) scaleMatrixRealizer) second

theorem polynomial_scaledData : PolynomialTime scaledDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_scaleMatrix) polynomial_second

def gridExponent (z : ExponentData) : ℕ := fullExponent (scaledData z)

def gridExponentRealizer : Realizer gridExponent :=
  composition scaledDataRealizer fullExponentRealizer

theorem polynomial_gridExponent : PolynomialTime gridExponentRealizer :=
  polynomial_composition polynomial_scaledData polynomial_fullExponent

theorem gridExponent_code {m n q K : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (a : Grid (I := Fin q) K)
    (e : Fin m×Fin n ≃ Fin q) :
    gridExponent (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat))=
      denseExponent R P d e a := by
  unfold gridExponent scaledData
  rw [scaleMatrix_code]
  exact fullExponent_code R P d e a

end ContingencyTables.DensePrograms

end OAI
