import OAI.Combinatorics.ContingencyTables.Dense.DenseMatrixLayoutProgram

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

abbrev FlatExponentData := GridFlatData×ℕ

def flatToGridData (z : FlatExponentData) : ExponentData :=
  ((z.1.1,unflattenGrid z.1),z.2)

def flatToGridDataRealizer : Realizer flatToGridData :=
  pair (pair (composition first first) (composition first unflattenGridRealizer)) second

theorem polynomial_flatToGridData : PolynomialTime flatToGridDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_unflattenGrid)) polynomial_second

def flatExponent (z : FlatExponentData) : ℕ := gridExponent (flatToGridData z)

def flatExponentRealizer : Realizer flatExponent := composition flatToGridDataRealizer gridExponentRealizer

theorem polynomial_flatExponent : PolynomialTime flatExponentRealizer :=
  polynomial_composition polynomial_flatToGridData polynomial_gridExponent

theorem flatExponent_code {m n K : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (a : Grid (I := Fin (m*n)) K) :
    flatExponent (((marginCode R,marginCode P),gridNatCode a),d)=
      denseExponent R P d finProdFinEquiv a := by
  unfold flatExponent flatToGridData gridNatCode
  rw [unflattenGrid_code]
  exact gridExponent_code R P d a finProdFinEquiv

end ContingencyTables.DensePrograms

end OAI
