import OAI.Analysis.KadisonKastler.MatrixTrace

namespace OAI

/-! # The canonical traces of the finite matrix-model coordinates -/

namespace KadisonKastler

noncomputable section

local instance scalarMatrixOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance scalarMatrixStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- The normalized trace on the scalar algebra. -/
def scalarTrace : FaithfulTracialState ℂ where
  toLinearMap := LinearMap.id
  map_one := rfl
  positive x := by
    change 0 ≤ (star x * x).re
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg x.re, sq_nonneg x.im]
  positive_im x := by
    change (star x * x).im = 0
    rw [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  faithful x hx := (CStarRing.star_mul_self_eq_zero_iff x).mp hx
  tracial := mul_comm

/-- The coordinate algebra M_n(M_(j+1)(C)) in the finite-matrix model. -/
abbrev FiniteMatrixModel (n j : ℕ) :=
  CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin (j + 1)) (Fin (j + 1)) ℂ)

/-- The normalized trace on the finite-matrix-model coordinate. -/
def finiteMatrixModelTrace (n : ℕ) [NeZero n] (j : ℕ) :
    FaithfulTracialState (FiniteMatrixModel n j) := matrixTrace (matrixTrace scalarTrace)

end

end KadisonKastler

end OAI
