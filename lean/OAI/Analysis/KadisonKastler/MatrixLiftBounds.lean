import OAI.Analysis.KadisonKastler.MatrixEmbedding
import OAI.Analysis.KadisonKastler.ScalarAmplification
import OAI.Analysis.KadisonKastler.FiniteMatrixFreeModel

namespace OAI

/-! # The dimension-free commutator estimate for finite model lifts -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B ι : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [Fintype ι] [DecidableEq ι]

local instance liftBoundScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance liftBoundScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

theorem matrixUnitsEmbedding_map (E : Generator.MatrixUnitSystem ι A)
    (φ : A →⋆ₐ[ℂ] B) (x : CStarMatrix ι ι ℂ) :
    matrixUnitsEmbedding (E.map φ) x = φ (matrixUnitsEmbedding E x) := by
  simp only [matrixUnitsEmbedding_apply, Generator.MatrixUnitSystem.map_entry,
    map_sum, map_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n j : ℕ}

/-- The coordinate finite model, now viewed directly as a matrix of
operators on the original Hilbert space. -/
def finiteMatrixAmbientEmbedding (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M)) :
    FiniteMatrixModel n j →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) :=
  coefficientMatrixMap (matrixUnitsEmbedding (E.map M.toStarSubalgebra.subtype))

theorem mappedMatrixUnits_algebra_le
    (E : Generator.MatrixUnitSystem ι (Algebra M)) :
    (E.map M.toStarSubalgebra.subtype).algebra ≤ M.toStarSubalgebra := by
  rintro x ⟨a, rfl⟩
  have he := matrixUnitsEmbedding_map E M.toStarSubalgebra.subtype (CStarMatrix.ofMatrix a)
  change (E.map M.toStarSubalgebra.subtype).hom a = (E.hom a).val at he
  change (E.map M.toStarSubalgebra.subtype).hom a ∈ M.toStarSubalgebra
  rw [he]
  exact (E.hom a).property

theorem finiteMatrixAmbientEmbedding_entry_mem
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (x : FiniteMatrixModel n j) (a b : Fin n) :
    finiteMatrixAmbientEmbedding E x a b ∈ (E.map M.toStarSubalgebra.subtype).algebra :=
  ⟨CStarMatrix.ofMatrix.symm (x a b), rfl⟩

local instance liftBoundOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance liftBoundOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Every coordinate finite-matrix unitary has commutator bounded by
twice the scalar derivation bound, uniformly in both matrix sizes. -/
theorem finiteMatrix_unitary_commutator_le
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (u : unitary (FiniteMatrixModel n j)) :
    let v := Unitary.map (StarMonoidHom.ofClass (finiteMatrixAmbientEmbedding E)) u
    ‖diagonalAmplification h * (v : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) -
      (v : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) * diagonalAmplification h‖ ≤ 2 * δ := by
  let v : unitary (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :=
    Unitary.map (StarMonoidHom.ofClass (finiteMatrixAmbientEmbedding E)) u
  have hv : ∀ a b, (v : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) a b ∈
      (E.map M.toStarSubalgebra.subtype).algebra :=
    fun a b => finiteMatrixAmbientEmbedding_entry_mem E (u : FiniteMatrixModel n j) a b
  exact matrixUnit_lift_commutator_le M (E.map M.toStarSubalgebra.subtype)
    (mappedMatrixUnits_algebra_le E) h hδ hb v hv

end

end KadisonKastler

end OAI
