import OAI.Analysis.BoundedHochschild.CountableColumnRegrouping
import OAI.Analysis.BoundedHochschild.MatrixCornerCommutant

namespace OAI

/-!
# Finite self-similar matrix systems in a properly infinite algebra

Every positive finite matrix size occurs unitally, and its commutant is
isomorphic to the original algebra. These are concrete matrix systems for the
properly infinite amplification argument.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildMatrixSystems

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Unital matrix systems of arbitrary finite size, with their actual
commutants identified with the given algebra. -/
theorem exists_self_commutant_matrixSystem (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (n : ℕ) [NeZero n] :
    ∃ E : MatrixSystem M n, Nonempty (M ≃⋆ₐ[ℂ] E.commutant) := by
  obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno n
  let E := matrixSystemOfColumns c hi ho hs
  let i : Fin n := ⟨0, NeZero.pos n⟩
  refine ⟨E, ⟨?_⟩⟩
  exact (isometryCornerEquiv (c i) (hi i)).trans (matrixCornerCommutantEquiv E i)

end BoundedHochschild.KadisonRingrose

end

end OAI
