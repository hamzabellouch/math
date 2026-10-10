import OAI.Analysis.KadisonKastler.TypeIIISpectralMatrix
import OAI.Analysis.KadisonKastler.FiniteInnerAveraging

namespace OAI

/-! # Constructed scalar averaging in type III factors -/

namespace KadisonKastler

open Generator
open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

/-- The finite signed matrix group, considered as inner automorphisms of M. -/
def matrixInnerAverage {n : ℕ} (E : MatrixUnitSystem (Fin n) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra) : FiniteInnerAverage M where
  Index := SignedPermutation (Fin n)
  fintype := inferInstance
  nonempty := inferInstance
  unitary g := algebraUnitaryOfMem (matrixUnitSignedRepresentation E g)
    (hE (matrixUnitSignedRepresentation_mem E g))

/-- A finite inner average brings a self-adjoint element arbitrarily close
to a scalar, by averaging its actual spectral matrix approximation. -/
theorem TypeIIIFactor.exists_selfAdjoint_scalar_average (hM : TypeIIIFactor M)
    (x : Algebra M) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  classical
  obtain ⟨n, E, hn, hE, y, hy, hxy⟩ := hM.exists_selfAdjoint_matrix_approx x hx ε hε
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let A := matrixInnerAverage E hE
  obtain ⟨z, hz⟩ := matrixUnitAverage_scalar E y hy
  have hAz : A.apply y = z • (1 : H →L[ℂ] H) := hz
  refine ⟨A, z, ?_⟩
  rw [← hAz]
  exact (A.norm_apply_sub_le x.val y).trans_lt hxy

end

end KadisonKastler

end OAI
