import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixOperator (A : ι → ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl

lemma matrixOperator_selfAdjoint (A : ι → ι → ℂ)
    (hA : ∀ i j, A i j = star (A j i)) : IsSelfAdjoint (matrixOperator A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  change (Matrix.toEuclideanLin A).IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact (hA i j).symm

end TwoPointCorrelations

end OAI
