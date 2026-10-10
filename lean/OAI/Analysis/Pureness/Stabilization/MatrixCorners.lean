import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [NonUnitalCStarAlgebra A]
abbrev FinMatrix (A : Type*) (n : ℕ) := CStarMatrix (Fin n) (Fin n) A

private def successorEntry {n : ℕ} (M : FinMatrix A n) (i j : Fin (n + 1)) : A :=
  Fin.lastCases 0 (fun i => Fin.lastCases 0 (M i) j) i

def matrixSuccessor (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A (n+1) where
  toFun M := CStarMatrix.ofMatrix (successorEntry M)
  map_zero' := by
    ext i j
    change successorEntry (0 : FinMatrix A n) i j = 0
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [successorEntry]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [successorEntry]
  map_add' M N := by
    ext i j
    change successorEntry (M + N) i j = successorEntry M i j + successorEntry N i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [successorEntry]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [successorEntry]
  map_mul' M N := by
    ext i j
    change successorEntry (M * N) i j = ∑ k, successorEntry M i k * successorEntry N k j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [successorEntry]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [successorEntry, Fin.sum_univ_castSucc]
      · simp [successorEntry, CStarMatrix.mul_apply, Fin.sum_univ_castSucc]
  map_smul' c M := by
    ext i j
    change successorEntry (c • M) i j = c • successorEntry M i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [successorEntry]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [successorEntry]
  map_star' M := by
    ext i j
    change successorEntry (star M) i j = star (successorEntry M j i)
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [successorEntry, CStarMatrix.star_apply]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [successorEntry, CStarMatrix.star_apply]

@[simp] lemma matrixSuccessor_apply (n : ℕ) (M : FinMatrix A n) (i j : Fin (n + 1)) :
    matrixSuccessor n M i j = Fin.lastCases 0 (fun i => Fin.lastCases 0 (M i) j) i := rfl

@[simp] lemma matrixSuccessor_apply_castSucc (n : ℕ) (M : FinMatrix A n) (i j : Fin n) :
    matrixSuccessor n M i.castSucc j.castSucc = M i j := by
  change successorEntry M i.castSucc j.castSucc = M i j
  simp [successorEntry]

lemma matrixSuccessor_injective (n : ℕ) : Function.Injective (matrixSuccessor (A := A) n) := by
  intro M N h
  ext i j
  have := congrArg (fun P : FinMatrix A (n+1) => P i.castSucc j.castSucc) h
  simpa using this

variable [PartialOrder A] [StarOrderedRing A]

lemma matrixSuccessor_isometry (n : ℕ) : Isometry (matrixSuccessor (A := A) n) :=
  NonUnitalStarAlgHom.isometry _ (matrixSuccessor_injective n)

@[simp] lemma matrixSuccessor_norm (n : ℕ) (M : FinMatrix A n) :
    ‖matrixSuccessor n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixSuccessor_injective n) M
end CuntzTrace

end

end OAI
