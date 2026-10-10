import OAI.Analysis.Pureness.States.FiniteFamilyPullback
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteMatrixFlattenProduct (k n : ℕ) :
    FinMatrix (FinMatrix A n) k ≃⋆ₐ[ℂ]
      CStarMatrix (Fin k × Fin n) (Fin k × Fin n) A where
  toFun X := CStarMatrix.ofMatrix (fun i j => X i.1 j.1 i.2 j.2)
  invFun X := CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (fun a b => X (i,a) (j,b)))
  left_inv X := by ext i j a b; rfl
  right_inv X := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl
  map_star' X := by ext i j; rfl
  map_mul' X Y := by
    ext i j
    change ((X*Y) i.1 j.1) i.2 j.2 =
      ∑ s : Fin k × Fin n, X i.1 s.1 i.2 s.2 * Y s.1 j.1 s.2 j.2
    simp only [CStarMatrix.mul_apply]
    let ev : FinMatrix A n →+ A :=
      { toFun := fun Z => Z i.2 j.2, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have he := map_sum ev (fun s : Fin k => X i.1 s * Y s j.1) Finset.univ
    change ((∑ s : Fin k, X i.1 s * Y s j.1) i.2 j.2)=
      ∑ s : Fin k, (X i.1 s * Y s j.1) i.2 j.2 at he
    rw [he]
    simp only [CStarMatrix.mul_apply,Fintype.sum_prod_type]

def finiteMatrixFlatten (k n : ℕ) :
    FinMatrix (FinMatrix A n) k ≃⋆ₐ[ℂ] FinMatrix A (k*n) :=
  (finiteMatrixFlattenProduct k n).trans (CStarMatrix.reindexₐ ℂ A finProdFinEquiv)

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteMatrixFlatten_entry (k n : ℕ) (X : FinMatrix (FinMatrix A n) k)
    (i j : Fin k) (a b : Fin n) :
    finiteMatrixFlatten k n X (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) = X i j a b := by
  change (finiteMatrixFlattenProduct k n X)
    (finProdFinEquiv.symm (finProdFinEquiv (i, a)))
    (finProdFinEquiv.symm (finProdFinEquiv (j, b))) = X i j a b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

lemma finiteMatrixFlatten_isometry (k n : ℕ) :
    Isometry (finiteMatrixFlatten (A := A) k n) :=
  NonUnitalStarAlgHom.isometry (finiteMatrixFlatten (A := A) k n).toNonUnitalStarAlgHom
    (finiteMatrixFlatten (A := A) k n).injective
end CuntzPureness

end

end OAI
