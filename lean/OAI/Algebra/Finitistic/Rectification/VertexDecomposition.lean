import OAI.Algebra.Finitistic.Tensor.IdempotentTensor
import OAI.Algebra.Finitistic.Encoding.DirectedBound

namespace OAI
noncomputable section
namespace LittleFinitistic.VertexDecomposition
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedBound.DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

abbrev Space (i : Fin n) := IdempotentTensor.leftSpace (k := k) (D.e i) M

/-- Projection onto an actual vertex subspace. -/
def project (i : Fin n) : M →ₗ[k] Space D M i where
  toFun x := ⟨D.e i • x, by
    change D.e i • (D.e i • x) = D.e i • x
    rw [← mul_smul, D.idem]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (smul_comm _ _ _)

/-- A module decomposes into its actual vertex subspaces. This is a vector-space
isomorphism; off-diagonal arrows act between its factors. -/
def equiv : M ≃ₗ[k] ((i : Fin n) → Space D M i) where
  toFun x i := project D M i x
  invFun x := ∑ i, (x i).val
  map_add' x y := by funext i; exact (project D M i).map_add x y
  map_smul' c x := by funext i; exact (project D M i).map_smul c x
  left_inv x := by
    change ∑ i, D.e i • x = x
    rw [← Finset.sum_smul, D.complete, one_smul]
  right_inv x := by
    funext i
    apply Subtype.ext
    change D.e i • (∑ j, (x j).val) = (x i).val
    rw [Finset.smul_sum]
    rw [Finset.sum_eq_single i]
    · exact (x i).property
    · intro j _ hji
      rw [← (x j).property, ← mul_smul, D.orthogonal i j (Ne.symm hji), zero_smul]
    · simp

@[simp] theorem equiv_apply (x : M) (i : Fin n) :
    equiv D M x i = project D M i x := rfl

@[simp] theorem equiv_symm_apply (x : (i : Fin n) → Space D M i) :
    (equiv D M).symm x = ∑ i, (x i).val := rfl

lemma project_self (i : Fin n) (x : Space D M i) : project D M i x.val = x :=
  Subtype.ext x.property

lemma project_other (i j : Fin n) (hij : i ≠ j) (x : Space D M j) :
    project D M i x.val = 0 := by
  apply Subtype.ext
  change D.e i • x.val = 0
  rw [← x.property, ← mul_smul, D.orthogonal i j hij, zero_smul]
end LittleFinitistic.VertexDecomposition

end

end OAI
