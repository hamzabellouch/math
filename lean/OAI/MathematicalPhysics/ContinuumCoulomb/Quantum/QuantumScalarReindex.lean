import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicHistory

namespace OAI

/-! Exact reindexing of the four-rational local-core sums.  This lets the
literal support-list coordinates evaluate the propagation Gram matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators

private theorem scalar_add_eq (x y : Scalar) : add x y=x+y := rfl
theorem scalar_sum_eq (xs : List Scalar) : QuantumAlgebraicScalar.sum xs=xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [QuantumAlgebraicScalar.sum,ih,List.sum_cons,scalar_add_eq]

theorem scalar_finiteSum_eq {α : Type} [Fintype α] (f : α → Scalar) :
    finiteSum f=∑ a,f a := by
  rw [finiteSum,scalar_sum_eq]
  simp only [enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp f

theorem scalar_finiteSum_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → Scalar) :
    finiteSum (fun a => f (e a))=finiteSum f := by
  rw [scalar_finiteSum_eq,scalar_finiteSum_eq]
  exact e.sum_comp f

def reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) : Matrix α α Scalar :=
  fun s t => A (e s) (e t)

theorem matMul_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix β β Scalar) :
    matMul (reindex e A) (reindex e B)=reindex e (matMul A B) := by
  funext s t
  exact scalar_finiteSum_reindex e (fun u => mul (A (e s) u) (B u (e t)))

theorem adjoint_reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) :
    adjoint (reindex e A)=reindex e (adjoint A) := rfl

theorem gram_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix β β Scalar) :
    matMul (adjoint (reindex e A)) (reindex e A)=
      reindex e (matMul (adjoint A) A) := by
  rw [adjoint_reindex,matMul_reindex]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
