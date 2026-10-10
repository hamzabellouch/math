import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryVertexCompression
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorIdealActions

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BimoduleO
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

@[simp] theorem tensor_smul (b : B) (c : ChainAlgebra k l) (v : BimoduleO P a l) :
    (b ⊗ₜ[k] c) • v = b • (c • v) := rfl

@[simp] theorem tensor_vertex_smul (i : Fin (l+1)) (v : BimoduleO P a l) :
    TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i) • v =
      ChainAlgebra.vertex k l i • v := by
  change (1:B) • (ChainAlgebra.vertex k l i • v) = _
  exact one_smul _ _

/-- The BC vertex space is the same actual subspace of O as the C vertex space. -/
def tensorVertexSpaceEquiv (i : Fin (l+1)) :
    IdempotentTensor.leftSpace (k := k) (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i))
      (BimoduleO P a l) ≃ₗ[k] Compression.vertexSpace (k := k) P a l i where
  toFun x := ⟨x.val, by
    have h := x.property
    change TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i) • x.val = x.val at h
    rw [tensor_vertex_smul] at h
    exact h⟩
  invFun x := ⟨x.val, by
    exact (tensor_vertex_smul P a l i (show BimoduleO P a l from x.val)).trans x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation uses the actual balanced tensor over BC, not only over C. -/
def tensorVertexEquiv (i : Fin (l+1)) :
    BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
      (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
      (BimoduleO P a l) ≃ₗ[k] (underlyingComplex (k := k) P).X (a+(i.val:ℤ)) := by
  letI (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k (Enveloping k B))
  have (n : ℤ) : IsScalarTower k (Enveloping k B) (P.X n) := IsScalarTower.of_compHom k (Enveloping k B) (P.X n)
  exact (IdempotentTensor.tensorEquiv (k := k)
    (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)) (BimoduleO P a l)
    (TensorIdeal.vertex_idempotent _ (ChainAlgebra.vertex_idempotent k l i))).trans
      ((tensorVertexSpaceEquiv P a l i).trans
        ((Compression.vertexEquiv (k := k) P a l i).restrictScalars k))
end LittleFinitistic.OrdinarySimulation.BimoduleO

end

end OAI
