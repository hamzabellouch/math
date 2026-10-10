import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorVertex
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedActions

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

def VertexTensor (i : Fin (l+1)) :=
  BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
    (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (BimoduleO P a l)

namespace VertexTensor
variable (i : Fin (l+1))
instance : AddCommGroup (VertexTensor P a l i) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l) _ (BimoduleO P a l)))
instance : Module k (VertexTensor P a l i) := inferInstanceAs (Module k (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l) _ (BimoduleO P a l)))

def action : Enveloping k B →ₐ[k] Module.End k (VertexTensor P a l i) :=
  by
    have : SMulCommClass Bᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
      ⟨fun r x v => (smul_comm x r v).symm⟩
    exact BalancedTensor.bimoduleAction

instance : Module (Enveloping k B) (VertexTensor P a l i) := Module.compHom _ (action P a l i).toRingHom
instance : IsScalarTower k (Enveloping k B) (VertexTensor P a l i) where
  smul_assoc r x z := by
    change action P a l i (r • x) z = r • action P a l i x z
    rw [map_smul]
    rfl

def mk : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)) →ₗ[k]
    BimoduleO P a l →ₗ[k] VertexTensor P a l i := BalancedTensor.mk k (B ⊗[k] ChainAlgebra k l)
    (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (BimoduleO P a l)

@[simp] theorem action_tmul_mk (b : B) (r : Bᵐᵒᵖ)
    (m : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (v : BimoduleO P a l) :
    (b ⊗ₜ[k] r) • mk P a l i m v = mk P a l i (b • m) (r • v) := rfl

local instance termScalar (n : ℤ) : Module k (P.X n) := Module.compHom _ (algebraMap k (Enveloping k B))
local instance termTower (n : ℤ) : IsScalarTower k (Enveloping k B) (P.X n) :=
  IsScalarTower.of_compHom k (Enveloping k B) (P.X n)

/-- Evaluation of the actual BC-balanced tensor. -/
def evaluation : VertexTensor P a l i ≃ₗ[k] P.X (a+(i.val:ℤ)) :=
  BimoduleO.tensorVertexEquiv P a l i

@[simp] theorem evaluation_mk
    (m : IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (ChainAlgebra.vertex k l i)))
    (v : BimoduleO P a l) :
    evaluation P a l i (mk P a l i m v) = (m.val • v : BimoduleO P a l) i := rfl

/-- The original enveloping-algebra action is the two original B-actions. -/
theorem enveloping_smul (b : B) (r : Bᵐᵒᵖ) (v : BimoduleO P a l) :
    (b ⊗ₜ[k] r : Enveloping k B) • v = b • (r • v) := by
  change (b ⊗ₜ[k] r : Enveloping k B) • (v : Compression P a l) =
    (b ⊗ₜ[k] (1:Bᵐᵒᵖ)) • (((1:B) ⊗ₜ[k] r) • (v : Compression P a l))
  rw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

theorem evaluation_tmul_smul (b : B) (r : Bᵐᵒᵖ) (z : VertexTensor P a l i) :
    evaluation P a l i ((b ⊗ₜ[k] r) • z) =
      (b ⊗ₜ[k] r : Enveloping k B) • (evaluation P a l i z : P.X (a+(i.val:ℤ))) := by
  have h : (evaluation P a l i).toLinearMap.comp (action P a l i (b ⊗ₜ[k] r)) =
      (Algebra.lsmul k k (P.X (a+(i.val:ℤ))) (b ⊗ₜ[k] r : Enveloping k B)).comp
        (evaluation P a l i).toLinearMap := by
    apply BalancedTensor.ext
    intro m v
    change evaluation P a l i ((b ⊗ₜ[k] r) • mk P a l i m v) =
      (b ⊗ₜ[k] r : Enveloping k B) • evaluation P a l i (mk P a l i m v)
    rw [action_tmul_mk, evaluation_mk, evaluation_mk]
    change (((TensorIdeal.coefficient b * m.val) • (r • v)) : BimoduleO P a l) i = _
    have hv : (TensorIdeal.coefficient b * m.val) • (r • v) =
        (b ⊗ₜ[k] r : Enveloping k B) • (m.val • v) := by
      rw [mul_smul, smul_comm m.val r]
      change (b ⊗ₜ[k] (1:ChainAlgebra k l)) • (r • (m.val • v)) = _
      rw [BimoduleO.tensor_smul, one_smul, ← enveloping_smul]
    exact congrArg (fun w : BimoduleO P a l => w i) hv
  exact congrArg (fun f => f z) h

theorem evaluation_smul (x : Enveloping k B) (z : VertexTensor P a l i) :
    evaluation P a l i (x • z) = x • (evaluation P a l i z : P.X (a+(i.val:ℤ))) := by
  induction x using TensorProduct.inductionOn with
  | tmul b r => exact evaluation_tmul_smul P a l i b r z
  | add x y hx hy => simp only [add_smul,map_add,hx,hy]

/-- Degreewise comparison as a genuine B-bimodule equivalence. -/
def bimoduleEquiv : VertexTensor P a l i ≃ₗ[Enveloping k B] P.X (a+(i.val:ℤ)) where
  __ := (evaluation P a l i).toAddEquiv
  map_smul' x z := evaluation_smul P a l i x z
end VertexTensor
end LittleFinitistic.OrdinarySimulation

end

end OAI
