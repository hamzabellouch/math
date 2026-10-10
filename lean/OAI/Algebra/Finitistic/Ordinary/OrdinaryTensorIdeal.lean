import OAI.Algebra.Finitistic.Tensor.IdempotentTensor
import Mathlib.RingTheory.TensorProduct.Maps

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorIdeal
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable (e : C) (he : e*e=e)

def vertex : B ⊗[k] C := (1:B) ⊗ₜ[k] e

include he in
theorem vertex_idempotent : vertex (k := k) (B := B) e * vertex e = vertex e := by
  simp only [vertex, Algebra.TensorProduct.tmul_mul_tmul, one_mul, he]

def project : C →ₗ[k] IdempotentTensor.rightIdeal e where
  toFun c := ⟨e*c, by change e*(e*c)=e*c; rw [← mul_assoc,he]⟩
  map_add' x y := Subtype.ext (mul_add e x y)
  map_smul' r x := Subtype.ext (mul_smul_comm r e x)

def inclusion : B ⊗[k] IdempotentTensor.rightIdeal e →ₗ[k] B ⊗[k] C :=
  TensorProduct.map (LinearMap.id) ((IdempotentTensor.rightIdeal e).subtype.restrictScalars k)

def retraction : B ⊗[k] C →ₗ[k] B ⊗[k] IdempotentTensor.rightIdeal e :=
  TensorProduct.map (LinearMap.id) (project e he)

theorem inclusion_retraction (z : B ⊗[k] C) :
    inclusion e (retraction e he z) = vertex e * z := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [inclusion,retraction,TensorProduct.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,Submodule.subtype_apply,project,LinearMap.coe_mk,
      AddHom.coe_mk,vertex,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
  | add x y hx hy => simp only [map_add,mul_add,hx,hy]

theorem retraction_inclusion (z : B ⊗[k] IdempotentTensor.rightIdeal e) :
    retraction e he (inclusion e z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    change b ⊗ₜ[k] (⟨e*c.val, _⟩ : IdempotentTensor.rightIdeal e) = b ⊗ₜ[k] c
    congr 1
    exact Subtype.ext c.property
  | add x y hx hy => simp only [map_add,hx,hy]

include he in
theorem inclusion_fixed (z : B ⊗[k] IdempotentTensor.rightIdeal e) :
    vertex e * inclusion e z = inclusion e z := by
  rw [← inclusion_retraction e he, retraction_inclusion e he]

/-- The source term B tensor eC is the actual right ideal (1 tensor e)(B tensor C). -/
def equivalence : B ⊗[k] IdempotentTensor.rightIdeal e ≃ₗ[k]
    IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) where
  toFun z := ⟨inclusion e z, inclusion_fixed e he z⟩
  invFun z := retraction e he z.val
  left_inv := retraction_inclusion e he
  right_inv z := Subtype.ext ((inclusion_retraction e he z.val).trans z.property)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (map_smul _ r x)

@[simp] theorem equivalence_tmul (b : B) (c : IdempotentTensor.rightIdeal e) :
    (equivalence (B := B) e he (b ⊗ₜ[k] c)).val = b ⊗ₜ[k] c.val := rfl
end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
