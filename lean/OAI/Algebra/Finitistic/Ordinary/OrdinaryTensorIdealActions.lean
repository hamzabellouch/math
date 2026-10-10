import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorIdeal

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorIdeal
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable (e : C)

abbrev coefficient : B →ₐ[k] B ⊗[k] C := Algebra.TensorProduct.includeLeft

theorem coefficient_commute (b : B) :
    vertex (k := k) e * coefficient b = coefficient b * vertex e := by
  simp only [vertex,coefficient,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

def leftMultiply (b : B) : IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) →ₗ[(B ⊗[k] C)ᵐᵒᵖ]
    IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e) where
  toFun x := ⟨coefficient b * x.val, by
    change vertex e * (coefficient b * x.val) = coefficient b * x.val
    rw [← mul_assoc, coefficient_commute, mul_assoc, x.property]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ r.unop).symm

def leftAction : B →ₐ[k] Module.End (B ⊗[k] C)ᵐᵒᵖ
    (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  toFun := leftMultiply e
  map_one' := by ext x; exact one_mul x.val
  map_mul' b c := by
    ext x
    change coefficient (b*c) * x.val = coefficient b * (coefficient c * x.val)
    rw [map_mul,mul_assoc]
  map_zero' := by
    ext x
    change coefficient (0:B) * x.val = 0
    rw [map_zero,zero_mul]
  map_add' b c := by
    ext x
    change coefficient (b+c) * x.val = coefficient b * x.val + coefficient c * x.val
    rw [map_add,add_mul]
  commutes' r := by
    ext x
    change coefficient (algebraMap k B r) * x.val = r • x.val
    rw [AlgHom.commutes, Algebra.smul_def]

instance leftModule : Module B (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) :=
  Module.compHom _ (leftAction (k := k) (B := B) e).toRingHom

instance towerLeft : IsScalarTower k B (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  smul_assoc r b x := by
    change leftAction e (r • b) x = r • leftAction e b x
    rw [map_smul]
    rfl

instance commute : SMulCommClass B (B ⊗[k] C)ᵐᵒᵖ
    (IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) where
  smul_comm b r x := (leftAction e b).map_smul r x

@[simp] theorem left_smul_value (b : B)
    (x : IdempotentTensor.rightIdeal (vertex (k := k) (B := B) e)) :
    (b • x).val = coefficient b * x.val := rfl
end LittleFinitistic.OrdinarySimulation.TensorIdeal

end

end OAI
