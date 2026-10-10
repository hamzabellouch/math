import OAI.Algebra.Finitistic.Tensor.IdempotentTensor
import Mathlib.Algebra.Module.Projective

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {A : Type v} [Ring A] {e e' : A}

/-- An element of e'Ae acts by left multiplication on the right projectives. -/
def leftMultiply (b : A) (hb : e'*b=b) : rightIdeal e →ₗ[Aᵐᵒᵖ] rightIdeal e' where
  toFun m := ⟨b*m.val, by change e'*(b*m.val)=b*m.val; rw [← mul_assoc,hb]⟩
  map_add' m n := Subtype.ext (mul_add b m.val n.val)
  map_smul' a m := by apply Subtype.ext; exact (mul_assoc b m.val a.unop).symm

@[simp] theorem leftMultiply_apply (b : A) (hb : e'*b=b) (m : rightIdeal e) :
    (leftMultiply b hb m).val = b*m.val := rfl

/-- eA is a retract of the rank-one free right A-module. -/
def splitProjection (he : e*e=e) : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] rightIdeal e where
  toFun a := ⟨e*a.unop, by change e*(e*a.unop)=e*a.unop; rw [← mul_assoc,he]⟩
  map_add' a b := Subtype.ext (mul_add e a.unop b.unop)
  map_smul' a b := by apply Subtype.ext; exact (mul_assoc e b.unop a.unop).symm

def splitInclusion : rightIdeal e →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun a := MulOpposite.op a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightIdeal_projective (he : e*e=e) : Module.Projective Aᵐᵒᵖ (rightIdeal e) := by
  apply Module.Projective.of_split splitInclusion (splitProjection he)
  ext a
  exact a.property
end LittleFinitistic.IdempotentTensor

end

end OAI
