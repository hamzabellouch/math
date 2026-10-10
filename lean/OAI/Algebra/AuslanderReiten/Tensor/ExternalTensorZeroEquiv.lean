import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDegreeZero
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def zeroEquiv : (complex k A B P Q).X 0 ≃ₗ[A ⊗[k] B]
    moduleObject k A B (P.X 0) (Q.X 0) where
  toLinearMap := bottomProjection k A B P Q 0
  invFun := cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩
  left_inv := bottomInsert_projection_zero k A B P Q
  right_inv := bottomProjection_bottom k A B P Q 0

theorem zeroEquiv_symm (x : moduleObject k A B (P.X 0) (Q.X 0)) :
    (zeroEquiv k A B P Q).symm x = inclusion k A B P Q 0 0 0 rfl x := by
  change cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩ x = _
  exact (LinearMap.congr_fun (inclusion_eq_directSum k A B P Q 0 0 0 rfl) x).symm

end ArExplicit.ExternalTensor

end

end OAI
