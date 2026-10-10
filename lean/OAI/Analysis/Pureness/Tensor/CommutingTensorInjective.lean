import OAI.Analysis.Pureness.Tensor.CommutingAlgTensorInjective
import OAI.Analysis.Pureness.Tensor.CommutingStarTensor

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]
variable [Nontrivial A]

theorem commutingStarTensorHom_injective (hsimple : TopologicallySimple A)
    (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N) (hψ : Function.Injective ψ)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (commutingStarTensorHom φ ψ hc) :=
  commutingAlgTensorHom_injective hsimple φ.toAlgHom ψ.toAlgHom hψ hc
end CuntzPureness

end

end OAI
