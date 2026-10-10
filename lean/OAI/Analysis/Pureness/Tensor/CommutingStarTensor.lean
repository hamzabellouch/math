import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Star.TensorProduct

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]

def commutingStarTensorHom (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b)) : A ⊗[ℂ] B →⋆ₐ[ℂ] N :=
  { Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc with
    map_star' := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change φ (star a)*ψ (star b) = star (φ a*ψ b)
        rw [star_mul,← map_star,← map_star]
        exact (hc (star a) (star b)).eq
      | add z w hz hw =>
        let L := Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc
        change L (star z) = star (L z) at hz
        change L (star w) = star (L w) at hw
        change L (star (z+w)) = star (L (z+w))
        rw [star_add,map_add,map_add,hz,hw,star_add] }

lemma commutingStarTensorHom_tmul (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    commutingStarTensorHom φ ψ hc (a ⊗ₜ[ℂ] b) = φ a*ψ b := rfl
end CuntzPureness

end

end OAI
