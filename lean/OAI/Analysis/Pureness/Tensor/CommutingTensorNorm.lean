import OAI.Analysis.Pureness.Tensor.CommutingTensorInjective
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]
variable [Nontrivial A]
variable (hsimple : TopologicallySimple A)
variable (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
variable (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b))

abbrev commutingTensorNormedRing : NormedRing (A ⊗[ℂ] B) :=
  NormedRing.induced _ N (commutingStarTensorHom φ ψ hc)
    (commutingStarTensorHom_injective hsimple φ ψ hψ hc)

abbrev commutingTensorNormedAlgebra :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    NormedAlgebra ℂ (A ⊗[ℂ] B) := by
  letI := commutingTensorNormedRing hsimple φ ψ hψ hc
  exact
  NormedAlgebra.induced ℂ _ N (commutingStarTensorHom φ ψ hc)

theorem commutingTensorCStarRing :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    CStarRing (A ⊗[ℂ] B) := by
  let := commutingTensorNormedRing hsimple φ ψ hψ hc
  refine ⟨fun z => ?_⟩
  change ‖commutingStarTensorHom φ ψ hc z‖*‖commutingStarTensorHom φ ψ hc z‖ ≤
      ‖commutingStarTensorHom φ ψ hc (star z*z)‖
  rw [map_mul,map_star,CStarRing.norm_star_mul_self]

lemma commutingTensor_norm_def (z : A ⊗[ℂ] B) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    ‖z‖ = ‖commutingStarTensorHom φ ψ hc z‖ := rfl

lemma commutingTensor_norm_tmul_le (a : A) (b : B) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    ‖a ⊗ₜ[ℂ] b‖ ≤ ‖a‖*‖b‖ := by
  change ‖φ a*ψ b‖ ≤ ‖a‖*‖b‖
  exact (norm_mul_le _ _).trans (mul_le_mul
    (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom a)
    (NonUnitalStarAlgHom.norm_apply_le ψ.toNonUnitalStarAlgHom b)
    (norm_nonneg _) (norm_nonneg _))
end CuntzPureness

end

end OAI
