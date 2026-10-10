import OAI.Algebra.AuslanderReiten.Cones.TwoConeEvaluatedTriangles

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

namespace FiniteLeftModule
variable (X : FiniteLeftModule k R) {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}
variable (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
variable (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P.carrier)]
variable (τ : FrobeniusTrace k R)

theorem evaluationTriangle_second :
    (evaluationTriangle X f g hf hg he τ).mor₂ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X g)) :=
  resolutionTriangle_second τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1
    (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2
end FiniteLeftModule

namespace TwoCone
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

theorem evaluatedSkeletonTriangle_second (n : ℕ) :
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₂ =
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (FiniteLeftModule.evaluationMap X
          (M := skeletonCokernelModule D hf n) (N := middleCokernelModule D hf n)
          (singletonCokernelProjection D n))) := by
  let := hr (n+2)
  let : Module.Projective Rᵐᵒᵖ
      (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) :=
    EnvelopingBimodule.prod_right_projective
      (baseCokernelModule D hf (n+2)).carrier (baseCokernelModule D hf (n+2)).carrier
  exact FiniteLeftModule.evaluationTriangle_second X _ _
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n) τ

theorem evaluatedTopTriangle_second (n : ℕ) :
    (evaluatedTopTriangle D hf hex hr X τ n).mor₂ =
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (FiniteLeftModule.evaluationMap X
          (M := cokernelModule D hf n) (N := baseCokernelModule D hf (n+4))
          (topCokernelProjection D n))) := by
  let := hr (n+4)
  exact FiniteLeftModule.evaluationTriangle_second X _ _
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n) τ
end TwoCone
end ArExplicit

end

end OAI
