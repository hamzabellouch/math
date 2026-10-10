import OAI.Algebra.AuslanderReiten.Complete.CompleteFunctorRawEndpoint
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCokernel

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := S) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := S) (F := F))]
variable [(functor (k := k) (R := R) (S := S) (F := F)).PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain
  (functorComplex (functor (k := k) (R := R) (S := S) (F := F)) K)))

theorem rawFunctorEndpointIso_eq :
    rawFunctorEndpointIso (functor (k := k) (R := R) (S := S) (F := F)) K hK hFK =
      (cochainCokernelEquiv (k := k) (F := F) (S := S) K).toModuleIso := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((functorComplex (functor (k := k) (R := R) (S := S) (F := F)) K).d (-1) 0).hom) z
  have h := congrArg (fun f => f.hom x)
    (rawFunctorEndpointIso_augmentation (functor (k := k) (R := R) (S := S) (F := F)) K hK hFK)
  exact h.symm.trans (cokernelEquiv_mk (k := k) (F := F) (S := S) (K.d (-1) 0).hom x).symm

end ArExplicit.BalancedTensor

end

end OAI
