import OAI.Algebra.AuslanderReiten.Complete.CompleteTailExt
import OAI.Algebra.AuslanderReiten.Complete.CompleteTailEndpoint

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

theorem fullPositiveExtEquiv_functor (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) (functorComplex F K) (functorComplex F K)
      hFK hFK.toExactProjectiveComplex n
      (CohomologyClass.mk (fullHomCocycleMap F K K ((n+1 : ℕ) : ℤ) x)) =
    ((Ext.mk₀ (completeFunctorEndpointIso F K hK hFK).hom).comp
      ((fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
        (CohomologyClass.mk x)).mapExactFunctor F) (zero_add _)).comp
          (Ext.mk₀ (completeFunctorEndpointIso F K hK hFK).inv) (add_zero _) :=
  fullPositiveExtEquiv_functor_mk (k := k) F K hK hFK
    (completeFunctorEndpointIso F K hK hFK)
    (completeFunctorEndpointIso_augmentation F K hK hFK) n x

end ArExplicit.CompleteComparison

end

end OAI
