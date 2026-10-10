import OAI.Algebra.AuslanderReiten.HomComplex.FullCochainProducts
import OAI.Algebra.AuslanderReiten.Ext.NatComparisonExt
import OAI.Algebra.AuslanderReiten.Stable.SourceStableCoordinates

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

def restrictedEndExt (r : ℕ) (x : Cocycle K K (r : ℤ)) :
    Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
      (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) r :=
  ResolutionProducts.endExt (completeExtResolution hK)
    (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex r x)

theorem fullPositiveExtEquiv_mk (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (CohomologyClass.mk x) = restrictedEndExt (k := k) K hK (n+1) x := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, fullHomSourceStableLinearEquiv_mk]
  unfold restrictedEndExt restrictedCocycle
  erw [ResolutionProducts.natComparison_endExt_eq,
    positiveExtStableEquiv_extMk]
  unfold completeExtCyclesStable
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  exact (sourceCocycleMap_mk (k := k) x z).trans (by rfl)

theorem restrictedEndExt_product {r s : ℕ}
    (x : Cocycle K K (r : ℤ)) (y : Cocycle K K (s : ℤ)) :
    (restrictedEndExt (k := k) K hK r x).comp (restrictedEndExt (k := k) K hK s y) rfl =
      restrictedEndExt (k := k) K hK (r+s) (ResolutionProducts.natCocycleProduct x y) := by
  unfold restrictedEndExt
  rw [ResolutionProducts.endExt_product, restrictedCocycle_product]

theorem fullPositiveExtEquiv_product (n m : ℕ)
    (x : Cocycle K K ((n+1 : ℕ) : ℤ)) (y : Cocycle K K ((m+1 : ℕ) : ℤ)) :
    (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (CohomologyClass.mk x)).comp
      (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex m
        (CohomologyClass.mk y)) rfl =
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex (n+1+m)
      (CohomologyClass.mk (ResolutionProducts.natCocycleProduct (n := n+1) (m := m+1) x y)) := by
  rw [fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk,
    restrictedEndExt_product]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
