import OAI.Algebra.AuslanderReiten.HomComplex.PositiveFullHomProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

theorem fullPositiveExtEquiv_augmented (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n (CohomologyClass.mk x) =
    (completeExtResolution hK).extMk
      (ResolutionProducts.natComparisonAugmentation (completeExtResolution hK) (n+1)
        (cochainTailMap K K (n+1) x.val)) (n+2) rfl
      (ResolutionProducts.natComparison_augmented_cycle (completeExtResolution hK) (n+1)
        (cochainTailMap K K (n+1) x.val) (cochainTailMap_comm (k := k) K K (n+1) x)) := by
  rw [fullPositiveExtEquiv_mk]
  exact ResolutionProducts.natComparison_endExt_eq (completeExtResolution hK) (n+1)
    (cochainTailMap K K (n+1) x.val) (cochainTailMap_comm (k := k) K K (n+1) x)

end ArExplicit.CompleteComparison

end

end OAI
