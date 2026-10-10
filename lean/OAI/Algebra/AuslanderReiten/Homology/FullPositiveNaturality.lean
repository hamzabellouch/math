import OAI.Algebra.AuslanderReiten.Cocycles.SourceCocycleNaturality
import OAI.Algebra.AuslanderReiten.Stable.StableExtPrecomp
import OAI.Algebra.AuslanderReiten.HomComplex.PositiveFullHomExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem fullPositiveExtEquiv_precomp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : K ⟶ L) (n : ℕ) (x : CohomologyClass L M ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K M hK hM n (fullHomPrecomp f _ x) =
      (Ext.mk₀ (ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0))).comp
        (fullPositiveExtEquiv (k := k) L M hL hM n x) (zero_add _) := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain M) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, positiveExtStableEquiv_precomp hK hL,
    fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPrecomp_mk, fullHomSourceStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, StableHom.precomp_classOf,
    sourceCocycleMap_precomp (k := k)]

theorem fullPositiveExtEquiv_postcomp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : L ⟶ M) (n : ℕ) (x : CohomologyClass K L ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K M hK hM n (fullHomPostcomp f _ x) =
      (fullPositiveExtEquiv (k := k) K L hK hL n x).comp
        (Ext.mk₀ (ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0))) (add_zero _) := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain M) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, positiveExtStableEquiv_postcomp,
    fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, fullHomSourceStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, StableHom.postcomp_classOf,
    sourceCocycleMap_postcomp (k := k)]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
