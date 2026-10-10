import OAI.Algebra.AuslanderReiten.Stable.TargetStableCoordinates
import OAI.Algebra.AuslanderReiten.Complete.TateKoszul

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FrobeniusTrace
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b)=τ.trace (b*a))
open CompleteComparison
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

def fullHomSourceDualityAt (a b : ℤ) (hb : b = -a-1) :
    Module.Dual k (CohomologyClass K K a) ≃ₗ[k] CohomologyClass K K b :=
  (fullHomSourceStableLinearEquiv (k := k) K K a hK
    hK.toExactProjectiveComplex).symm.dualMap |>.trans
      ((τ.completeStableDualityAt hs (chainOfCochain K) hK.toExactProjectiveComplex a).trans
        (fullHomTargetStableLinearEquiv (k := k) (a+1) (by omega) hK
          hK.toExactProjectiveComplex).symm)

theorem fullHomSourceDualityAt_symm_apply (a b : ℤ) (hb : b = -a-1)
    (v : CohomologyClass K K b) (u : CohomologyClass K K a) :
    ((τ.fullHomSourceDualityAt hs K hK a b hb).symm v) u =
      ((τ.completeStableDualityAt hs (chainOfCochain K) hK.toExactProjectiveComplex a).symm
        (fullHomTargetStableLinearEquiv (k := k) (a+1) (by omega) hK
          hK.toExactProjectiveComplex v))
        (fullHomSourceStableLinearEquiv (k := k) K K a hK hK.toExactProjectiveComplex u) := rfl

def fullHomSourceDuality (a : ℤ) :
    Module.Dual k (CohomologyClass K K a) ≃ₗ[k] CohomologyClass K K (-a-1) :=
  τ.fullHomSourceDualityAt hs K hK a (-a-1) rfl

theorem fullHomSourceDualityAt_transport (a b : ℤ) (hb : b = -a-1)
    (v : CohomologyClass K K b) :
    (τ.fullHomSourceDualityAt hs K hK a b hb).symm v =
      (τ.fullHomSourceDuality hs K hK a).symm
        (TateKoszul.degreeEquiv (k := k) (CohomologyClass K K) hb v) := by
  subst b
  rfl

variable [CharP k 2]

theorem fullHomSourceDualityAt_product (a n m : ℤ) (hm : m = -(n+a)-1)
    (p : CohomologyClass K K n) (u : CohomologyClass K K a)
    (v : CohomologyClass K K m) :
    ((τ.fullHomSourceDualityAt hs K hK a (m+n) (by omega)).symm
      (fullHomProduct v p)) u =
    ((τ.fullHomSourceDualityAt hs K hK (n+a) m hm).symm v)
      (fullHomProduct p u) := by
  obtain ⟨p,rfl⟩ := CohomologyClass.mk_surjective p
  obtain ⟨u,rfl⟩ := CohomologyClass.mk_surjective u
  obtain ⟨v,rfl⟩ := CohomologyClass.mk_surjective v
  rw [fullHomProduct_mk, fullHomProduct_mk,
    fullHomSourceDualityAt_symm_apply, fullHomSourceDualityAt_symm_apply,
    fullHomTargetStableLinearEquiv_mk, fullHomTargetStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, fullHomSourceStableLinearEquiv_mk]
  rw [targetCocycleMap_eq_reversed (k := k), targetCocycleMap_eq_reversed (k := k),
    sourceCocycleMap_eq_reversed (k := k), sourceCocycleMap_eq_reversed (k := k),
    reversedCokernelMap_product (k := k) v p 0 (n+a+1) (a+1) (by omega) (by omega),
    reversedCokernelMap_product (k := k) p u (n+a) a 0 (by omega) (by omega)]
  exact (τ.completeStableDualityAt_source hs hK.toExactProjectiveComplex
    hK.toExactProjectiveComplex (n+a) a
    (reversedComponent p.val (n+a) a (by omega)).hom
    (reversedCokernelMap (k := k) p (n+a) a (by omega))
    (reversedCokernelMap (k := k) p (n+a+1) (a+1) (by omega))
    (by ext x; rfl) (reversedCokernelMap_syzygy (k := k) p hK.toExactProjectiveComplex
      hK.toExactProjectiveComplex (n+a) a (by omega))
    (StableHom.classOf R _ _ (reversedCokernelMap (k := k) u a 0 (by omega)))
    (StableHom.classOf R _ _ (reversedCokernelMap (k := k) v 0 (n+a+1) (by omega)))).symm

end ArExplicit.FrobeniusTrace

end

end OAI
