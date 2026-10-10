import OAI.Algebra.AuslanderReiten.Cocycles.ReversedCocycleMap

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

def fullHomTargetStableLinearEquiv (b : ℤ) (hb : n = -b)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) b) :=
  (fullHomStableLinearEquiv K L n hK (hL.cochainShift n)).trans
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L n b hb))

def targetCocycleMap (x : Cocycle K L n) (b : ℤ) (hb : n = -b) :
    Cokernel (chainOfCochain K) 0 →ₗ[R] Cokernel (chainOfCochain L) b :=
  (shiftedCokernelEquiv L n b hb).toLinearMap.comp
    (cokernelMap (cocycleComparisonMap x) 0)

@[simp] theorem fullHomTargetStableLinearEquiv_mk (b : ℤ) (hb : n = -b)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    fullHomTargetStableLinearEquiv (k := k) b hb hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (targetCocycleMap x b hb) := by
  change StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L n b hb)
    (fullHomStableEquiv K L n hK (hL.cochainShift n) (CohomologyClass.mk x)) = _
  rw [fullHomStableEquiv_mk, StableHom.targetEquiv_classOf]
  rfl

@[reassoc] private theorem component_transport (x : Cochain K L n)
    (p q r : ℤ) (hpq : p + n = q) (hqr : q = r) :
    x.v p q hpq ≫ (L.XIsoOfEq hqr).hom = x.v p r (hpq.trans hqr) := by
  subst r
  simp

theorem targetCocycleMap_mk (x : Cocycle K L n) (b : ℤ) (hb : n = -b)
    (z : (chainOfCochain K).X 0) :
    targetCocycleMap x b hb (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((reversedComponent x.val 0 b (by omega)).hom z) := by
  change shiftedCokernelEquiv L n b hb
    (Submodule.Quotient.mk (((cocycleComparisonMap x).f 0).hom z)) = _
  rw [shiftedCokernelEquiv_mk]
  congr 1
  unfold cocycleComparisonMap
  rw [extendMap_f _ negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rw [cocycleHom_component]
  have he :
      (K.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom ≫
        x.val.v 0 (0+n) rfl ≫
          ((L⟦n⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv ≫
            (shiftedCokernelComponent L n b hb).hom = reversedComponent x.val 0 b (by omega) := by
    subst n
    dsimp only [shiftedCokernelComponent, reversedComponent]
    erw [Iso.trans_hom, Iso.trans_hom]
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
    simp only [CochainComplex.shiftFunctorObjXIso, Int.neg_zero]
    erw [component_transport_assoc]
  exact congrArg (fun f => f.hom z) he

variable [CharP k 2]
include k

theorem targetCocycleMap_eq_reversed (x : Cocycle K L n) (b : ℤ) (hb : n = -b) :
    targetCocycleMap x b hb = reversedCokernelMap (k := k) x 0 b (by omega) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [targetCocycleMap_mk, reversedCokernelMap_mk]

end ArExplicit.CompleteComparison

end

end OAI
