import OAI.Algebra.AuslanderReiten.Stable.SourceStableShift
import OAI.Algebra.AuslanderReiten.Cones.CokernelShiftCoordinates
import OAI.Algebra.AuslanderReiten.Resolutions.NatResolutionCochain

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

def sourceCocycleMap (x : Cocycle K L n) :
    Cokernel (chainOfCochain K) n →ₗ[R] Cokernel (chainOfCochain L) 0 :=
  (shiftedCokernelEquiv L 0 0 rfl).toLinearMap.comp
    ((cokernelMap (cocycleComparisonMap (x.leftShift (-n) 0 (by omega))) 0).comp
      (shiftedCokernelEquiv K (-n) n rfl).symm.toLinearMap)

@[simp]
theorem fullHomSourceStableLinearEquiv_mk
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    fullHomSourceStableLinearEquiv (k := k) K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (sourceCocycleMap x) := by
  change StableHom.sourceEquiv (k := k) (shiftedCokernelEquiv K (-n) n rfl).symm
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L 0 0 rfl)
      (fullHomStableEquiv (K⟦-n⟧) L 0 (hK.cochainShift (-n)) (hL.cochainShift 0)
        (CohomologyClass.mk (x.leftShift (-n) 0 (by omega))))) = _
  rw [fullHomStableEquiv_mk, StableHom.targetEquiv_classOf, StableHom.sourceEquiv_classOf]
  rfl

def sourceCocycleComponent (x : Cocycle K L n) :
    (chainOfCochain K).X n ⟶ (chainOfCochain L).X 0 :=
  (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).hom ≫
    x.val.v (-n) 0 (by omega) ≫
      (L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv

theorem sourceCocycleMap_mk [CharP k 2] (x : Cocycle K L n)
    (z : (chainOfCochain K).X n) :
    sourceCocycleMap x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((sourceCocycleComponent x).hom z) := by
  change shiftedCokernelEquiv L 0 0 rfl
    (cokernelMap (cocycleComparisonMap (x.leftShift (-n) 0 (by omega))) 0
      ((shiftedCokernelEquiv K (-n) n rfl).symm (Submodule.Quotient.mk z))) = _
  rw [shiftedCokernelEquiv_symm_mk]
  change shiftedCokernelEquiv L 0 0 rfl
    (Submodule.Quotient.mk
      (((cocycleComparisonMap (x.leftShift (-n) 0 (by omega))).f 0).hom
        ((shiftedCokernelComponent K (-n) n rfl).inv.hom z))) = _
  rw [shiftedCokernelEquiv_mk]
  congr 1
  unfold cocycleComparisonMap
  rw [extendMap_f _ negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rw [cocycleHom_component]
  simp only [Cocycle.leftShift_coe]
  rw [Cochain.leftShift_v _ (-n) 0 (by omega) 0 (0 + 0) rfl (-n) (by omega)]
  rw [ResolutionProducts.intUnit_smul_charTwo (k := k)]
  have hh : (shiftedCokernelComponent K (-n) n rfl).inv ≫
      ((K⟦-n⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom ≫
      (K.shiftFunctorObjXIso (-n) 0 (-n) (by omega)).hom ≫
      x.val.v (-n) 0 (by omega) ≫
      ((L⟦(0 : ℤ)⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv ≫
      (shiftedCokernelComponent L 0 0 rfl).hom = sourceCocycleComponent x := by
    dsimp only [shiftedCokernelComponent, sourceCocycleComponent]
    erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_hom, Iso.trans_hom]
    simp only [Iso.symm_inv, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      CochainComplex.shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom]
    erw [Category.id_comp]
  exact congrArg (fun f : (chainOfCochain K).X n ⟶ (chainOfCochain L).X 0 => f.hom z) hh

end ArExplicit.CompleteComparison

end

end OAI
