import OAI.Algebra.AuslanderReiten.Cones.CokernelShift

namespace OAI

open CategoryTheory HomologicalComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]

@[simp]
theorem cokernelOpcyclesEquiv_mk (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : P.X n) :
    cokernelOpcyclesEquiv P n (Submodule.Quotient.mk x) = (P.pOpcycles n).hom x := by
  apply (cokernelOpcyclesEquiv P n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f : P.X n ⟶ ModuleCat.of R (Cokernel P n) => f.hom x)
    (show P.pOpcycles n ≫ (P.opcyclesIsoSc' (n + 1) n (n - 1)
      (ChainComplex.prev ℤ n) (ChainComplex.next ℤ n)).hom ≫
        (P.sc' (n + 1) n (n - 1)).moduleCatOpcyclesIso.hom =
          ModuleCat.ofHom (LinearMap.range (P.d (n + 1) n).hom).mkQ by
      rw [pOpcycles_opcyclesIsoSc'_hom_assoc]
      exact ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom _)
  exact h.symm

@[simp]
theorem cochainCokernelEquiv_mk (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (chainOfCochain K).X n) :
    cochainCokernelEquiv K n (Submodule.Quotient.mk x) =
      (K.pOpcycles (-n)).hom
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).hom.hom x) := by
  change (K.extendOpcyclesIso negIndexEmbedding (neg_neg n)).hom.hom
    (cokernelOpcyclesEquiv (chainOfCochain K) n (Submodule.Quotient.mk x)) = _
  rw [cokernelOpcyclesEquiv_mk]
  exact congrArg (fun f : (chainOfCochain K).X n ⟶ K.opcycles (-n) => f.hom x)
    (pOpcycles_extendOpcyclesIso_hom K negIndexEmbedding (neg_neg n))

noncomputable def shiftedCokernelComponent (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) :
    (chainOfCochain (K⟦a⟧)).X 0 ≅ (chainOfCochain K).X n :=
  (K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl ≪≫
    K.shiftFunctorObjXIso a 0 (-n) (by omega) ≪≫
      (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).symm

@[simp]
theorem shiftedCokernelEquiv_mk (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) (x : (chainOfCochain (K⟦a⟧)).X 0) :
    shiftedCokernelEquiv K a n ha (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((shiftedCokernelComponent K a n ha).hom.hom x) := by
  apply (cochainCokernelEquiv K n).injective
  change cochainCokernelEquiv K n ((cochainCokernelEquiv K n).symm _) = _
  rw [LinearEquiv.apply_symm_apply, cochainCokernelEquiv_mk]
  erw [cochainCokernelEquiv_mk]
  have h := congrArg (fun f : (K⟦a⟧).X 0 ⟶ K.opcycles (-n) =>
      f.hom (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x))
    (ShortComplex.p_opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K))
  change (ShortComplex.opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K)).hom
      (((K⟦a⟧).pOpcycles 0).hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) =
      (K.pOpcycles (-n)).hom
        ((K.shiftFunctorObjXIso a 0 (-n) (by omega)).hom.hom
          (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) at h
  change (ShortComplex.opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K)).hom
      (((K⟦a⟧).pOpcycles 0).hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) = _
  rw [h]
  congr 1
  change _ = (K.extendXIso negIndexEmbedding (neg_neg n)).hom.hom
    ((K.extendXIso negIndexEmbedding (neg_neg n)).inv.hom
      ((K.shiftFunctorObjXIso a 0 (-n) (by omega)).hom.hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)))
  exact (Iso.inv_hom_id_apply _ _).symm

@[simp]
theorem shiftedCokernelEquiv_symm_mk (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) (x : (chainOfCochain K).X n) :
    (shiftedCokernelEquiv K a n ha).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((shiftedCokernelComponent K a n ha).inv.hom x) := by
  apply (shiftedCokernelEquiv K a n ha).injective
  rw [LinearEquiv.apply_symm_apply, shiftedCokernelEquiv_mk]
  congr 1
  exact (Iso.inv_hom_id_apply _ _).symm

end ArExplicit.CompleteComparison

end OAI
