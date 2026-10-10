import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem cocycleHom_ofHom {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ 0 rfl f := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [CompleteComparison.cocycleHom_component, Cocycle.ofHom_coe]
  simp only [ShiftedHom.mk₀, HomologicalComplex.comp_f, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
    CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
  change (Cochain.ofHom f).v i (i+0) rfl =
    f.f i ≫ (L.XIsoOfEq (show i=i+0 by omega)).hom
  simpa only [Cochain.ofHom_v] using
    (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom f) i i (i+0) (add_zero i) (by omega)).symm

variable [HasDerivedCategory C] [HasExt.{v} C]

theorem endExt_identity {X : C} (P : ProjectiveResolution X) :
    endExt P (Cocycle.ofHom (𝟙 P.cochainComplex)) = Ext.mk₀ (𝟙 X) := by
  apply Ext.homEquiv.injective
  change (endExt P (Cocycle.ofHom (𝟙 P.cochainComplex))).hom = (Ext.mk₀ (𝟙 X)).hom
  rw [endExt_hom, cocycleHom_ofHom, Ext.mk₀_hom]
  erw [ShiftedHom.map_mk₀]
  simp [conjugate, ShiftedHom.mk₀, ← NatTrans.naturality]

theorem extMk_augmentation {X : C} (P : ProjectiveResolution X) :
    P.extMk (Y := X) (P.π.f 0) 1 rfl P.complex_d_comp_π_f_zero = Ext.mk₀ (𝟙 X) := by
  rw [← endExt_identity P, endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show (0 : ℤ)+0=0 by omega)).injective
  change (Cochain.toSingleMk ((P.cochainComplexXIso 0 0 rfl).hom ≫ P.π.f 0)
      (by omega : (0 : ℤ)+0=0)).v 0 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
    ((Cochain.ofHom (𝟙 P.cochainComplex)).comp (Cochain.ofHom P.π') (add_zero 0)).v 0 0
      (by omega) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.id_comp, Cochain.ofHom_v, Cochain.toSingleMk_v, P.π'_f_zero]
  dsimp only [ChainComplex.single₀_obj_zero]
  exact congrArg (fun morphism =>
      morphism ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom)
    (Category.assoc (P.cochainComplexXIso 0 0 rfl).hom (P.π.f 0)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv)

end ArExplicit.ResolutionProducts

end

end OAI
