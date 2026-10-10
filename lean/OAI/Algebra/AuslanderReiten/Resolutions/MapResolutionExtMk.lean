import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExt
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

omit [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v'} D] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
private theorem map_eval_cancel {U V W Z : C} {U' Z' : D}
    (a : U' ⟶ F.obj U) (b : U ⟶ V) (f : V ⟶ W) (e : Z ≅ W) (t : Z' ≅ F.obj W) :
    (a ≫ F.map ((b ≫ f) ≫ e.inv) ≫ (F.map e.hom ≫ t.inv)) ≫ t.hom =
      (a ≫ F.map b) ≫ F.map f := by
  simp only [Functor.map_comp, Category.assoc, t.inv_hom_id, Category.comp_id]
  rw [← F.map_comp e.inv e.hom, e.inv_hom_id, F.map_id, Category.comp_id]

omit [HasExt.{v} C] [HasExt.{v'} D] in
theorem mappedResolutionCocycle_eq
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    mappedResolutionCocycle F P x =
      ((fullHomCocycleMap F _ _ _ x).precomp (mapResolutionCochainIso F P).hom).postcomp
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y) := by
  apply Cocycle.equivHomShift.symm.injective
  rw [mappedResolutionCocycle, AddEquiv.symm_apply_apply,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp, cocycle_map_hom]
  exact (Category.assoc _ _ _).symm

omit [HasExt.{v} C] [HasExt.{v'} D] in
theorem mappedResolutionCocycle_v
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ))
    (i j : ℤ) (hij : i+n=j) :
    (mappedResolutionCocycle F P x).val.v i j hij =
      (mapResolutionCochainIso F P).hom.f i ≫ F.map (x.val.v i j hij) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y).f j := by
  rw [mappedResolutionCocycle_eq]
  change (((Cochain.ofHom _).comp (x.val.map F) (zero_add (n : ℤ))).comp
    (Cochain.ofHom _) (add_zero (n : ℤ))).v i j hij = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.map_v]
  exact Category.assoc _ _ _

theorem map_extMk (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mapResolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map (P.complex.d (n+1) n) ≫ F.map f = 0
            rw [← F.map_comp, hf, F.map_zero]) := by
  unfold ProjectiveResolution.extMk
  rw [map_extOfCocycle]
  apply congrArg (mapResolution F P).extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  apply (Cochain.toSingleEquiv (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by omega)).injective
  rw [Cocycle.toSingleMk_coe, Cochain.toSingleEquiv_toSingleMk]
  change (mappedResolutionCocycle F P _).val.v (-(n : ℤ)) 0 (by omega) ≫
    (singleObjXSelf (.up ℤ) 0 (F.obj Y)).hom = _
  rw [mappedResolutionCocycle_v, Cocycle.toSingleMk_coe, Cochain.toSingleMk_v]
  change ((mapResolutionCochainIso F P).hom.f (-(n : ℤ)) ≫
    F.map (((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f) ≫
      (singleObjXSelf (.up ℤ) 0 Y).inv) ≫
      ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app Y).f 0) ≫
        (singleObjXSelf (.up ℤ) 0 (F.obj Y)).hom = _
  rw [singleMapHomologicalComplex_hom_app_self]
  exact (map_eval_cancel F ((mapResolutionCochainIso F P).hom.f (-(n : ℤ)))
    (P.cochainComplexXIso (-(n : ℤ)) n rfl).hom f
    (singleObjXSelf (.up ℤ) 0 Y) (singleObjXSelf (.up ℤ) 0 (F.obj Y))).trans
      (congrArg (fun g => g ≫ F.map f) (mapResolutionCochainIso_coordinate F P _ n rfl))

end ArExplicit.ResolutionProducts

end

end OAI
