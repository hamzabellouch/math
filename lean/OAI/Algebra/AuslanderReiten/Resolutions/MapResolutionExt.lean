import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionCochain
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Localization
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

def mappedResolutionCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    Cocycle (mapResolution F P).cochainComplex
      ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) (n : ℤ) :=
  Cocycle.equivHomShift ((mapResolutionCochainIso F P).hom ≫
    ShiftedHom.map (Cocycle.equivHomShift.symm x) (F.mapHomologicalComplex (.up ℤ)) ≫
      ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧')

theorem precomp_extOfCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (SmallShiftedHom.mk₀ (quasiIso C (.up ℤ)) 0 rfl P.π').comp
      (P.extEquivCohomologyClass.symm (CohomologyClass.mk x)) (add_zero (n : ℤ)) =
        SmallShiftedHom.mk (quasiIso C (.up ℤ)) (Cocycle.equivHomShift.symm x) := by
  have hπ : quasiIso C (.up ℤ) P.π' := by rw [mem_quasiIso_iff]; infer_instance
  change (SmallShiftedHom.precompEquiv P.π' hπ)
    ((SmallShiftedHom.precompEquiv P.π' hπ).symm
      (CohomologyClass.equivOfIsKProjective (CohomologyClass.mk x))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem map_extOfCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (P.extEquivCohomologyClass.symm (CohomologyClass.mk x)).mapExactFunctor F =
      (mapResolution F P).extEquivCohomologyClass.symm
        (CohomologyClass.mk (mappedResolutionCocycle F P x)) := by
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let eP : (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex ≅
      (mapResolution F P).cochainComplex := (mapResolutionCochainIso F P).symm
  let eX : (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X) ≅
      (CochainComplex.singleFunctor D 0).obj (F.obj X) := (F.mapCochainComplexSingleFunctor 0).app X
  let eY : (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj Y) ≅
      (CochainComplex.singleFunctor D 0).obj (F.obj Y) := (F.mapCochainComplexSingleFunctor 0).app Y
  have h := congrArg (fun z => Φ.smallShiftedHomMap eP eY z) (precomp_extOfCocycle P x)
  erw [Φ.smallShiftedHomMap_comp eP eX eY,
    Φ.smallShiftedHomMap_mk₀ eP eX, Φ.smallShiftedHomMap_mk eP eY] at h
  have hπ : eP.inv ≫ Φ.functor.map P.π' ≫ eX.hom = (mapResolution F P).π' :=
    mapResolutionCochainIso_π F P
  erw [hπ] at h
  apply (SmallShiftedHom.precompEquiv (mapResolution F P).π'
    (by rw [mem_quasiIso_iff]; infer_instance)).injective
  change (SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) 0 rfl (mapResolution F P).π').comp
    _ (add_zero (n : ℤ)) =
      (SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) 0 rfl (mapResolution F P).π').comp
        ((mapResolution F P).extEquivCohomologyClass.symm
          (CohomologyClass.mk (mappedResolutionCocycle F P x))) (add_zero (n : ℤ))
  have hpost := precomp_extOfCocycle (mapResolution F P) (mappedResolutionCocycle F P x)
  refine h.trans (Eq.trans ?_ hpost.symm)
  apply congrArg (SmallShiftedHom.mk (quasiIso D (.up ℤ)))
  rw [mappedResolutionCocycle, AddEquiv.symm_apply_apply]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
