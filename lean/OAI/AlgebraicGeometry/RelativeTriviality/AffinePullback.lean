import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.Cotangent.Affine
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u
variable (R S : CommRingCat.{u}) (φ : R ⟶ S)

 

def specGlobalPushforwardIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine LinearEquiv.toModuleIso
      (X₁ := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M))
      (X₂ := (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M))
      (m₁ := ModuleCat.isModule (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj M)))
      (m₂ := ModuleCat.isModule ((ModuleCat.restrictScalars φ.hom).obj
        (moduleSpecΓFunctor.obj M)))
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := ?_ }
    intro r m
    change Γ(M, ⊤) at m
    change (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) • m =
      (Scheme.ΓSpecIso S).inv (φ r) • m
    exact congrArg (fun a => a • m)
      (CategoryTheory.congr_fun (Scheme.ΓSpecIso_inv_naturality φ).symm r)
  · intro M N f
    ext x
    rfl

 

def tildePullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight (specGlobalPushforwardIso R S φ)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)

 
def affinePullbackAdjunction :=
  (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
    (specGlobalPushforwardIso R S φ)

lemma tildePullbackIso_homEquiv (M : ModuleCat R) (N : ModuleCat S)
    (g : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) :
    (affinePullbackAdjunction R S φ).homEquiv M (tilde N)
      ((tildePullbackIso R S φ).hom.app M ≫ tilde.map g) =
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).homEquiv
      M (tilde N) (tilde.map g) := by
  erw [Adjunction.homEquiv_naturality_right]
  change (affinePullbackAdjunction R S φ).homEquiv _ _
    (((affinePullbackAdjunction R S φ).leftAdjointUniq
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)).hom.app M) ≫ _ = _
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]

lemma tilde_homEquiv_apply (M : ModuleCat R) (N : (Spec R).Modules)
    (f : tilde M ⟶ N) (m : M) :
    tilde.adjunction.homEquiv M N f m = f.val.app (op ⊤) (tilde.toOpen M ⊤ m) := by
  erw [Adjunction.homEquiv_unit]
  rfl

lemma affinePullback_homEquiv_apply (M : ModuleCat R) (N : (Spec S).Modules)
    (f : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶ N) (m : M) :
    (affinePullbackAdjunction R S φ).homEquiv M N f m =
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ f).val.app
      (op ⊤) (tilde.toOpen M ⊤ m) := by
  erw [affinePullbackAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  change tilde.adjunction.homEquiv M _
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ f) m = _
  exact tilde_homEquiv_apply R _ _ _ _

lemma extendTilde_homEquiv_apply (M : ModuleCat R) (N : ModuleCat S)
    (g : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).homEquiv
      M (tilde N) (tilde.map g) m =
    tilde.toOpen N ⊤ (g (ModuleCat.extendRestrictScalarsAdj φ.hom |>.unit.app M m)) := by
  rw [Adjunction.comp_homEquiv]
  change (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
    (tilde.adjunction.homEquiv _ _ (tilde.map g)) m = _
  erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, tilde_homEquiv_apply]
  exact CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) _

end CampanaPeternellSix.Cotangent.Affine

namespace CampanaPeternellSix.AffineBaseChange
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable (R S : CommRingCat.{u}) (φ : R ⟶ S)
 

def sectionMap (E : (Spec R).Modules) :
      moduleSpecΓFunctor.obj E →ₛₗ[φ.hom]
        moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj E) where
  toFun m := ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).val.app
    (op ⊤) m
  map_add' := map_add _
  map_smul' r m := by
    change Γ(E, ⊤) at m
    change ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).val.app
      (op ⊤) (((Scheme.ΓSpecIso R).inv r) • m) = _
    let η : E ⟶ (Scheme.Modules.pushforward (Spec.map φ)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj E) :=
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app E
    have hη := Scheme.Modules.Hom.app_smul η ((Scheme.ΓSpecIso R).inv r) m
    erw [hη]
    let n : Γ((Scheme.Modules.pullback (Spec.map φ)).obj E, ⊤) :=
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).val.app (op ⊤) m
    change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • n =
      ((Scheme.ΓSpecIso S).inv (φ r)) • n
    exact congrArg (fun a => a • n)
      (CategoryTheory.congr_fun (Scheme.ΓSpecIso_inv_naturality φ).symm r)

open Cotangent.Affine

def globalPullbackIso (E : (Spec R).Modules) [E.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj E) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj E) := by
  let iso : tilde (moduleSpecΓFunctor.obj E) ≅ E :=
    @asIso _ _ _ _ E.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E)
  exact tilde.toTildeΓNatIso.app _ ≪≫
    moduleSpecΓFunctor.mapIso ((tildePullbackIso R S φ).app _).symm ≪≫
    moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso iso)

lemma tilde_unit_comparison (M : ModuleCat R) (m : M) :
    ((tildePullbackIso R S φ).hom.app M).val.app (op ⊤)
      (sectionMap R S φ (tilde M) (tilde.toOpen M ⊤ m)) =
    tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m) := by
  have h := congrArg (fun f => f m)
    (tildePullbackIso_homEquiv R S φ M ((ModuleCat.extendScalars φ.hom).obj M)
      (𝟙 ((ModuleCat.extendScalars φ.hom).obj M)))
  erw [affinePullback_homEquiv_apply R S φ M
    (tilde ((ModuleCat.extendScalars φ.hom).obj M))
    ((tildePullbackIso R S φ).hom.app M ≫
      tilde.map (𝟙 ((ModuleCat.extendScalars φ.hom).obj M))) m,
    extendTilde_homEquiv_apply R S φ M ((ModuleCat.extendScalars φ.hom).obj M)
      (𝟙 ((ModuleCat.extendScalars φ.hom).obj M)) m] at h
  have h_id : tilde.map (𝟙 ((ModuleCat.extendScalars φ.hom).obj M)) = 𝟙 _ :=
    (tilde.functor S).map_id _
  erw [h_id] at h
  erw [Category.comp_id, Adjunction.homEquiv_unit] at h
  exact h

lemma sectionMap_naturality {E F : (Spec R).Modules} (f : E ⟶ F)
    (m : moduleSpecΓFunctor.obj E) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map f))
      (sectionMap R S φ E m) =
    sectionMap R S φ F (moduleSpecΓFunctor.map f m) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality f
  exact congrArg (fun g => g.val.app (op ⊤) m) h.symm

lemma counit_top (E : (Spec R).Modules) (m : moduleSpecΓFunctor.obj E) :
    moduleSpecΓFunctor.map E.fromTildeΓ
       (tilde.toOpen (moduleSpecΓFunctor.obj E) ⊤ m) = m := by
  have h := tilde.adjunction.right_triangle_components E
  exact congrArg (fun g => g m) h

lemma globalPullbackIso_one (E : (Spec R).Modules) [E.IsQuasicoherent]
    (m : moduleSpecΓFunctor.obj E) :
    (globalPullbackIso R S φ E).hom
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj E) m) =
    sectionMap R S φ E m := by
  change moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map E.fromTildeΓ)
    (((tildePullbackIso R S φ).inv.app (moduleSpecΓFunctor.obj E)).val.app (op ⊤)
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj E)) ⊤
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj E) m))) = _
  rw [← tilde_unit_comparison R S φ]
  have h : ((tildePullbackIso R S φ).inv.app (moduleSpecΓFunctor.obj E)).val.app (op ⊤)
      (((tildePullbackIso R S φ).hom.app (moduleSpecΓFunctor.obj E)).val.app (op ⊤)
        (sectionMap R S φ (tilde (moduleSpecΓFunctor.obj E))
          (tilde.toOpen (moduleSpecΓFunctor.obj E) ⊤ m))) =
      sectionMap R S φ (tilde (moduleSpecΓFunctor.obj E))
          (tilde.toOpen (moduleSpecΓFunctor.obj E) ⊤ m) := by
    exact congrArg (fun f => f.val.app (op ⊤)
      (sectionMap R S φ (tilde (moduleSpecΓFunctor.obj E))
        (tilde.toOpen (moduleSpecΓFunctor.obj E) ⊤ m)))
      ((tildePullbackIso R S φ).app (moduleSpecΓFunctor.obj E)).hom_inv_id
  rw [h]
  exact (sectionMap_naturality R S φ E.fromTildeΓ
    (tilde.toOpen (moduleSpecΓFunctor.obj E) ⊤ m)).trans
    (congrArg (sectionMap R S φ E) (counit_top R E m))

 
theorem isBaseChange_sections (E : (Spec R).Modules) [E.IsQuasicoherent] :
    letI : Algebra R S := φ.hom.toAlgebra
    let N := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj E)
    letI : Module R N := Module.compHom N φ.hom
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S
      ({ toFun := sectionMap R S φ E
         map_add' := map_add _
         map_smul' := fun r m => (sectionMap R S φ E).map_smul' r m } :
        moduleSpecΓFunctor.obj E →ₗ[R] N) := by
  let : Algebra R S := φ.hom.toAlgebra
  let N := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj E)
  let : Module R N := Module.compHom N φ.hom
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact IsBaseChange.of_equiv (globalPullbackIso R S φ E).toLinearEquiv
    (globalPullbackIso_one R S φ E)
end CampanaPeternellSix.AffineBaseChange

end

end OAI
