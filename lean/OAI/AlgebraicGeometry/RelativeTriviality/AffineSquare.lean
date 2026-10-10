import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.AffinePullback

namespace OAI

noncomputable section

namespace CampanaPeternellSix.AffineSquare
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} {A B : CommRingCat.{u}}
  (g : X ⟶ Y) (i : Spec A ⟶ Y) (j : Spec B ⟶ X) (φ : A ⟶ B)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (h : Spec.map φ ≫ i = j ≫ g)
open Scheme.Modules

private theorem section_square_unit {C : Type*} [Category C] {P Q T W Z : C}
    (p : P ⟶ Q) (s : Q ⟶ P) (q₀ : P ⟶ T) (q₁ : Q ⟶ W) (t : W ⟶ T)
    (η : P ⟶ Z) (l : Z ⟶ W) (r : Z ⟶ T)
    (hunit : p ≫ s = 𝟙 P) (hn : s ≫ q₀ = q₁ ≫ t)
    (hc : p ≫ q₁ = η ≫ l) (hr : l ≫ t = r) : q₀ = η ≫ r := by
  calc
    q₀ = (p ≫ s) ≫ q₀ := by rw [hunit, Category.id_comp]
    _ = p ≫ (q₁ ≫ t) := by rw [Category.assoc, hn]
    _ = (η ≫ l) ≫ t := by rw [← Category.assoc, hc]
    _ = η ≫ r := by rw [Category.assoc, hr]

def pushforwardSquare :
    pushforward (Spec.map φ) ⋙ pushforward i ≅ pushforward j ⋙ pushforward g :=
  pushforwardComp (Spec.map φ) i ≪≫ pushforwardCongr h ≪≫ (pushforwardComp j g).symm

def squareAdjunction :=
  ((pullbackPushforwardAdjunction g).comp (restrictAdjunction j)).ofNatIsoRight
    (pushforwardSquare g i j φ h).symm

def restrictionPullbackIso :
    restrictFunctor i ⋙ pullback (Spec.map φ) ≅ pullback g ⋙ restrictFunctor j :=
  ((restrictAdjunction i).comp (pullbackPushforwardAdjunction (Spec.map φ))).leftAdjointUniq
    (squareAdjunction g i j φ h)

lemma restrictionPullbackIso_unit (E : Y.Modules) :
    (((restrictAdjunction i).comp (pullbackPushforwardAdjunction (Spec.map φ))).unit.app E) ≫
      (pushforward (Spec.map φ) ⋙ pushforward i).map
        ((restrictionPullbackIso g i j φ h).hom.app E) =
      (squareAdjunction g i j φ h).unit.app E :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ E

lemma comparison_unit (E : Y.Modules) (U : Y.Opens)
    (hij : j ''ᵁ (Spec.map φ ⁻¹ᵁ i ⁻¹ᵁ U) ≤ g ⁻¹ᵁ U) :
    E.presheaf.map (homOfLE (i.image_preimage_le U)).op ≫
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        ((restrictFunctor i).obj E)).app (i ⁻¹ᵁ U) ≫
      ((restrictionPullbackIso g i j φ h).hom.app E).app (Spec.map φ ⁻¹ᵁ i ⁻¹ᵁ U) =
    ((pullbackPushforwardAdjunction g).unit.app E).app U ≫
      ((pullback g).obj E).presheaf.map (homOfLE hij).op := by
  have hh := congrArg (fun f => f.app U) (restrictionPullbackIso_unit g i j φ h E)
  have hu : (squareAdjunction g i j φ h).unit.app E =
      ((pullbackPushforwardAdjunction g).comp (restrictAdjunction j)).unit.app E ≫
        (pushforwardSquare g i j φ h).inv.app
          ((pullback g ⋙ restrictFunctor j).obj E) := rfl
  rw [hu] at hh
  simp only [Adjunction.comp_unit_app, Hom.comp_app, Functor.comp_map,
    pushforward_map_app, restrictAdjunction_unit_app_app,
    pushforwardSquare, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    pushforwardComp_inv_app_app, pushforwardComp_hom_app_app,
    pushforwardCongr_inv_app_app, Hom.comp_app, Category.assoc] at hh
  change _ = ((pullbackPushforwardAdjunction g).unit.app E).app U ≫
    ((pullback g).obj E).presheaf.map (homOfLE (j.image_preimage_le (g ⁻¹ᵁ U))).op ≫
      ((pullback g).obj E).presheaf.map
        (j.opensFunctor.map (eqToHom (congrArg (fun k : Spec B ⟶ Y => k ⁻¹ᵁ U) h))).op at hh
  erw [← Functor.map_comp, ← op_comp] at hh
  exact hh

lemma restriction_maps_comp (E : Y.Modules) (V W : (Spec A).Opens) (U : Y.Opens)
    (h₁ : i ''ᵁ V ≤ U) (h₂ : W ≤ V) (h₃ : i ''ᵁ W ≤ U) :
    E.presheaf.map (homOfLE h₁).op ≫ (E.restrict i).presheaf.map (homOfLE h₂).op =
      E.presheaf.map (homOfLE h₃).op := by
  change E.presheaf.map (homOfLE h₁).op ≫
    E.presheaf.map (i.opensFunctor.map (homOfLE h₂)).op = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma restriction_unit_top (E : Y.Modules) :
    E.presheaf.map (homOfLE (i.image_preimage_le (i ''ᵁ ⊤))).op ≫
      (E.restrict i).presheaf.map (homOfLE (i.preimage_image_eq ⊤).ge).op =
        𝟙 Γ(E, i ''ᵁ ⊤) := by
  rw [restriction_maps_comp i E _ _ _ _ _ le_rfl]
  change E.presheaf.map (𝟙 (op (i ''ᵁ ⊤))) = _
  exact E.presheaf.map_id _

lemma comparison_unit_top (E : Y.Modules)
    (hij : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ (i ''ᵁ ⊤)) :
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        ((restrictFunctor i).obj E)).app ⊤ ≫
      ((restrictionPullbackIso g i j φ h).hom.app E).app ⊤ =
    ((pullbackPushforwardAdjunction g).unit.app E).app (i ''ᵁ ⊤) ≫
      ((pullback g).obj E).presheaf.map (homOfLE hij).op := by
  let U : Y.Opens := i ''ᵁ ⊤
  let V : (Spec A).Opens := i ⁻¹ᵁ U
  have hv : ⊤ ≤ V := (i.preimage_image_eq ⊤).ge
  let τ : (⊤ : (Spec A).Opens) ⟶ V := homOfLE hv
  let F := (pullback g).obj E
  let q : E.restrict i ⟶ (pushforward (Spec.map φ)).obj (F.restrict j) :=
    (pullbackPushforwardAdjunction (Spec.map φ)).unit.app _ ≫
      (pushforward (Spec.map φ)).map ((restrictionPullbackIso g i j φ h).hom.app E)
  have hn := q.mapPresheaf.naturality τ.op
  change (E.restrict i).presheaf.map τ.op ≫ q.app ⊤ =
    q.app V ≫ ((pushforward (Spec.map φ)).obj (F.restrict j)).presheaf.map τ.op at hn
  have hle : j ''ᵁ (Spec.map φ ⁻¹ᵁ V) ≤ g ⁻¹ᵁ U := by
    have he : Spec.map φ ⁻¹ᵁ V = j ⁻¹ᵁ g ⁻¹ᵁ U :=
      congrArg (fun k : Spec B ⟶ Y => k ⁻¹ᵁ U) h
    rw [he]
    exact j.image_preimage_le _
  have hc := comparison_unit g i j φ h E U hle
  change E.presheaf.map (homOfLE (i.image_preimage_le U)).op ≫ q.app V =
     ((pullbackPushforwardAdjunction g).unit.app E).app U ≫
       F.presheaf.map (homOfLE hle).op at hc
  change q.app ⊤ = _
  exact section_square_unit
    (E.presheaf.map (homOfLE (i.image_preimage_le U)).op)
    ((E.restrict i).presheaf.map τ.op) (q.app ⊤) (q.app V)
    (((pushforward (Spec.map φ)).obj (F.restrict j)).presheaf.map τ.op)
    (((pullbackPushforwardAdjunction g).unit.app E).app U)
    (F.presheaf.map (homOfLE hle).op) (F.presheaf.map (homOfLE hij).op)
    (restriction_unit_top i E) hn hc
    (restriction_maps_comp j F _ _ _ hle
      (show Spec.map φ ⁻¹ᵁ ⊤ ≤ Spec.map φ ⁻¹ᵁ V from fun x hx => hv trivial) hij)

end

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {X Y : Scheme.{u}} {A B : CommRingCat.{u}}
  (g : X ⟶ Y) (i : Spec A ⟶ Y) (j : Spec B ⟶ X) (φ : A ⟶ B)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (h : Spec.map φ ≫ i = j ≫ g)

def sectionMap (E : Y.Modules) :
    moduleSpecΓFunctor.obj (E.restrict i) →ₛₗ[φ.hom]
      moduleSpecΓFunctor.obj (((pullback g).obj E).restrict j) :=
  (moduleSpecΓFunctor.map ((restrictionPullbackIso g i j φ h).hom.app E)).hom.comp
    (AffineBaseChange.sectionMap A B φ (E.restrict i))

include h in
lemma image_top_le_preimage : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ (i ''ᵁ ⊤) := by
  rintro x ⟨y,hy,rfl⟩
  change (j ≫ g) y ∈ i ''ᵁ ⊤
  rw [← h]
  exact ⟨(Spec.map φ) y, trivial, rfl⟩

lemma sectionMap_apply (E : Y.Modules) (m : moduleSpecΓFunctor.obj (E.restrict i)) :
    sectionMap g i j φ h E m =
      ((pullback g).obj E).presheaf.map
        (homOfLE (image_top_le_preimage g i j φ h)).op
          (((pullbackPushforwardAdjunction g).unit.app E).app (i ''ᵁ ⊤) m) := by
  have he := comparison_unit_top g i j φ h E (image_top_le_preimage g i j φ h)
  have hv := ConcreteCategory.congr_hom he m
  change _ = _ at hv
  dsimp only [sectionMap, LinearMap.comp_apply]
  exact hv

lemma isBaseChange_sections (E : Y.Modules) [E.IsQuasicoherent] :
    letI : Algebra A B := φ.hom.toAlgebra
    let N := moduleSpecΓFunctor.obj (((pullback g).obj E).restrict j)
    letI : Module A N := Module.compHom N φ.hom
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange B
      ({ toFun := sectionMap g i j φ h E
         map_add' := map_add _
         map_smul' := fun a m => (sectionMap g i j φ h E).map_smul' a m } :
        moduleSpecΓFunctor.obj (E.restrict i) →ₗ[A] N) := by
  let : Algebra A B := φ.hom.toAlgebra
  let N := moduleSpecΓFunctor.obj (((pullback g).obj E).restrict j)
  let : Module A N := Module.compHom N φ.hom
  let : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj (E.restrict i)) ≅ N :=
    AffineBaseChange.globalPullbackIso A B φ (E.restrict i) ≪≫
       moduleSpecΓFunctor.mapIso ((restrictionPullbackIso g i j φ h).app E)
  apply IsBaseChange.of_equiv (N := N) e.toLinearEquiv
  intro m
  change (moduleSpecΓFunctor.map ((restrictionPullbackIso g i j φ h).hom.app E))
    ((AffineBaseChange.globalPullbackIso A B φ (E.restrict i)).hom
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m)) = _
  rw [AffineBaseChange.globalPullbackIso_one]
  rfl
end CampanaPeternellSix.AffineSquare

namespace CampanaPeternellSix.RelativeCech
open scoped TensorProduct
universe u v
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  (M N : Type v) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module S N] [Module A N] [Module B N]
  [IsScalarTower R S N] [IsScalarTower R A N]
  [IsScalarTower S B N] [IsScalarTower A B N]

lemma isBaseChange_restrictScalars (f : M →ₗ[A] N) (hf : IsBaseChange B f) :
    IsBaseChange S (f.restrictScalars R) := by
  apply IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange R S A B M).symm ≪≫ₗ
      hf.equiv.restrictScalars S)
  intro x
  simp only [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
    map_one, LinearEquiv.restrictScalars_apply, hf.equiv_tmul, one_smul]
  rfl
end CampanaPeternellSix.RelativeCech

namespace CampanaPeternellSix.AffineSquare
section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  {X Y : Scheme.{u}} (g : X ⟶ Y) (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (h : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i = j ≫ g)

lemma isBaseChange_sections_overBase (E : Y.Modules) [E.IsQuasicoherent] :
    let M : ModuleCat.{u} A := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (E.restrict i)
    let N : ModuleCat.{u} B := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj (((pullback g).obj E).restrict j)
    letI : Module B N := N.isModule
    letI : Module A M := M.isModule
    letI : Module R M := Module.compHom M (algebraMap R A)
    letI : Module R N := Module.compHom N (algebraMap R B)
    letI : Module S N := Module.compHom N (algebraMap S B)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (R := R) (A := S) (M := N) (fun (r : R) (m : N) => by
      change ((algebraMap S B (algebraMap R S r)) • m : N) = ((algebraMap R B r) • m : N)
      rw [← IsScalarTower.algebraMap_apply R S B])
    IsBaseChange S ({
      toFun := fun m => sectionMap g i j (CommRingCat.ofHom (algebraMap A B)) h E m
      map_add' := fun x y => (sectionMap g i j (CommRingCat.ofHom (algebraMap A B)) h E).map_add x y
      map_smul' := fun r m => by
        change sectionMap g i j _ h E ((algebraMap R A r) • m) = _
        calc
          _ = (algebraMap A B (algebraMap R A r)) • sectionMap g i j _ h E m :=
            (sectionMap g i j _ h E).map_smul' (algebraMap R A r) m
          _ = _ := by rw [← IsScalarTower.algebraMap_apply R A B]; rfl } : M →ₗ[R] N) := by
  let M : ModuleCat.{u} A := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (E.restrict i)
  let N : ModuleCat.{u} B := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj (((pullback g).obj E).restrict j)
  let : Module B N := N.isModule
  let : Module A M := M.isModule
  let : Module R M := Module.compHom M (algebraMap R A)
  let : Module R N := Module.compHom N (algebraMap R B)
  let : Module S N := Module.compHom N (algebraMap S B)
  let : Module A N := Module.compHom N (algebraMap A B)
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower S B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (R := R) (A := S) (M := N) (fun (r : R) (m : N) => by
    change ((algebraMap S B (algebraMap R S r)) • m : N) = ((algebraMap R B r) • m : N)
    rw [← IsScalarTower.algebraMap_apply R S B])
  let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul (R := R) (A := A) (M := N) (fun (r : R) (m : N) => by
    change ((algebraMap A B (algebraMap R A r)) • m : N) = ((algebraMap R B r) • m : N)
    rw [← IsScalarTower.algebraMap_apply R A B])
  let f : M →ₗ[A] N := {
    toFun := fun m => sectionMap g i j (CommRingCat.ofHom (algebraMap A B)) h E m
    map_add' := fun x y => (sectionMap g i j (CommRingCat.ofHom (algebraMap A B)) h E).map_add x y
    map_smul' := (sectionMap g i j (CommRingCat.ofHom (algebraMap A B)) h E).map_smul' }
  exact RelativeCech.isBaseChange_restrictScalars R S A B M N f
    (by
      have hh := isBaseChange_sections g i j (CommRingCat.ofHom (algebraMap A B)) h E
      dsimp only at hh
      simp only [CommRingCat.hom_ofHom] at hh
      convert hh using 1
      exact toAlgebra_algebraMap.symm)
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {Y : Scheme.{u}} {A R : CommRingCat.{u}} (i : Spec A ⟶ Y) [IsOpenImmersion i]
lemma appTop_appIso_inv (s : Γ(Y, ⊤)) :
    (i.appIso ⊤).inv (i.appTop s) =
      Y.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op s := by
  exact CategoryTheory.congr_fun (Scheme.Hom.appLE_appIso_inv i
    (show (⊤ : (Spec A).Opens) ≤ i ⁻¹ᵁ ⊤ from le_top)) s

lemma scalar_identity (a : R ⟶ A) (s : R ⟶ Γ(Y, ⊤))
    (h : s ≫ i.appTop = a ≫ (Scheme.ΓSpecIso A).inv) (r : R) :
    (i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv (a r)) =
      Y.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op (s r) := by
  have hc : i.appTop (s r) = (Scheme.ΓSpecIso A).inv (a r) :=
    CategoryTheory.congr_fun h r
  rw [← hc]
  exact appTop_appIso_inv i (s r)

def coefficientSectionEquiv (E : Y.Modules) (a : R ⟶ A) (s : R ⟶ Γ(Y, ⊤))
    (h : s ≫ i.appTop = a ≫ (Scheme.ΓSpecIso A).inv) :
    let M : ModuleCat A := moduleSpecΓFunctor.obj (E.restrict i)
    let N : Type u := Γ(E, i ''ᵁ ⊤)
    letI : Module R M := Module.compHom M a.hom
    letI : Module R N := Module.compHom N
      (s ≫ Y.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom
    M ≃ₗ[R] N := by
  let M : ModuleCat A := moduleSpecΓFunctor.obj (E.restrict i)
  let N : Type u := Γ(E, i ''ᵁ ⊤)
  letI : Module R M := Module.compHom M a.hom
  letI : Module R N := Module.compHom N
    (s ≫ Y.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom
  refine { toFun := fun m => m
           invFun := fun m => m
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  let : Module Γ(Y,i ''ᵁ ⊤) M := (E.val.obj (op (i ''ᵁ ⊤))).isModule
  change ((i.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv (a r))) • m =
    (Y.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op (s r)) • m
  rw [scalar_identity i a s h]
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (g : X ⟶ Y) (f : R ⟶ S) (sR : R ⟶ Γ(Y,⊤)) (sS : S ⟶ Γ(X,⊤))
  (h : sR ≫ g.appTop = f ≫ sS)

abbrev coefficientModule (s : R ⟶ Γ(Y,⊤)) (E : Y.Modules) (U : Y.Opens) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (s ≫ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom).obj
    (E.val.obj (op U))

include h in
lemma scalar_section_map (U : Y.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    sR ≫ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ g.appLE U V hV =
      f ≫ sS ≫ X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  calc
    _ = sR ≫ g.appLE ⊤ V (show V ≤ g ⁻¹ᵁ ⊤ from le_top) := by
      rw [Scheme.Hom.map_appLE]
    _ = (sR ≫ g.appTop) ≫ X.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op := by
      rfl
    _ = _ := by rw [h, Category.assoc]

def coefficientUnit (E : Y.Modules) (U : Y.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    coefficientModule sR E U →ₛₗ[f.hom] coefficientModule sS ((pullback g).obj E) V where
  toFun m := ((pullback g).obj E).presheaf.map (homOfLE hV).op
    (((pullbackPushforwardAdjunction g).unit.app E).app U m)
  map_add' x y := by
    change Γ(E, U) at x y
    erw [map_add, map_add]
    rfl
  map_smul' r m := by
    change Γ(E,U) at m
    change ((pullback g).obj E).presheaf.map (homOfLE hV).op
      (((pullbackPushforwardAdjunction g).unit.app E).app U
        ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sR r)) • m)) =
      (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (sS (f r))) • _
    rw [show ((pullbackPushforwardAdjunction g).unit.app E).app U
      ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sR r)) • m) =
      (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sR r)) •
        ((pullbackPushforwardAdjunction g).unit.app E).app U m from
      (((pullbackPushforwardAdjunction g).unit.app E).val.app (op U)).hom.map_smul _ _]
    let : Module Γ(X, g ⁻¹ᵁ U) Γ((pullback g ⋙ pushforward g).obj E,U) :=
      (((pullback g).obj E).val.obj (op (g ⁻¹ᵁ U))).isModule
    change ((pullback g).obj E).presheaf.map (homOfLE hV).op
      ((g.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sR r))) •
        ((pullbackPushforwardAdjunction g).unit.app E).app U m) = _
    erw [Scheme.Modules.map_smul]
    congr 1
    exact CategoryTheory.congr_fun (scalar_section_map g f sR sS h U V hV) r
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped TensorProduct
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  {X Y : Scheme.{u}} (g : X ⟶ Y) (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (h : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i = j ≫ g)
  (sR : CommRingCat.of R ⟶ Γ(Y,⊤)) (sS : CommRingCat.of S ⟶ Γ(X,⊤))
  (hi : sR ≫ i.appTop = CommRingCat.ofHom (algebraMap R A) ≫ (Scheme.ΓSpecIso (.of A)).inv)
  (hj : sS ≫ j.appTop = CommRingCat.ofHom (algebraMap S B) ≫ (Scheme.ΓSpecIso (.of B)).inv)
  (hg : sR ≫ g.appTop = CommRingCat.ofHom (algebraMap R S) ≫ sS)

include hi hj in
lemma coefficientUnit_isBaseChange (E : Y.Modules) [E.IsQuasicoherent] :
    let M := coefficientModule sR E (i ''ᵁ ⊤)
    let N := coefficientModule sS ((pullback g).obj E) (j ''ᵁ ⊤)
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S ({
      toFun := coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E
        (i ''ᵁ ⊤) (j ''ᵁ ⊤) (image_top_le_preimage g i j _ h)
      map_add' := map_add _
      map_smul' := fun r m => (coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E
        (i ''ᵁ ⊤) (j ''ᵁ ⊤) (image_top_le_preimage g i j _ h)).map_smul' r m } : M →ₗ[R] N) := by
  let MC : ModuleCat A := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (E.restrict i)
  let NC : ModuleCat B := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj (((pullback g).obj E).restrict j)
  let : Module A MC := MC.isModule
  let : Module B NC := NC.isModule
  let : Module R MC := Module.compHom MC (algebraMap R A)
  let : Module R NC := Module.compHom NC (algebraMap R B)
  let : Module S NC := Module.compHom NC (algebraMap S B)
  let : IsScalarTower R S NC := IsScalarTower.of_algebraMap_smul (R := R) (A := S) (M := NC) (fun (r : R) (m : NC) => by
    change ((algebraMap S B (algebraMap R S r)) • m : NC) = ((algebraMap R B r) • m : NC)
    rw [← IsScalarTower.algebraMap_apply R S B])
  let M := coefficientModule sR E (i ''ᵁ ⊤)
  let N := coefficientModule sS ((pullback g).obj E) (j ''ᵁ ⊤)
  let : Module R N := Module.compHom N (algebraMap R S)
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eM : MC ≃ₗ[R] M := coefficientSectionEquiv i E (CommRingCat.ofHom (algebraMap R A)) sR hi
  let eN : NC ≃ₗ[S] N := coefficientSectionEquiv j ((pullback g).obj E)
    (CommRingCat.ofHom (algebraMap S B)) sS hj
  have hb := isBaseChange_sections_overBase (R := R) (S := S) g i j h E
  apply IsBaseChange.of_equiv (eM.symm.baseChange R S M MC ≪≫ₗ hb.equiv ≪≫ₗ eN)
  intro m
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  have he := hb.equiv_tmul (1 : S) (eM.symm m)
  rw [one_smul] at he
  have he' := congrArg eN he
  exact he'.trans (sectionMap_apply g i j _ h E m)
include h hi hj in
lemma coefficientUnit_isBaseChange_of_image (E : Y.Modules) [E.IsQuasicoherent]
    (U : Y.Opens) (V : X.Opens) (hiU : i ''ᵁ ⊤ = U) (hjV : j ''ᵁ ⊤ = V)
    (hv : V ≤ g ⁻¹ᵁ U) :
    let M := coefficientModule sR E U
    let N := coefficientModule sS ((pullback g).obj E) V
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S ({
      toFun := coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E U V hv
      map_add' := map_add _
      map_smul' := fun r m => (coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E U V hv).map_smul' r m } : M →ₗ[R] N) := by
  subst U
  subst V
  exact coefficientUnit_isBaseChange g i j h sR sS hi hj hg E
end

section
open CategoryTheory AlgebraicGeometry Limits Opposite
universe u
variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (g : X ⟶ Y) (x : X ⟶ Spec S) (y : Y ⟶ Spec R) (f : R ⟶ S)
  (H : IsPullback g x y (Spec.map f))

def baseScalars : R ⟶ Γ(Y,⊤) := (Scheme.ΓSpecIso R).inv ≫ y.appTop

def openBaseScalars (U : Y.Opens) : R ⟶ Γ(Y,U) :=
  baseScalars y ≫ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op

include H in
lemma baseScalars_natural : baseScalars y ≫ g.appTop = f ≫ baseScalars x := by
  dsimp only [baseScalars]
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

include H in
lemma openBaseScalars_pushout (U : Y.Opens) (V : X.Opens)
    (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : V = g ⁻¹ᵁ U) :
    IsPushout (openBaseScalars y U) f (g.appLE U V (by rw [hUV])) (openBaseScalars x V) := by
  have hv : V = g ⁻¹ᵁ U ⊓ x ⁻¹ᵁ ⊤ := by simpa using hUV
  have hIso := isIso_pushoutSection_of_isAffineOpen H
    (show (⊤ : (Spec S).Opens) ≤ (Spec.map f) ⁻¹ᵁ ⊤ from le_top)
    (show U ≤ y ⁻¹ᵁ ⊤ from le_top) hv
    (isAffineOpen_top (Spec R)) (isAffineOpen_top (Spec S)) hU
  have hp := (isIso_pushoutSection_iff H
    (show (⊤ : (Spec S).Opens) ≤ (Spec.map f) ⁻¹ᵁ ⊤ from le_top)
    (show U ≤ y ⁻¹ᵁ ⊤ from le_top) hv).mp hIso
  refine hp.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso S) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, openBaseScalars, baseScalars,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  · exact Scheme.ΓSpecIso_naturality f
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, openBaseScalars, baseScalars,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
end

section
open CategoryTheory AlgebraicGeometry Limits Opposite
open Scheme.Modules
universe u
variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma fromSpec_appTop {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appTop = Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      (Scheme.ΓSpecIso Γ(Y,U)).inv := by
  have he := hU.fromSpec_app_of_le ⊤ (show U ≤ ⊤ from le_top)
  simpa [Scheme.Hom.appTop] using! he

variable (g : X ⟶ Y)
  (sR : CommRingCat.of R ⟶ Γ(Y,⊤)) (sS : CommRingCat.of S ⟶ Γ(X,⊤))
  (hg : sR ≫ g.appTop = CommRingCat.ofHom (algebraMap R S) ≫ sS)
  (U : Y.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U)
  (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
  (hp : IsPushout
    (sR ≫ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op)
    (CommRingCat.ofHom (algebraMap R S)) (g.appLE U V hV)
    (sS ≫ X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op))

include hp hUaff hVaff in
lemma coefficientUnit_isBaseChange_of_isPushout (E : Y.Modules) [E.IsQuasicoherent] :
    let M := coefficientModule sR E U
    let N := coefficientModule sS ((Scheme.Modules.pullback g).obj E) V
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S ({
      toFun := coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E U V hV
      map_add' := map_add _
      map_smul' := fun r m => (coefficientUnit g (CommRingCat.ofHom (algebraMap R S)) sR sS hg E U V hV).map_smul' r m } : M →ₗ[R] N) := by
  let A := Γ(Y,U)
  let B := Γ(X,V)
  let a : CommRingCat.of R ⟶ A := sR ≫ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  let b : CommRingCat.of S ⟶ B := sS ≫ X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
  let φ : A ⟶ B := g.appLE U V hV
  let : Algebra R A := a.hom.toAlgebra
  let : Algebra S B := b.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra R B := (a ≫ φ).hom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun r => CategoryTheory.congr_fun hp.w r)
  let : Algebra.IsPushout R S A B :=
    (CommRingCat.isPushout_iff_isPushout.mp hp).symm
  have hi : sR ≫ hUaff.fromSpec.appTop = CommRingCat.ofHom (algebraMap R A) ≫ (Scheme.ΓSpecIso A).inv := by
    rw [fromSpec_appTop]
    rfl
  have hj : sS ≫ hVaff.fromSpec.appTop = CommRingCat.ofHom (algebraMap S B) ≫ (Scheme.ΓSpecIso B).inv := by
    rw [fromSpec_appTop]
    rfl
  exact coefficientUnit_isBaseChange_of_image g hUaff.fromSpec hVaff.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec g hUaff hVaff hV) sR sS hi hj hg E U V
    (by simp [Scheme.Hom.image_top_eq_opensRange])
    (by simp [Scheme.Hom.image_top_eq_opensRange]) hV

end

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (g : X ⟶ Y) (f : R ⟶ S) (sR : R ⟶ Γ(Y,⊤)) (sS : S ⟶ Γ(X,⊤))
  (h : sR ≫ g.appTop = f ≫ sS)

lemma coefficientUnit_naturality (E : Y.Modules)
    (U₁ U₂ : Y.Opens) (V₁ V₂ : X.Opens)
    (hU : U₁ ≤ U₂) (hV : V₁ ≤ V₂)
    (hv₁ : V₁ ≤ g ⁻¹ᵁ U₁) (hv₂ : V₂ ≤ g ⁻¹ᵁ U₂)
    (m : Γ(E,U₂)) :
    coefficientUnit g f sR sS h E U₁ V₁ hv₁
      (E.presheaf.map (homOfLE hU).op m) =
    ((pullback g).obj E).presheaf.map (homOfLE hV).op
      (coefficientUnit g f sR sS h E U₂ V₂ hv₂ m) := by
  have hn := ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction g).unit.app E).val.naturality (homOfLE hU).op).symm m
  change ((pullback g).obj E).presheaf.map
    (homOfLE (show g ⁻¹ᵁ U₁ ≤ g ⁻¹ᵁ U₂ from fun x hx => hU hx)).op
    (((pullbackPushforwardAdjunction g).unit.app E).app U₂ m) =
    (((pullbackPushforwardAdjunction g).unit.app E).app U₁
      (E.presheaf.map (homOfLE hU).op m)) at hn
  change ((pullback g).obj E).presheaf.map (homOfLE hv₁).op
    (((pullbackPushforwardAdjunction g).unit.app E).app U₁
      (E.presheaf.map (homOfLE hU).op m)) = _
  rw [← hn]
  change (((pullback g).obj E).presheaf.map _ ≫ ((pullback g).obj E).presheaf.map _)
    (((pullbackPushforwardAdjunction g).unit.app E).app U₂ m) =
    (((pullback g).obj E).presheaf.map _ ≫ ((pullback g).obj E).presheaf.map _)
    (((pullbackPushforwardAdjunction g).unit.app E).app U₂ m)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl
end CampanaPeternellSix.AffineSquare

end

end OAI
