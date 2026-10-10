import Mathlib

namespace OAI

/-! The cotangent sheaf is the sheafification of the presheaf of Kähler differentials, with its universal derivation. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- Constants on every open come from the given structure morphism. -/
def constants : (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of k) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp, Category.assoc, Category.assoc, ← X.presheaf.map_comp]
    congr 2

/-- The presheaf of Kähler differentials of all section rings. -/
def presheaf : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constants f)

/-- The Zariski cotangent sheaf. -/
def sheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (presheaf f)

/-- Its derivation is induced by the universal objectwise derivation. -/
def derivation : PresheafOfModulesOfCommRing.Derivation' ((sheaf f).val) (constants f) :=
  (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' (constants f)).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf f))

variable (M : X.Modules)

/-- Universal property among sheaves of modules. -/
def homEquiv : (sheaf f ⟶ M) ≃ PresheafOfModulesOfCommRing.Derivation' (M.val) (constants f) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (presheaf f) M).trans
    { toFun := fun a =>
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' (constants f)).postcomp a
      invFun := fun d =>
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' (constants f)).desc d
      left_inv := fun a => by
        apply (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' (constants f)).postcomp_injective
        exact (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' (constants f)).fac _
      right_inv := fun d =>
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' (constants f)).fac d }

lemma homEquiv_apply (a : sheaf f ⟶ M) :
    homEquiv f M a = (derivation f).postcomp a.val := by
  ext U b
  rfl

end ActualCotangent

end

/-! Derivations and cotangent sheaves under open restriction. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))

lemma constants_app (U : Y.Opens) :
    (constants g).app (.op U) ≫ f.app U =
      (constants (f ≫ g)).app (.op (f ⁻¹ᵁ U)) := by
  dsimp [constants]
  simp only [Category.assoc]
  rw [Scheme.Hom.naturality]
  simp only [← Category.assoc]
  congr 1

lemma constants_app_apply (U : Y.Opens) (a : k) :
    f.app U ((constants g).app (.op U) a) =
      (constants (f ≫ g)).app (.op (f ⁻¹ᵁ U)) a :=
  congr($(constants_app f g U) a)

/-- Push a derivation back through the map of section rings. -/
def pushDerivation (N : X.Modules)
    (D : PresheafOfModulesOfCommRing.Derivation' (N.val) (constants (f ≫ g))) :
    PresheafOfModulesOfCommRing.Derivation' (((Scheme.Modules.pushforward f).obj N).val) (constants g) where
  d {U} := D.d.comp (f.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change D.d ((f.app U.unop) (a*b)) = _
    erw [map_mul]
    exact D.d_mul _ _
  d_map {U V} h a := by
    change D.d (f.app V.unop (Y.presheaf.map h a)) =
      N.val.map ((Opens.map f.base).map h.unop).op (D.d (f.app U.unop a))
    erw [← D.d_map]
    congr 1
    exact congr($(f.naturality h) a)
  d_app {U} a := by
    change D.d (f.app U.unop ((constants g).app U a)) = 0
    rw [constants_app_apply]
    exact D.d_app a

variable [IsOpenImmersion f]
lemma constants_appIso (U : X.Opens) :
    (constants g).app (.op (f ''ᵁ U)) ≫ (f.appIso U).hom =
      (constants (f ≫ g)).app (.op U) := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE, ← Category.assoc,constants_app]
  exact (constants (f ≫ g)).naturality _ |>.symm

lemma constants_appIso_inv (U : X.Opens) :
    (constants (f ≫ g)).app (.op U) ≫ (f.appIso U).inv =
      (constants g).app (.op (f ''ᵁ U)) := by
  rw [← constants_appIso f g U, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Restrict an sheaf derivation along an open immersion. -/
def restrictDerivation (M : Y.Modules) (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (constants g)) :
    PresheafOfModulesOfCommRing.Derivation' ((M.restrict f).val) (constants (f ≫ g)) where
  d {U} := D.d.comp (f.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change D.d ((f.appIso U.unop).inv (a*b)) = _
    erw [map_mul]
    exact D.d_mul _ _
  d_map {U V} h a := by
    change D.d ((f.appIso V.unop).inv (X.presheaf.map h a)) =
      M.val.map (f.opensFunctor.map h.unop).op (D.d ((f.appIso U.unop).inv a))
    erw [← D.d_map]
    congr 1
    exact congr($(f.appIso_inv_naturality h) a)
  d_app {U} a := by
    change D.d ((f.appIso U.unop).inv ((constants (f ≫ g)).app U a)) = 0
    rw [show (f.appIso U.unop).inv ((constants (f ≫ g)).app U a) =
      (constants g).app (.op (f ''ᵁ U.unop)) a from
      congr($(constants_appIso_inv f g U.unop) a)]
    exact D.d_app a

/-- Recover a derivation on an open scheme from one with values in its
pushforward, using the restriction-pushforward counit. -/
def pullDerivation (N : X.Modules)
    (D : PresheafOfModulesOfCommRing.Derivation' (((Scheme.Modules.pushforward f).obj N).val) (constants g)) :
    PresheafOfModulesOfCommRing.Derivation' (N.val) (constants (f ≫ g)) :=
  (restrictDerivation f g _ D).postcomp
    ((Scheme.Modules.restrictAdjunction f).counit.app N).val

lemma pull_push (N : X.Modules) (D : PresheafOfModulesOfCommRing.Derivation' (N.val) (constants (f ≫ g))) :
    pullDerivation f g N (pushDerivation f g N D) = D := by
  ext U a
  change N.val.map (eqToHom (f.preimage_image_eq U.unop).symm).op
    (D.d (f.app (f ''ᵁ U.unop) ((f.appIso U.unop).inv a))) = D.d a
  erw [← D.d_map]
  congr 1
  have hh : (f.appIso U.unop).inv ≫ f.app (f ''ᵁ U.unop) ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
    rw [← Scheme.Hom.appIso_hom, Iso.inv_hom_id]
  exact congr($(hh) a)

lemma push_pull (N : X.Modules)
    (D : PresheafOfModulesOfCommRing.Derivation' (((Scheme.Modules.pushforward f).obj N).val) (constants g)) :
    pushDerivation f g N (pullDerivation f g N D) = D := by
  ext U a
  change N.val.map (eqToHom (f.preimage_image_eq (f ⁻¹ᵁ U.unop)).symm).op
      (D.d ((f.appIso (f ⁻¹ᵁ U.unop)).inv (f.app U.unop a))) = D.d a
  have hh : (f.appIso (f ⁻¹ᵁ U.unop)).inv (f.app U.unop a) =
      Y.presheaf.map (homOfLE (f.image_preimage_le U.unop)).op a :=
    congr($(f.app_appIso_inv U.unop) a)
  erw [hh,D.d_map]
  change N.val.map (eqToHom (f.preimage_image_eq (f ⁻¹ᵁ U.unop)).symm).op
      (N.val.map ((Opens.map f.base).map (homOfLE (f.image_preimage_le U.unop))).op
        (D.d a)) = D.d a
  have hh' : N.presheaf.map ((Opens.map f.base).map
      (homOfLE (f.image_preimage_le U.unop))).op ≫
      N.presheaf.map (eqToHom (f.preimage_image_eq (f ⁻¹ᵁ U.unop)).symm).op = 𝟙 _ := by
    rw [← N.presheaf.map_comp]
    exact N.presheaf.map_id _
  exact congr($(hh') (D.d a))

/-- Derivations are local for open immersions. -/
def openDerivationEquiv (N : X.Modules) :
    PresheafOfModulesOfCommRing.Derivation' (((Scheme.Modules.pushforward f).obj N).val) (constants g) ≃
      PresheafOfModulesOfCommRing.Derivation' (N.val) (constants (f ≫ g)) where
  toFun := pullDerivation f g N
  invFun := pushDerivation f g N
  left_inv := push_pull f g N
  right_inv := pull_push f g N

end ActualCotangent


end

/-! Extension and uniqueness of derivations on affine principal opens. -/
noncomputable section
open KaehlerDifferential TensorProduct
namespace Derivation
open scoped _root_.Derivation
variable (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M] [Module S M]
  [IsScalarTower k R M] [IsScalarTower k S M] [IsScalarTower R S M]
variable [Algebra.FormallyEtale R S]

/-- A derivation extends uniquely along any formally étale algebra. -/
def extendEtale (d : Derivation k R M) : Derivation k S M :=
  ((LinearMap.liftBaseChange S d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale k R S).symm.toLinearMap).compDer (D k S)

lemma extendEtale_algebraMap (d : Derivation k R M) (a : R) :
    extendEtale k R S d (algebraMap R S a) = d a := by
  change LinearMap.liftBaseChange S d.liftKaehlerDifferential
    ((tensorKaehlerEquivOfFormallyEtale k R S).symm (D k S (algebraMap R S a))) = d a
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, _root_.Derivation.liftKaehlerDifferential_comp_D]

variable (T : Submonoid R) [IsLocalization T S]

omit [Module R M] [IsScalarTower k R M] [IsScalarTower R S M]
  [Algebra.FormallyEtale R S] in
include T in
lemma ext_of_algebraMap {d e : Derivation k S M}
    (he : ∀ a : R, d (algebraMap R S a) = e (algebraMap R S a)) : d = e := by
  have h : d.liftKaehlerDifferential = e.liftKaehlerDifferential := by
    apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (span_range_map_derivation_of_isLocalization k R S T)).mpr
    rintro ⟨_,⟨a,rfl⟩⟩
    simp only [Function.comp_apply, map_D, _root_.Derivation.liftKaehlerDifferential_comp_D]
    exact he a
  ext a
  simpa only [_root_.Derivation.liftKaehlerDifferential_comp_D] using
    congrArg (fun f : Ω[S⁄k] →ₗ[S] M => f (D k S a)) h


/-- Additive Leibniz maps on a localization are determined on the base ring.
This form does not prescribe a base-field scalar structure on the target. -/
lemma additive_ext_of_localization
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid A) [IsLocalization T B]
    {N : Type*} [AddCommGroup N] [Module B N]
    (d e : B →+ N)
    (hd : ∀ a b : B, d (a*b) = a • d b + b • d a)
    (he : ∀ a b : B, e (a*b) = a • e b + b • e a)
    (h : ∀ a : A, d (algebraMap A B a) = e (algebraMap A B a)) : d = e := by
  let : Module A N := Module.compHom N (algebraMap A B)
  let : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  have hd1 : d 1 = 0 := by simpa using (hd 1 1)
  have he1 : e 1 = 0 := by simpa using (he 1 1)
  let d' : Derivation ℤ B N :=
    { toLinearMap := d.toIntLinearMap
      map_one_eq_zero' := hd1
      leibniz' := hd }
  let e' : Derivation ℤ B N :=
    { toLinearMap := e.toIntLinearMap
      map_one_eq_zero' := he1
      leibniz' := he }
  have hh : d' = e' := Derivation.ext_of_algebraMap ℤ A B T h
  ext b
  exact Derivation.congr_fun hh b

end Derivation


end

/-! Derivations of an affine coordinate ring extend to the structure sheaf. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace AffineDerivation
universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
variable (M : (Spec (.of R)).Modules)

local instance (priority := 3000) (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R), U) Γ(M, U) := (M.val.obj (.op U)).isModule

local instance (priority := 2000) (U : (Spec (.of R)).Opens) :
    Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance (priority := 2000) (U : (Spec (.of R)).Opens) : Module R Γ(M,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U)))

local instance (priority := 2000) (U : (Spec (.of R)).Opens) :
    IsScalarTower R Γ(Spec (.of R),U) Γ(M,U) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) Γ(M,U)

local instance (U : (Spec (.of R)).Opens) : Algebra k Γ(Spec (.of R), U) :=
  ((algebraMap R Γ(Spec (.of R), U)).comp (algebraMap k R)).toAlgebra
local instance (U : (Spec (.of R)).Opens) :
    IsScalarTower k R Γ(Spec (.of R), U) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance (U : (Spec (.of R)).Opens) : Module k Γ(M, U) :=
  Module.compHom Γ(M,U) (algebraMap k R)
local instance (U : (Spec (.of R)).Opens) : IsScalarTower k R Γ(M, U) :=
  IsScalarTower.of_compHom k R _
local instance (U : (Spec (.of R)).Opens) :
    IsScalarTower k Γ(Spec (.of R), U) Γ(M, U) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a b
  change (algebraMap R Γ(Spec (.of R), U) (algebraMap k R a)) • b =
    (algebraMap k R a) • b
  exact IsScalarTower.algebraMap_smul Γ(Spec (.of R), U) _ _

private local instance (priority := 3000) (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Module Γ(Spec (.of R), U) Γ(M, U) := (M.val.obj (.op U)).isModule

private local instance (priority := 2000) (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
private local instance (priority := 2000) (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Module R Γ(M,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U)))

private local instance (priority := 2000) (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    IsScalarTower R Γ(Spec (.of R),U) Γ(M,U) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) Γ(M,U)

private local instance (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Algebra k Γ(Spec (.of R), U) :=
  ((algebraMap R Γ(Spec (.of R), U)).comp (algebraMap k R)).toAlgebra
private local instance (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    IsScalarTower k R Γ(Spec (.of R), U) :=
  IsScalarTower.of_algebraMap_eq' rfl
private local instance (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Module k Γ(M, U) :=
  Module.compHom Γ(M,U) (algebraMap k R)
private local instance (U : TopologicalSpace.Opens (PrimeSpectrum R)) : IsScalarTower k R Γ(M, U) :=
  IsScalarTower.of_compHom k R _
private local instance (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    IsScalarTower k Γ(Spec (.of R), U) Γ(M, U) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a b
  change (algebraMap R Γ(Spec (.of R), U) (algebraMap k R a)) • b =
    (algebraMap k R a) • b
  exact IsScalarTower.algebraMap_smul Γ(Spec (.of R), U) _ _

private local instance (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R), U) (PresheafOfModulesOfCommRing.obj M.val (.op U)) :=
  (M.val.obj (.op U)).isModule

local instance (r : R) : IsLocalization.Away r
    Γ(Spec (.of R), PrimeSpectrum.basicOpen r) :=
  inferInstanceAs (IsLocalization.Away r
    ((Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen r))))

local instance (r : R) : Algebra.FormallyEtale R
    Γ(Spec (.of R), PrimeSpectrum.basicOpen r) :=
  Algebra.FormallyEtale.of_isLocalization (.powers r)

/-- Restriction of sections regarded as a linear map over the base ring R. -/
def sectionRestriction {U V : (Spec (.of R)).Opens} (h : U ≤ V) :
    Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

/-- Derivations extend to the ring of sections of each principal open. -/
def basic (d : Derivation k R Γ(M,⊤)) (r : R) :
    Derivation k Γ(Spec (.of R), PrimeSpectrum.basicOpen r) Γ(M,PrimeSpectrum.basicOpen r) :=
  @Derivation.extendEtale k R Γ(Spec (.of R), PrimeSpectrum.basicOpen r)
    _ _ _ _ _ _ _ Γ(M, PrimeSpectrum.basicOpen r) _ _ _ _
    (IsScalarTower.of_compHom k R _) _ _ _
    (@LinearMap.compDer k R Γ(M,⊤) _ _ _ _ _ _ Γ(M, PrimeSpectrum.basicOpen r)
      _ _ _ _ (IsScalarTower.of_compHom k R _) (sectionRestriction R M le_top) d)

lemma basic_algebraMap (d : Derivation k R Γ(M,⊤)) (r a : R) :
    basic k R M d r (algebraMap R _ a) = sectionRestriction R M le_top (d a) :=
  @Derivation.extendEtale_algebraMap k R Γ(Spec (.of R), PrimeSpectrum.basicOpen r)
    _ _ _ _ _ _ _ Γ(M, PrimeSpectrum.basicOpen r) _ _ _ _
    (IsScalarTower.of_compHom k R _) _ _ _ _ a


/-- Compatibility of the extended derivations with restriction between
basic opens. -/
lemma basic_natural (d : Derivation k R Γ(M,⊤)) (r s : R)
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r)
    (a : Γ(Spec (.of R), PrimeSpectrum.basicOpen r)) :
    sectionRestriction R M h (basic k R M d r a) =
      basic k R M d s (((Spec (.of R)).presheaf.map (homOfLE h).op) a) := by
  let φ : Γ(Spec (.of R), PrimeSpectrum.basicOpen r) →+*
      Γ(Spec (.of R), PrimeSpectrum.basicOpen s) :=
    ((Spec (.of R)).presheaf.map (homOfLE h).op).hom
  let ψ := sectionRestriction R M h
  let : Module Γ(Spec (.of R), PrimeSpectrum.basicOpen r)
      Γ(M,PrimeSpectrum.basicOpen s) := Module.compHom _ φ
  let D₁ : Γ(Spec (.of R), PrimeSpectrum.basicOpen r) →+
      Γ(M,PrimeSpectrum.basicOpen s) :=
    ψ.toAddMonoidHom.comp (basic k R M d r).toLinearMap.toAddMonoidHom
  let D₂ : Γ(Spec (.of R), PrimeSpectrum.basicOpen r) →+
      Γ(M,PrimeSpectrum.basicOpen s) :=
    (basic k R M d s).toLinearMap.toAddMonoidHom.comp φ.toAddMonoidHom
  have hh : D₁ = D₂ := Derivation.additive_ext_of_localization R _ (.powers r) D₁ D₂
    (by
      intro x y
      change ψ (basic k R M d r (x*y)) =
        φ x • ψ (basic k R M d r y) + φ y • ψ (basic k R M d r x)
      rw [Derivation.leibniz, map_add]
      congr 1
      · exact M.val.map_smul (homOfLE h).op x _
      · exact M.val.map_smul (homOfLE h).op y _)
    (by
      intro x y
      change basic k R M d s (φ (x*y)) =
        φ x • basic k R M d s (φ y) + φ y • basic k R M d s (φ x)
      rw [map_mul, Derivation.leibniz])
    (by
      intro x
      change ψ (basic k R M d r (algebraMap R _ x)) =
        basic k R M d s (φ (algebraMap R _ x))
      have hφ : φ (algebraMap R _ x) = algebraMap R _ x := rfl
      rw [hφ, basic_algebraMap, basic_algebraMap]
      exact congrArg (fun f : (modulesSpecToSheaf.obj M).obj.obj (.op ⊤) ⟶
          (modulesSpecToSheaf.obj M).obj.obj (.op (PrimeSpectrum.basicOpen s)) => f (d x))
        ((modulesSpecToSheaf.obj M).obj.map_comp
          (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op
          (homOfLE h).op).symm)
  exact DFunLike.congr_fun hh a


private local instance :
    Category.{u,u} (InducedCategory (Opens ↥(Spec (.of R))) PrimeSpectrum.basicOpen) :=
  inferInstanceAs
    (Category.{u,u} (InducedCategory (Opens (PrimeSpectrum R)) PrimeSpectrum.basicOpen))

private local instance :
    Category.{u,u} (InducedCategory (Opens ↥(Spec (.of R))) PrimeSpectrum.basicOpen)ᵒᵖ :=
  inferInstanceAs
    (Category.{u,u} (InducedCategory (Opens (PrimeSpectrum R)) PrimeSpectrum.basicOpen)ᵒᵖ)

/-- The compatible derivation on the basis extends as an additive map to all
opens, using the sheaf condition of the target. -/
def additive (d : Derivation k R Γ(M,⊤)) :
    ((Spec (.of R)).ringCatSheaf.obj ⋙ forget₂ RingCat AddCommGrpCat) ⟶ M.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom (B := (PrimeSpectrum.basicOpen : R → (Spec (.of R)).Opens))
    _ ⟨M.presheaf,M.isSheaf⟩ PrimeSpectrum.isBasis_basic_opens
    { app r := AddCommGrpCat.ofHom (basic k R M d r.unop).toLinearMap.toAddMonoidHom
      naturality {r s} i := by
        ext a
        exact (basic_natural k R M d r.unop s.unop i.unop.hom.le a).symm }

lemma additive_basic (d : Derivation k R Γ(M,⊤)) (r : R)
    (a : Γ(Spec (.of R),PrimeSpectrum.basicOpen r)) :
    (additive k R M d).app (.op (PrimeSpectrum.basicOpen r)) a =
      basic k R M d r a := by
  unfold additive
  erw [TopCat.Sheaf.extend_hom_app]
  rfl

lemma additive_res (d : Derivation k R Γ(M,⊤))
    {U V : (Spec (.of R)).Opens} (h : U ≤ V) (a : Γ(Spec (.of R), V)) :
    (additive k R M d).app (.op U) (((Spec (.of R)).presheaf.map (homOfLE h).op) a) =
      M.presheaf.map (homOfLE h).op ((additive k R M d).app (.op V) a) :=
  congrArg (fun f => f a) ((additive k R M d).naturality (homOfLE h).op)


lemma constants_spec_app (U : (Spec (.of R)).Opens) (a : k) :
    (ActualCotangent.constants (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app
      (.op U) a = algebraMap k Γ(Spec (.of R),U) a := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
    (Spec (.of R)).presheaf.map (homOfLE le_top).op) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl


lemma additive_mul (d : Derivation k R Γ(M,⊤)) (U : (Spec (.of R)).Opens)
    (a b : Γ(Spec (.of R),U)) :
    (additive k R M d).app (.op U) (a*b) =
      a • (additive k R M d).app (.op U) b +
      b • (additive k R M d).app (.op U) a := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r,rfl⟩,rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  refine ⟨PrimeSpectrum.basicOpen r,hrU,hxr,?_⟩
  rw [map_add]
  change M.val.map (homOfLE hrU).op ((additive k R M d).app (.op U) (a*b)) =
    M.val.map (homOfLE hrU).op (a • ((additive k R M d).app (.op U) b)) +
    M.val.map (homOfLE hrU).op (b • ((additive k R M d).app (.op U) a))
  erw [M.val.map_smul, M.val.map_smul]
  erw [← additive_res k R M d hrU (a*b), ← additive_res k R M d hrU b,
    ← additive_res k R M d hrU a]
  rw [additive_basic, additive_basic, additive_basic, map_mul, Derivation.leibniz]
  rfl

lemma additive_algebraMap (d : Derivation k R Γ(M,⊤))
    (U : (Spec (.of R)).Opens) (a : k) :
    (additive k R M d).app (.op U) (algebraMap k Γ(Spec (.of R),U) a) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r,rfl⟩,rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  refine ⟨PrimeSpectrum.basicOpen r,hrU,hxr,?_⟩
  erw [map_zero, ← additive_res, additive_basic]
  have h : ((Spec (.of R)).presheaf.map (homOfLE hrU).op)
      (algebraMap k Γ(Spec (.of R),U) a) =
      algebraMap k Γ(Spec (.of R),PrimeSpectrum.basicOpen r) a := rfl
  change basic k R M d r (algebraMap k Γ(Spec (.of R),PrimeSpectrum.basicOpen r) a) = 0
  exact Derivation.map_algebraMap _ _

/-- derivation of the structure sheaf extending the given affine
coordinate derivation. -/
def derivation (d : Derivation k R Γ(M,⊤)) :
    PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))) where
  d {U} := ((additive k R M d).app U).hom
  d_mul {U} := additive_mul k R M d U.unop
  d_map {U V} i a := additive_res k R M d i.unop.le a
  d_app {U} a := by
    change (additive k R M d).app U
      ((ActualCotangent.constants (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app U a) = 0
    rw [constants_spec_app]
    exact additive_algebraMap k R M d U.unop a

lemma derivation_basic (d : Derivation k R Γ(M,⊤)) (r : R)
    (a : Γ(Spec (.of R),PrimeSpectrum.basicOpen r)) :
    (derivation k R M d).d a = basic k R M d r a := additive_basic k R M d r a

lemma derivation_top (d : Derivation k R Γ(M,⊤)) (a : R) :
    (derivation k R M d).d (algebraMap R Γ(Spec (.of R),⊤) a) = d a := by
  have hh := basic_algebraMap k R M d 1 a
  rw [← additive_basic] at hh
  have h1 : (PrimeSpectrum.basicOpen (1:R) : (Spec (.of R)).Opens) = ⊤ :=
    PrimeSpectrum.basicOpen_one
  change (additive k R M d).app (.op (PrimeSpectrum.basicOpen (1:R)))
    (algebraMap R Γ(Spec (.of R),PrimeSpectrum.basicOpen (1:R)) a) =
    sectionRestriction R M le_top (d a) at hh
  erw [h1] at hh
  dsimp only [sectionRestriction] at hh
  erw [(modulesSpecToSheaf.obj M).obj.map_id (.op ⊤)] at hh
  exact hh


lemma global_leibniz (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R))))) (a b : R) :
    D.d (algebraMap R Γ(Spec (.of R),⊤) (a*b)) =
      (algebraMap R Γ(Spec (.of R),⊤) a) • D.d (algebraMap R Γ(Spec (.of R),⊤) b) +
      (algebraMap R Γ(Spec (.of R),⊤) b) • D.d (algebraMap R Γ(Spec (.of R),⊤) a) :=
  (congrArg (D.d (X := .op ⊤)) ((algebraMap R Γ(Spec (.of R),⊤)).map_mul a b)).trans
    (D.d_mul _ _)

/-- Evaluate an sheaf derivation on the global coordinate functions. -/
def global (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R))))) : Derivation k R Γ(M,⊤) where
  toFun a := D.d (algebraMap R Γ(Spec (.of R),⊤) a)
  map_add' a b := by
      erw [map_add,map_add]
      rfl
  map_smul' a b := by
    erw [Algebra.smul_def,map_mul,D.d_mul]
    have hc : D.d (algebraMap R Γ(Spec (.of R),⊤) (algebraMap k R a)) = 0 := by
      have h := D.d_app (X := .op ⊤) a
      erw [constants_spec_app] at h
      exact h
    erw [hc, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := by
    change D.d (algebraMap R Γ(Spec (.of R),⊤) 1) = 0
    erw [map_one,D.d_one]
  leibniz' a b := global_leibniz k R M D a b

lemma global_apply (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R))))) (a : R) :
    global k R M D a = D.d (algebraMap R Γ(Spec (.of R),⊤) a) := rfl

lemma global_derivation (d : Derivation k R Γ(M,⊤)) :
    global k R M (derivation k R M d) = d := by
  ext a
  exact derivation_top k R M d a

lemma derivation_global_basic (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R))))) (r : R)
    (a : Γ(Spec (.of R),PrimeSpectrum.basicOpen r)) :
    (derivation k R M (global k R M D)).d a = D.d a := by
  rw [derivation_basic]
  have hh : (basic k R M (global k R M D) r).toLinearMap.toAddMonoidHom =
      D.d (X := .op (PrimeSpectrum.basicOpen r)) :=
    Derivation.additive_ext_of_localization R _ (.powers r) _ _
      (fun x y => (basic k R M (global k R M D) r).leibniz x y)
      (fun x y => D.d_mul x y) (by
        intro x
        change basic k R M (global k R M D) r (algebraMap R _ x) =
          D.d (algebraMap R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) x)
        rw [basic_algebraMap]
        change M.val.map (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op
          (D.d (algebraMap R Γ(Spec (.of R),⊤) x)) = _
        exact (D.d_map (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op
          (algebraMap R Γ(Spec (.of R),⊤) x)).symm)
  exact DFunLike.congr_fun hh a

lemma derivation_global (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R))))) :
    derivation k R M (global k R M D) = D := by
  ext U a
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r,rfl⟩,rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.unop.2
  refine ⟨PrimeSpectrum.basicOpen r,hrU,hxr,?_⟩
  change M.val.map (homOfLE hrU).op ((derivation k R M (global k R M D)).d a) =
    M.val.map (homOfLE hrU).op (D.d a)
  erw [← PresheafOfModulesOfCommRing.Derivation.d_map, ← D.d_map]
  exact derivation_global_basic k R M D r _

/-- Affine-coordinate derivations and sheaf derivations are equivalent. -/
def equiv : PresheafOfModulesOfCommRing.Derivation' (M.val) (ActualCotangent.constants
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))) ≃ Derivation k R Γ(M,⊤) where
  toFun := global k R M
  invFun := derivation k R M
  left_inv := derivation_global k R M
  right_inv := global_derivation k R M

end AffineDerivation


end

/-! The cotangent sheaf on an affine scheme is associated to its module of Kähler differentials. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

local instance (priority := 3000) (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module Γ(Spec (.of R),U) Γ(M,U) :=
  (M.val.obj (.op U)).isModule
local instance (priority := 2000) (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module R Γ(M,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U)))
local instance (M : (Spec (.of R)).Modules) : Module k Γ(M,⊤) :=
  Module.compHom Γ(M,⊤) (algebraMap k R)
local instance (M : (Spec (.of R)).Modules) : IsScalarTower k R Γ(M,⊤) :=
  IsScalarTower.of_compHom k R _

private local instance (M : SheafOfModules (Spec (.of R)).ringCatSheaf) :
    Module R Γ(M,⊤) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (.op ⊤)))
private local instance (M : SheafOfModules (Spec (.of R)).ringCatSheaf) :
    Module k Γ(M,⊤) := Module.compHom Γ(M,⊤) (algebraMap k R)
private local instance (M : SheafOfModules (Spec (.of R)).ringCatSheaf) :
    IsScalarTower k R Γ(M,⊤) := IsScalarTower.of_compHom k R _

/-- The affine comparison on Hom sets, using sheaf derivations. -/
def affineHomEquiv (M : (Spec (.of R)).Modules) :
    (sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ M) ≃
      (tilde (ModuleCat.of R (KaehlerDifferential k R)) ⟶ M) :=
  (((((homEquiv _ M).trans (AffineDerivation.equiv k R M)).trans
    (@KaehlerDifferential.linearMapEquivDerivation k R _ _ _ Γ(M,⊤) _ _ _
      (IsScalarTower.of_compHom k R _)).toEquiv.symm).trans
    (ModuleCat.homEquiv (M := ModuleCat.of R (KaehlerDifferential k R))
      (N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)).symm).trans
    ((tilde.adjunction (R := CommRingCat.of R)).homEquiv _ M).symm)

lemma affineHomEquiv_adjoint (M : (Spec (.of R)).Modules)
    (a : sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ M) :
    (tilde.adjunction (R := CommRingCat.of R)).homEquiv _ M
      (affineHomEquiv k R M a) =
    ModuleCat.ofHom (@Derivation.liftKaehlerDifferential k R _ _ _ Γ(M,⊤) _ _ _
      (IsScalarTower.of_compHom k R _) (AffineDerivation.global k R M (homEquiv _ M a))) := by
  exact ((tilde.adjunction (R := CommRingCat.of R)).homEquiv _ M).apply_symm_apply _

lemma affineHomEquiv_natural {M N : (Spec (.of R)).Modules}
    (a : sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ M)
    (b : M ⟶ N) :
    affineHomEquiv k R N (a ≫ b) = affineHomEquiv k R M a ≫ b := by
  apply ((tilde.adjunction (R := CommRingCat.of R)).homEquiv _ N).injective
  erw [(tilde.adjunction (R := CommRingCat.of R)).homEquiv_naturality_right
    (affineHomEquiv k R M a) b]
  erw [affineHomEquiv_adjoint k R N (a ≫ b), affineHomEquiv_adjoint k R M a]
  change ModuleCat.ofHom
      (@Derivation.liftKaehlerDifferential k R _ _ _ Γ(N,⊤) _ _ _
      (IsScalarTower.of_compHom k R _) (AffineDerivation.global k R N (homEquiv _ N (a ≫ b)))) =
    ModuleCat.ofHom (@Derivation.liftKaehlerDifferential k R _ _ _ Γ(M,⊤) _ _ _
      (IsScalarTower.of_compHom k R _) (AffineDerivation.global k R M (homEquiv _ M a))) ≫
      (moduleSpecΓFunctor (R := CommRingCat.of R)).map b
  apply ModuleCat.homEquiv.injective
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  change (@Derivation.liftKaehlerDifferential k R _ _ _ Γ(N,⊤) _ _ _
      (IsScalarTower.of_compHom k R _) (AffineDerivation.global k R N (homEquiv _ N (a ≫ b))))
      (KaehlerDifferential.D k R x) =
    ((moduleSpecΓFunctor (R := CommRingCat.of R)).map b).hom
      ((@Derivation.liftKaehlerDifferential k R _ _ _ Γ(M,⊤) _ _ _
      (IsScalarTower.of_compHom k R _) (AffineDerivation.global k R M (homEquiv _ M a)))
        (KaehlerDifferential.D k R x))
  erw [Derivation.liftKaehlerDifferential_comp_D,Derivation.liftKaehlerDifferential_comp_D]
  erw [homEquiv_apply,homEquiv_apply]
  rfl

/-- The intrinsic cotangent sheaf of Spec R over k is the tilde sheaf of
its Kähler module. -/
def affineIso : sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≅
    tilde (ModuleCat.of R (KaehlerDifferential k R)) :=
  (Coyoneda.ext _ _
    (fun {M} => (affineHomEquiv k R M).symm)
    (fun {M} => affineHomEquiv k R M)
    (fun _ => Equiv.apply_symm_apply _ _)
    (fun _ => Equiv.symm_apply_apply _ _)
    (fun _ _ => affineHomEquiv_natural k R _ _)).symm

end ActualCotangent

end

/-! Cotangent sheaves commute with restriction to open subschemes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsOpenImmersion f]

lemma homEquiv_natural {M N : Y.Modules} (a : sheaf g ⟶ M) (b : M ⟶ N) :
    homEquiv g N (a ≫ b) = (homEquiv g M a).postcomp b.val := by
  ext U x
  rfl

/-- The Hom-set version of the open cotangent comparison. -/
def openInverseHomEquiv (N : X.Modules) :
    (sheaf (f ≫ g) ⟶ N) ≃ ((sheaf g).restrict f ⟶ N) :=
  ((homEquiv (f ≫ g) N).trans (openDerivationEquiv f g N).symm).trans
    ((homEquiv g ((Scheme.Modules.pushforward f).obj N)).symm.trans
      ((Scheme.Modules.restrictAdjunction f).homEquiv _ N).symm)

lemma openInverseHomEquiv_eval (N : X.Modules) (a : sheaf (f ≫ g) ⟶ N) :
    homEquiv g _ ((Scheme.Modules.restrictAdjunction f).homEquiv _ N
      (openInverseHomEquiv f g N a)) =
    pushDerivation f g N (homEquiv (f ≫ g) N a) := by
  change homEquiv g _ (((Scheme.Modules.restrictAdjunction f).homEquiv _ N)
    (((Scheme.Modules.restrictAdjunction f).homEquiv _ N).symm _)) = _
  rw [Equiv.apply_symm_apply]
  exact (homEquiv g _).apply_symm_apply _

lemma openInverseHomEquiv_natural {M N : X.Modules}
    (a : sheaf (f ≫ g) ⟶ M) (b : M ⟶ N) :
    openInverseHomEquiv f g N (a ≫ b) = openInverseHomEquiv f g M a ≫ b := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ N).injective
  apply (homEquiv g _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have h₁ := openInverseHomEquiv_eval f g N (a ≫ b)
  have h₂ := openInverseHomEquiv_eval f g M a
  have h₃ := homEquiv_natural g
    ((Scheme.Modules.restrictAdjunction f).homEquiv (sheaf g) M
      (openInverseHomEquiv f g M a)) ((Scheme.Modules.pushforward f).map b)
  refine h₁.trans ?_
  refine Eq.trans ?_ h₃.symm
  rw [h₂]
  rw [homEquiv_natural]

  ext U x
  rfl

/-- The intrinsic cotangent sheaf is local for open immersions. -/
def openIso : (sheaf g).restrict f ≅ sheaf (f ≫ g) :=
  (Coyoneda.ext _ _
    (fun {M} => (openInverseHomEquiv f g M).symm)
    (fun {M} => openInverseHomEquiv f g M)
    (fun _ => Equiv.apply_symm_apply _ _)
    (fun _ => Equiv.symm_apply_apply _ _)
    (fun _ _ => openInverseHomEquiv_natural f g _ _))

variable (R : Type u) [CommRing R] [Algebra k R]

/-- The affine Kähler module, bundled before subsequent specialization. -/
abbrev affineModule := ModuleCat.of R (KaehlerDifferential k R)

/-- An open affine chart of any scheme computes its cotangent sheaf. -/
def openAffineIso (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
    (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    (sheaf g).restrict i ≅ tilde (ModuleCat.of R (KaehlerDifferential k R)) :=
  openIso i g ≪≫ eqToIso (congrArg sheaf h) ≪≫ affineIso k R

end ActualCotangent

end

end OAI
