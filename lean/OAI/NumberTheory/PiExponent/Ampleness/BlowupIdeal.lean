import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology
import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry

def sectionImageIdeal {X : Scheme} (J : LineBundle X)
    (ι : J.sheaf ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X, U) := by
  letI : Module Γ(X, U) (J.sheaf.val.obj (Opposite.op U)) :=
    (J.sheaf.val.obj (Opposite.op U)).isModule
  let φ : J.sheaf.val.obj (Opposite.op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (ι.val.app (Opposite.op U)).hom
  exact φ.range

def PresentsPullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) : Prop :=
  Mono ι ∧ ∀ (U : Y.affineOpens) (V : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1),
    sectionImageIdeal J ι U.1 = (I.ideal V).map (f.appLE V.1 U.1 e).hom

def InvertiblePullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  ∃ (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y), PresentsPullbackIdeal I f J ι

def IsBlowup {X B : Scheme} (I : X.IdealSheafData) (π : B ⟶ X) : Prop :=
  InvertiblePullbackIdeal I π ∧ ∀ (Y : Scheme) (f : Y ⟶ X),
    InvertiblePullbackIdeal I f → ∃! h : Y ⟶ B, h ≫ π = f

end Geometry

namespace IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

def sectionFamily {M : X.Modules} (s : Γ(M, ⊤)) : M.sections where
  val U := M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  property {U V} i := by
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) s = _
    rw [← Functor.map_comp]
    rfl

def fromSection {M : X.Modules} (s : Γ(M, ⊤)) : unit X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily s)

@[simp] lemma fromSection_app {M : X.Modules} (s : Γ(M, ⊤))
    (U : X.Opens) (a : Γ(X, U)) :
    (fromSection s).val.app (op U) a = a • M.presheaf.map (homOfLE le_top).op s := rfl

lemma fromSection_inclusion_app {M : X.Modules} (g : M ⟶ unit X)
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) ((fromSection s).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a := by
  rw [fromSection_app]
  have hn := PresheafOfModules.naturality_apply g.val (homOfLE (show U ≤ ⊤ from le_top)).op s
  change g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s) =
    X.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) s) at hn
  have he := ((g.val.app (op U)).hom).map_smul a (M.presheaf.map (homOfLE le_top).op s)
  change _ = a * (show Γ(X, U) from g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s)) at he
  exact he.trans ((congrArg (fun b : Γ(X, U) => a * b)
    (hn.trans (congrArg (fun b : Γ(X, ⊤) => X.presheaf.map (homOfLE le_top).op b) hs))).trans
      (mul_comm _ _))

lemma isIso_fromSection {M : X.Modules} (g : M ⟶ unit X) [Mono g]
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (hprincipal : ∀ U : X.affineOpens,
      (g.val.app (op U.1)).hom.range = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (fromSection s) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective (g.val.app (op U.1)) := by
    let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
    exact PresheafOfModules.injective_of_mono g.val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg (g.val.app (op U.1)) hab
    change g.val.app (op U.1) ((fromSection s).val.app (op U.1) a) =
      g.val.app (op U.1) ((fromSection s).val.app (op U.1) b) at he
    exact (fromSection_inclusion_app g s r hs U.1 a).symm.trans
      (he.trans (fromSection_inclusion_app g s r hs U.1 b))
  · intro y
    have hy : (show Γ(X, U.1) from g.val.app (op U.1) y) ∈
        Ideal.span {X.presheaf.map (homOfLE le_top).op r} := by
      rw [← hprincipal U]
      exact ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨a, hinj ?_⟩
    exact (fromSection_inclusion_app g s r hs U.1 a).trans ha.symm

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    PiExponentSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  exact mono_comp' (C := X.Modules) inferInstance
    ⟨fun a b h => (Iso.cancel_iso_hom_right a b (Scheme.Modules.restrictUnitIso f)).mp h⟩

lemma restrictedInclusion_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ((closedModule I).restrict f, U)) :
    (restrictedInclusion I f).val.app (op U) s =
      (f.appIso U).hom ((closedInclusion I).val.app (op (f ''ᵁ U)) s) := rfl

lemma restricted_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    ((restrictedInclusion I f).val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  rw [I.ideal_comap_of_isOpenImmersion f U]
  ext r
  change Γ(X, U.1) at r
  change (∃ s, (restrictedInclusion I f).val.app (op U.1) s = r) ↔
    (f.appIso U.1).inv r ∈ I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  rw [← closed_image I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩]
  change (∃ s, _) ↔ ∃ s, (closedInclusion I).val.app (op (f ''ᵁ U.1)) s = (f.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (congrArg (fun k : Γ(Y, f ''ᵁ U.1) ⟶ Γ(Y, f ''ᵁ U.1) => k ((closedInclusion I).val.app (op (f ''ᵁ U.1)) s))
      (f.appIso U.1).hom_inv_id).symm.trans
        (congrArg (fun z : Γ(X, U.1) => (f.appIso U.1).inv z)
          ((restrictedInclusion_app I f U.1 s).symm.trans hs))
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (restrictedInclusion_app I f U.1 s).trans
      ((congrArg (fun z : Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).hom z) hs).trans
        (congrArg (fun k : Γ(X, U.1) ⟶ Γ(X, U.1) => k r) (f.appIso U.1).inv_hom_id))

lemma frame_restriction (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [IsAffine X] (r : Γ(X, ⊤))
    (hprincipal : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    Nonempty ((closedModule I).restrict f ≅ unit X) := by
  have hr' : r ∈ (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [hprincipal]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hr : r ∈ ((restrictedInclusion I f).val.app (op ⊤)).hom.range := by
    rw [restricted_image I f ⟨⊤, isAffineOpen_top X⟩]
    exact hr'
  obtain ⟨s, hs⟩ := hr
  have hi : IsIso (fromSection (M := (closedModule I).restrict f) s) := isIso_fromSection (restrictedInclusion I f) s r hs
    (fun U => ?_) (restriction_regular r hregular)
  · exact ⟨(asIso (fromSection (M := (closedModule I).restrict f) s)).symm⟩
  · rw [restricted_image I f U, ← (I.comap f).map_ideal (U := U)
      (V := ⟨⊤, isAffineOpen_top X⟩) (by change U.1 ≤ ⊤; exact le_top), hprincipal]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def frameOnRange (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
    (e : M.restrict f ≅ unit X) : M.restrict f.opensRange.ι ≅ unit f.opensRange.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.restrictFunctor f.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso f.isoOpensRange.inv

end IdealModule
namespace IdealPullback

section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

lemma map_top (J : X.IdealSheafData) (f : X ⟶ Y) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom :=
  J.ideal_map f ⟨⊤, isAffineOpen_top Y⟩ (isAffineOpen_top X)

lemma comap_top (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  apply le_antisymm
  · let J : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
    have h : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [map_top]
      simpa [J] using Ideal.le_comap_map
    have hh := (Scheme.IdealSheafData.le_map_iff_comap_le.mp h) ⟨⊤, isAffineOpen_top X⟩
    simpa [J] using hh
  · rw [Ideal.map_le_iff_le_comap]
    have h := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
    rwa [map_top] at h

end
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specIdeal (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] lemma specIdeal_top (I : Ideal R) :
    (specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdeal]

lemma specIdeal_comap (I : Ideal R) (f : R →+* S) :
    (specIdeal I).comap (Spec.map (CommRingCat.ofHom f)) = specIdeal (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, specIdeal_top, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

lemma comap_ι_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [I.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (I.map_ideal (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩)
    (V := U) (show U.1.ι ''ᵁ ⊤ ≤ U.1 from U.1.ι_image_top.le)).symm

lemma comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V.1 U.1 e).hom := by
  suffices hh : ((I.comap f).ideal U).map U.1.topIso.inv.hom =
      ((I.ideal V).map (f.appLE V.1 U.1 e).hom).map U.1.topIso.inv.hom by
    have hh' := congrArg (Ideal.map U.1.topIso.hom.hom) hh
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id, CommRingCat.hom_id,
      Ideal.map_id] using hh'
  rw [← comap_ι_top, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.Hom.resLE_comp_ι f e, Scheme.IdealSheafData.comap_comp,
    comap_top, comap_ι_top, Ideal.map_map, Ideal.map_map]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.hom_comp,
    Iso.inv_hom_id_assoc]

end IdealPullback
namespace InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}
lemma invertible_of_local_equations
    (hf : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      obtain ⟨U, hyU, r, hr, hIr⟩ := hf y
      exact ⟨U.1, hyU, IdealModule.frame_restriction (I.comap f) U.1.ι r hIr hr.1⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry

theorem invertible_of_affine_equations {X : Scheme} (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    InvertiblePullbackIdeal I (𝟙 X) := by
  apply invertible_of_local_equations
  intro x
  obtain ⟨U, hx, r, hr, he⟩ := hI x
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have hreg : IsLeftRegular (e.symm r) := by
    intro a b hab
    apply e.injective
    apply hr.1
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  refine ⟨U, hx, e.symm r, ⟨hreg, hreg.right_of_commute (fun a => mul_comm _ a)⟩, ?_⟩
  rw [Scheme.IdealSheafData.comap_id, IdealPullback.comap_ι_top, he,
    Ideal.map_span, Set.image_singleton]
  rfl

end InvertibleLocal

end PiExponentSeshadri

end

end OAI
