import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Cohomology.AffineVanishing

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.IdealModule
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureMap : unit Y ⟶
    (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] lemma structureMap_app (U : Y.Opens) (x : Γ(Y, U)) :
    ((structureMap f).val.app (op U)) x = (f.app U) x := rfl

def idealModule : Y.Modules := kernel (structureMap f)

def inclusion : idealModule f ⟶ unit Y :=
  kernel.ι (structureMap f)

instance : Mono (inclusion f) := inferInstanceAs (Mono (kernel.ι (structureMap f)))

def sectionsKernelIso (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≅
      ModuleCat.of (Y.ringCatSheaf.obj.obj (op U))
        ((structureMap f).val.app (op U)).hom.ker :=
  PreservesKernel.iso
    (Scheme.Modules.toPresheafOfModules Y ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)) (structureMap f) ≪≫
    ModuleCat.kernelIsoKer _

lemma sectionsKernelIso_inclusion (U : Y.Opens) :
    (sectionsKernelIso f U).hom ≫
      ModuleCat.ofHom ((structureMap f).val.app (op U)).hom.ker.subtype =
        (inclusion f).val.app (op U) := by
  let E := Scheme.Modules.toPresheafOfModules Y ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)
  change ((PreservesKernel.iso E (structureMap f)).hom ≫
    (ModuleCat.kernelIsoKer (E.map (structureMap f))).hom) ≫
      ModuleCat.ofHom (E.map (structureMap f)).hom.ker.subtype =
        E.map (kernel.ι (structureMap f))
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

lemma image_eq_kernel (U : Y.Opens) :
    ((inclusion f).val.app (op U)).hom.range = RingHom.ker (f.app U).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (f.app U) (((inclusion f).val.app (op U)) y) = 0
    have h := congrArg (fun g => (g.val.app (op U)) y)
      (kernel.condition (structureMap f))
    exact h
  · intro hx
    let y : ((structureMap f).val.app (op U)).hom.ker := ⟨x, hx⟩
    refine ⟨(sectionsKernelIso f U).inv y, ?_⟩
    have h := congrArg (fun g => g ((sectionsKernelIso f U).inv y))
      (sectionsKernelIso_inclusion f U)
    simpa using h.symm

lemma image_eq_ideal [QuasiCompact f] (U : Y.affineOpens) :
    ((inclusion f).val.app (op U.1)).hom.range = f.ker.ideal U := by
  rw [image_eq_kernel, Scheme.Hom.ker_apply]

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def closedModule (I : X.IdealSheafData) : X.Modules := idealModule I.subschemeι

def closedInclusion (I : X.IdealSheafData) : closedModule I ⟶ unit X :=
  inclusion I.subschemeι

lemma closed_image (I : X.IdealSheafData) (U : X.affineOpens) :
    ((closedInclusion I).val.app (op U.1)).hom.range = I.ideal U := by
  exact (image_eq_ideal I.subschemeι U).trans (congrArg (fun J => J.ideal U) I.ker_subschemeι)

lemma isIso_of_affine_app {M N : X.Modules} (g : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso (g.app U.1)) : IsIso g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hb : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => U.val) := by
    simpa using X.isBasis_affineOpens
  have hg : IsIso (F.map g) := TopCat.Sheaf.isIso_iff_isIso_basis hb h
  let : IsIso ((Scheme.Modules.toPresheaf X).map g) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ AddCommGrpCat).map (F.map g)))
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf X)

def multiply (r : Γ(X, ⊤)) : unit X ⟶ unit X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma multiply_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (multiply r).val.app (op U) a = X.presheaf.map (homOfLE le_top).op r * a := rfl

lemma multiply_structure_zero (f : Y ⟶ X) (r : Γ(X, ⊤))
    (hr : (f.app ⊤) r = 0) : multiply r ≫ structureMap f = 0 := by
  ext U a
  change Γ(X, U) at a
  change (f.app U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) *
    (a : Γ(X, U))) = 0
  rw [map_mul]
  have he : (f.app U) (X.presheaf.map (homOfLE le_top).op r) = 0 := by
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, hr, map_zero]
  rw [he, zero_mul]

def equationToIdeal (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    unit X ⟶ idealModule f :=
  kernel.lift (structureMap f) (multiply r) (multiply_structure_zero f r hr)

@[reassoc (attr := simp)] lemma equationToIdeal_inclusion
    (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    equationToIdeal f r hr ≫ inclusion f = multiply r := kernel.lift_ι _ _ _

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

noncomputable section
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
  exact he.trans ((congrArg (fun value : Γ(X, U) => a * value)
    (hn.trans (congrArg (X.presheaf.map (homOfLE le_top).op) hs))).trans (mul_comm _ _))

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

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (f r) := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : IsSMulRegular S r := Module.Flat.isSMulRegular_of_isRegular
    ⟨hr, hr.right_of_commute (fun a => mul_comm r a)⟩
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hh

lemma restriction_regular [IsAffine X] (r : Γ(X, ⊤)) (hr : IsLeftRegular r)
    (U : X.affineOpens) :
    IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r) := by
  apply regular_map_flat _ _ hr
  simpa [Scheme.Hom.appLE] using
    Scheme.Hom.flat_appLE (𝟙 X) (isAffineOpen_top X) U.2 (show U.1 ≤ (𝟙 X) ⁻¹ᵁ ⊤ from le_top)

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    MaximalSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  let unitIso : (unit Y).restrict f ≅ unit X := Scheme.Modules.restrictUnitIso f
  exact mono_comp ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) unitIso.hom

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
  refine Iff.trans ?_ (Iff.of_eq (congrArg
    (fun ideal : Ideal Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).inv r ∈ ideal)
    (closed_image I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩)))
  change (∃ s, _) ↔ ∃ s, (closedInclusion I).val.app (op (f ''ᵁ U.1)) s = (f.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (congrArg (fun k : Γ(Y, f ''ᵁ U.1) ⟶ Γ(Y, f ''ᵁ U.1) => k ((closedInclusion I).val.app (op (f ''ᵁ U.1)) s))
      (f.appIso U.1).hom_inv_id).symm.trans
        (congrArg (f.appIso U.1).inv ((restrictedInclusion_app I f U.1 s).symm.trans hs))
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (restrictedInclusion_app I f U.1 s).trans
      ((congrArg (f.appIso U.1).hom hs).trans
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

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def frameOnRange (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
    (e : M.restrict f ≅ unit X) : M.restrict f.opensRange.ι ≅ unit f.opensRange.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.restrictFunctor f.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso f.isoOpensRange.inv

end
end MaximalSeshadri.IdealModule

namespace MaximalSeshadri.IdealPullback
noncomputable section
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

noncomputable section
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

noncomputable section
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

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry
variable (X : Scheme)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
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

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry

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

end
end MaximalSeshadri.InvertibleLocal
end


end
end

end OAI
