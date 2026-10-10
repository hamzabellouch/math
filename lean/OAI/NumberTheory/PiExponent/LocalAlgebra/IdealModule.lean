import OAI.NumberTheory.PiExponent.Approximation.FrameSections

namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

section
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

section
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

section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme}
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

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end PiExponentSeshadri.IdealModule

end

end OAI
