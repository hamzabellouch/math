import OAI.NumberTheory.PiExponent.Cohomology.CechLinear

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem sectionZero_restrict (c : CechHigher.Cochain R U M 0) (t : Fin 1 → J) :
    restrictHom R (iInf_le (fun j => U (t j)) 0) (sectionZero R U M c (t 0)) = c t := by
  simp only [sectionZero]
  erw [restrictHom_restrictHom]
  have ht : (fun _ : Fin 1 => t 0) = t := by
    funext k
    exact congrArg t (Subsingleton.elim 0 k)
  exact (restrict_cochain_congr R U M c ht
    ((iInf_le (fun j => U (t j)) 0).trans (le_iInf fun _ => le_rfl)) (le_refl _)).trans
    (restrictHom_refl R M (c t))

theorem sectionZero_injective : Function.Injective (sectionZero R U M) := by
  intro c d h
  funext t
  rw [← sectionZero_restrict R U M c t, ← sectionZero_restrict R U M d t, h]

theorem augmentation_injective (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    Function.Injective (augmentation R U M V hUV) := by
  intro f g h
  apply hom_ext R U V hUV hcover M f g
  intro i
  have hi := congrArg (fun c => sectionZero R U M c i) h
  simpa only [sectionZero_augmentation] using hi

theorem augmentation_exists (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : CechHigher.Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ f : freeOpen R V ⟶ M, augmentation R U M V hUV f = c := by
  obtain ⟨f, hf⟩ := glue_zero_cocycle R U M V hUV hcover c hc
  refine ⟨f, sectionZero_injective R U M ?_⟩
  funext i
  rw [sectionZero_augmentation]
  exact hf i

theorem augmentation_comp (V : Opens X) (hUV : ∀ i, U i ≤ V)
    {N : SheafOfModules.{u} R} (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    augmentation R U N V hUV (f ≫ g) =
      CechHigher.map R U M g (augmentation R U M V hUV f) := by
  funext t
  exact restrictHom_comp R _ f g

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry

variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤)) (M : X.Modules)

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

def augmentationLinear (V : X.Opens) (hUV : ∀ i, U i ≤ V) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) →ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  refine {
    toFun := fun f => ⟨CechHigher.augmentation X.ringCatSheaf U M V hUV f,
      CechHigher.augmentation_closed X.ringCatSheaf U M V hUV f⟩
    map_add' := ?_
    map_smul' := ?_ }
  · intro f g
    apply Subtype.ext
    funext t
    exact CechOne.restrictHom_add X.ringCatSheaf _ f g
  · intro r f
    apply Subtype.ext
    funext t
    exact Linear.comp_smul (C := X.Modules) _ _ _
      (freeOpenMap X.ringCatSheaf
        (homOfLE ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))))) (ρ r) f

@[simp] theorem augmentationLinear_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (f : schemeFreeOpen V ⟶ M) :
    (augmentationLinear U ρ M V hUV f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

def sectionsEquiv (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) ≃ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  apply LinearEquiv.ofBijective (augmentationLinear U ρ M V hUV)
  constructor
  · intro f g h
    exact augmentation_injective X.ringCatSheaf U M V hUV hcover (congrArg Subtype.val h)
  · intro c
    obtain ⟨f, hf⟩ := augmentation_exists X.ringCatSheaf U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩

@[simp] theorem sectionsEquiv_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : schemeFreeOpen V ⟶ M) :
    (sectionsEquiv U ρ M V hUV hcover f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

theorem sectionsEquiv_symm_restrict (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : CechLinear.cycles U ρ M 0) (i : J) :
    CechOne.restrictHom X.ringCatSheaf (hUV i)
        ((sectionsEquiv U ρ M V hUV hcover).symm c) =
      CechHigher.sectionZero X.ringCatSheaf U M c.val i := by
  have h := congrArg
    (fun d : CechLinear.cycles U ρ M 0 => CechHigher.sectionZero X.ringCatSheaf U M d.val i)
    ((sectionsEquiv U ρ M V hUV hcover).apply_symm_apply c)
  simp only [sectionsEquiv_val] at h
  exact (CechHigher.sectionZero_augmentation X.ringCatSheaf U M V hUV
    ((sectionsEquiv U ρ M V hUV hcover).symm c) i).symm.trans h

theorem sectionsEquiv_comp (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules}
    (f : schemeFreeOpen V ⟶ M) (g : M ⟶ N) :
    sectionsEquiv U ρ N V hUV hcover (f ≫ g) =
      CechLinear.mapCycles U ρ g 0 (sectionsEquiv U ρ M V hUV hcover f) := by
  apply Subtype.ext
  exact augmentation_comp X.ringCatSheaf U M V hUV f g

theorem sectionsEquiv_symm_mapCycles (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules} (g : M ⟶ N)
    (c : CechLinear.cycles U ρ M 0) :
    (sectionsEquiv U ρ N V hUV hcover).symm (CechLinear.mapCycles U ρ g 0 c) =
      (sectionsEquiv U ρ M V hUV hcover).symm c ≫ g := by
  apply (sectionsEquiv U ρ N V hUV hcover).injective
  rw [LinearEquiv.apply_symm_apply, sectionsEquiv_comp, LinearEquiv.apply_symm_apply]

end PiExponent.GeometrySupport.CechZero

end

end OAI
