import OAI.NumberTheory.PiExponent.Cohomology.CechZero

namespace OAI

namespace PiExponent.GeometrySupport.CechZeroAdditive
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def differentialHom (q : ℕ) : Cochain R U M q →+ Cochain R U M (q + 1) where
  toFun := differential R U M
  map_zero' := differential_zero R U M
  map_add' c b := by
    funext t
    simp only [differential, Pi.add_apply, restrictHom_add, smul_add, Finset.sum_add_distrib]

def cycles (q : ℕ) : AddSubgroup (Cochain R U M q) := (differentialHom R U M q).ker

@[simp] theorem mem_cycles (q : ℕ) (c : Cochain R U M q) :
    c ∈ cycles R U M q ↔ differential R U M c = 0 := Iff.rfl

def augmentationHom (V : Opens X) (hUV : ∀ i, U i ≤ V) :
    (freeOpen R V ⟶ M) →+ cycles R U M 0 where
  toFun f := ⟨augmentation R U M V hUV f, augmentation_closed R U M V hUV f⟩
  map_zero' := by
    apply Subtype.ext
    funext t
    exact comp_zero
  map_add' f g := by
    apply Subtype.ext
    funext t
    exact restrictHom_add R _ f g

def sectionsEquiv (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    (freeOpen R V ⟶ M) ≃+ cycles R U M 0 :=
  AddEquiv.ofBijective (augmentationHom R U M V hUV) ⟨by
    intro f g hfg
    exact CechZero.augmentation_injective R U M V hUV hcover (congrArg Subtype.val hfg), by
    intro c
    obtain ⟨f, hf⟩ := CechZero.augmentation_exists R U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem sectionsEquiv_val (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : freeOpen R V ⟶ M) :
    (sectionsEquiv R U M V hUV hcover f).val = augmentation R U M V hUV f := rfl

end
end PiExponent.GeometrySupport.CechZeroAdditive

end OAI
