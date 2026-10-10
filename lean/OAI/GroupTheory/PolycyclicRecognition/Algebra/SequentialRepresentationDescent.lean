import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit

namespace OAI

/-! # Descent of compatible maps out of a concrete sequential colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
variable (c : D.ColimitCocone A) (B : Rep.{0} ℤ G)
variable (f : ∀ i, D.obj i ⟶ B)
variable (hf : ∀ i j (h : i ≤ j), D.map i j h ≫ f j = f i)

def descentModuleMap : D.ModuleLimit →ₗ[ℤ[G]] B.ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _
    (fun i => representationModuleHomEquiv ℤ G (D.obj i) B (f i)) (by
      intro i j h x
      change representationModuleHomEquiv ℤ G (D.obj i) B (D.map i j h ≫ f j) x = _
      rw [hf])

def desc : A ⟶ B :=
  (representationModuleHomEquiv ℤ G A B).symm
    ((descentModuleMap B f hf).comp c.moduleEquiv.symm.toLinearMap)

@[reassoc (attr := simp)]
theorem ι_desc (i : ℕ) : c.ι i ≫ c.desc B f hf = f i := by
  apply (representationModuleHomEquiv ℤ G (D.obj i) B).injective
  apply LinearMap.ext
  intro x
  have he : c.moduleEquiv.symm (c.moduleMap i x) =
      Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i x := by
    apply c.moduleEquiv.injective
    rw [c.moduleEquiv.apply_symm_apply]
    exact (c.moduleLift_of i x).symm
  change descentModuleMap B f hf (c.moduleEquiv.symm (c.moduleMap i x)) = _
  rw [he]
  exact Module.DirectLimit.lift_of _ _ _

theorem hom_ext {f g : A ⟶ B} (h : ∀ i, c.ι i ≫ f = c.ι i ≫ g) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  obtain ⟨i, x, rfl⟩ := c.surj a
  exact ConcreteCategory.congr_hom (h i) x

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
