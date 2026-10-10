import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationDiagram

namespace OAI

/-! # Concrete sequential colimits of representations

Only the two elementwise properties used in coefficient calculations are
packaged: every element comes from a stage, and zero is detected at a later
stage. They identify the cocone with the actual group-ring module colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G) (A : Rep.{0} ℤ G)

structure ColimitCocone where
  ι : ∀ i : ℕ, D.obj i ⟶ A
  comm : ∀ i j (h : i ≤ j), D.map i j h ≫ ι j = ι i
  surj : ∀ a : A, ∃ (i : ℕ) (x : D.obj i), (ι i).hom x = a
  zero_exact : ∀ (i : ℕ) (x : D.obj i), (ι i).hom x = 0 →
    ∃ (j : ℕ) (h : i ≤ j), (D.map i j h).hom x = 0

namespace ColimitCocone
variable {D A} (c : D.ColimitCocone A)

def moduleMap (i : ℕ) : (D.obj i).ρ.asModule →ₗ[ℤ[G]] A.ρ.asModule :=
  representationModuleHomEquiv ℤ G (D.obj i) A (c.ι i)

def moduleLift : D.ModuleLimit →ₗ[ℤ[G]] A.ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _ c.moduleMap (by
    intro i j h x
    change representationModuleHomEquiv ℤ G (D.obj i) A (D.map i j h ≫ c.ι j) x =
      representationModuleHomEquiv ℤ G (D.obj i) A (c.ι i) x
    rw [c.comm])

@[simp]
theorem moduleLift_of (i : ℕ) (x : (D.obj i).ρ.asModule) :
    c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i x) = c.moduleMap i x :=
  Module.DirectLimit.lift_of _ _ _

theorem moduleLift_bijective : Function.Bijective c.moduleLift := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rw [c.moduleLift_of] at hz
    have hx : (c.ι i).hom ((D.obj i).ρ.asModuleEquiv x) = 0 := by
      have he := congrArg A.ρ.asModuleEquiv hz
      exact he
    obtain ⟨j, hij, hj⟩ := c.zero_exact i ((D.obj i).ρ.asModuleEquiv x) hx
    have he : D.moduleMap i j hij x = 0 := by
      apply (D.obj j).ρ.asModuleEquiv.injective
      exact hj
    have hc := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
      (G := fun i => (D.obj i).ρ.asModule) (f := D.moduleMap) (hij := hij) (x := x)
    rw [he, map_zero] at hc
    exact hc.symm
  · intro a
    obtain ⟨i, x, hx⟩ := c.surj (A.ρ.asModuleEquiv a)
    refine ⟨Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i
      ((D.obj i).ρ.asModuleEquiv.symm x), ?_⟩
    rw [c.moduleLift_of]
    apply A.ρ.asModuleEquiv.injective
    exact hx

def moduleEquiv : D.ModuleLimit ≃ₗ[ℤ[G]] A.ρ.asModule :=
  LinearEquiv.ofBijective c.moduleLift c.moduleLift_bijective

theorem lift_finitelyPresented (B : Rep.{0} ℤ G)
    [Module.FinitePresentation ℤ[G] B.ρ.asModule] (u : B ⟶ A) :
    ∃ (i : ℕ) (v : B ⟶ D.obj i), v ≫ c.ι i = u := by
  let u' := representationModuleHomEquiv ℤ G B A u
  obtain ⟨i, v, hv⟩ := sequentialLimit_lift_finitelyPresented D.moduleMap
    (c.moduleEquiv.symm.toLinearMap.comp u')
  refine ⟨i, (representationModuleHomEquiv ℤ G B (D.obj i)).symm v, ?_⟩
  apply (representationModuleHomEquiv ℤ G B A).injective
  apply LinearMap.ext
  intro b
  have he := LinearMap.congr_fun hv b
  have he' := congrArg c.moduleEquiv he
  change c.moduleEquiv (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (v b)) =
    c.moduleEquiv (c.moduleEquiv.symm (u' b)) at he'
  rw [c.moduleEquiv.apply_symm_apply] at he'
  change c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (v b)) = u' b at he'
  rw [c.moduleLift_of] at he'
  exact he'

theorem eventually_zero_hom (B : Rep.{0} ℤ G) [Module.Finite ℤ[G] B.ρ.asModule]
    (i : ℕ) (u : B ⟶ D.obj i) (hu : u ≫ c.ι i = 0) :
    ∃ (j : ℕ) (hij : i ≤ j), u ≫ D.map i j hij = 0 := by
  let u' := representationModuleHomEquiv ℤ G B (D.obj i) u
  have hz : (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i).comp u' = 0 := by
    apply LinearMap.ext
    intro b
    apply c.moduleLift_bijective.1
    change c.moduleLift (Module.DirectLimit.of ℤ[G] ℕ _ D.moduleMap i (u' b)) = c.moduleLift 0
    rw [map_zero]
    rw [c.moduleLift_of]
    have he := congrArg (fun f => representationModuleHomEquiv ℤ G B A f b) hu
    exact he
  obtain ⟨j, hij, hj⟩ := sequentialLimit_eventually_zero_finite D.moduleMap i u' hz
  refine ⟨j, hij, ?_⟩
  apply (representationModuleHomEquiv ℤ G B (D.obj j)).injective
  exact hj

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
