import OAI.Algebra.AuslanderReiten.Duality.RightDual
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

noncomputable section
namespace ArExplicit.RightDualHomology
universe u
variable {k R U V W : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]

variable (f : U →ₗ[Rᵐᵒᵖ] V) (g : V →ₗ[Rᵐᵒᵖ] W) (h : g.comp f = 0)

def cycleMap : U →ₗ[Rᵐᵒᵖ] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (fun x => LinearMap.congr_fun h x)

def boundaries : Submodule Rᵐᵒᵖ (LinearMap.ker g) := LinearMap.range (cycleMap f g h)

abbrev Homology := LinearMap.ker g ⧸ boundaries f g h

def cyclesToDualHomology : LinearMap.ker (RightDual.map (k := k) f) →ₗ[R]
    RightDual k R (Homology f g h) where
  toFun φ := ⟨((boundaries f g h).restrictScalars k).liftQ
    (φ.val.functional.comp ((LinearMap.ker g).subtype.restrictScalars k)) (by
      rintro _ ⟨x, rfl⟩
      exact congrArg (fun ψ : RightDual k R U => ψ.functional x) φ.property)⟩
  map_add' φ ψ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl
  map_smul' r φ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl

omit [Module k W] [IsScalarTower k Rᵐᵒᵖ W] in
@[simp] theorem cyclesToDualHomology_mk
    (φ : LinearMap.ker (RightDual.map (k := k) f)) (x : LinearMap.ker g) :
    (cyclesToDualHomology f g h φ).functional ((boundaries f g h).mkQ x) =
      φ.val.functional x.val := rfl

omit [Module k W] [IsScalarTower k Rᵐᵒᵖ W] in
theorem cyclesToDualHomology_surjective :
    Function.Surjective (cyclesToDualHomology (k := k) f g h) := by
  intro l
  let ℓ : ((LinearMap.ker g).restrictScalars k) →ₗ[k] k :=
    l.functional.comp ((boundaries f g h).mkQ.restrictScalars k)
  obtain ⟨φ, hφ⟩ := ℓ.exists_extend
  have hp : (RightDual.mk φ : RightDual k R V) ∈ LinearMap.ker (RightDual.map (k := k) f) := by
    apply RightDual.ext
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hφ (cycleMap f g h x)
    change φ (f x) = 0
    change φ (f x) = l.functional ((boundaries f g h).mkQ (cycleMap f g h x)) at hx
    rw [show (boundaries f g h).mkQ (cycleMap f g h x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero] at hx
    exact hx
  refine ⟨⟨⟨φ⟩, hp⟩, ?_⟩
  apply RightDual.ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
  exact LinearMap.congr_fun hφ x

def dualCycleMap : RightDual k R W →ₗ[R] LinearMap.ker (RightDual.map (k := k) f) :=
  (RightDual.map g).codRestrict _ (by
    intro ψ
    apply RightDual.ext
    ext x
    change ψ.functional (g (f x)) = 0
    have hx : g (f x) = 0 := LinearMap.congr_fun h x
    rw [hx, map_zero])

def dualBoundaries : Submodule R (LinearMap.ker (RightDual.map (k := k) f)) :=
  LinearMap.range (dualCycleMap f g h)

abbrev DualHomology := LinearMap.ker (RightDual.map (k := k) f) ⧸ dualBoundaries f g h

theorem cyclesToDualHomology_kernel :
    LinearMap.ker (cyclesToDualHomology (k := k) f g h) = dualBoundaries f g h := by
  ext φ
  constructor
  · intro hφ
    have ha : φ.val.functional ∈ (LinearMap.ker (g.restrictScalars k)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact congrArg (fun l : RightDual k R (Homology f g h) =>
        l.functional ((boundaries f g h).mkQ ⟨x, hx⟩)) hφ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨⟨ψ⟩, Subtype.ext (RightDual.ext hψ)⟩
  · rintro ⟨ψ, rfl⟩
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    change ψ.functional (g x.val) = 0
    rw [x.property, map_zero]

def dualHomologyEquiv : RightDual k R (Homology f g h) ≃ₗ[R] DualHomology (k := k) f g h :=
  ((Submodule.quotEquivOfEq _ _ (cyclesToDualHomology_kernel f g h).symm).trans
    ((cyclesToDualHomology f g h).quotKerEquivOfSurjective
      (cyclesToDualHomology_surjective f g h))).symm

end ArExplicit.RightDualHomology

end

end OAI
