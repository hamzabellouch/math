import OAI.Algebra.Finitistic.Dimension.PDCoverRadical
import OAI.Algebra.Finitistic.Dimension.PDRadical
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open Module LinearMap Submodule
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Finite-dimensional actual left modules, retaining the scalar compatibility. -/
structure FiniteModule where
  carrier : Type u
  [add : AddCommGroup carrier]
  [moduleA : Module A carrier]
  [moduleK : Module k carrier]
  [tower : IsScalarTower k A carrier]
  [finite : FiniteDimensional k carrier]
attribute [instance] FiniteModule.add FiniteModule.moduleA FiniteModule.moduleK
  FiniteModule.tower FiniteModule.finite
instance : CoeSort (FiniteModule k A) (Type u) := ⟨FiniteModule.carrier⟩

namespace FiniteModule
variable {k A}
abbrev of (M : Type u) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] : FiniteModule k A := ⟨M⟩
def cat (M : FiniteModule k A) : ModuleCat A := ModuleCat.of A M
instance (M : FiniteModule k A) : Module.Finite A M :=
  Module.Finite.of_restrictScalars_finite k A M
end FiniteModule

variable [FiniteDimensional k A]
/-- Projective covers with their actual maps and radical-kernel property. -/
structure Cover (M : FiniteModule k A) where
  source : FiniteModule k A
  [projective : Module.Projective A source]
  π : source →ₗ[A] M
  surjective : Function.Surjective π
  minimal : PDCovers.RightMinimal π
  radical : LinearMap.ker π ≤ Ring.jacobson A • (⊤ : Submodule A source)
attribute [instance] Cover.projective

variable {k A}
theorem cover_nonempty (M : FiniteModule k A) : Nonempty (Cover k A M) := by
  obtain ⟨n, S, p, hP, hp, hm, hr⟩ := PDCovers.exists_finite_projective_cover (k := k) (A := A) (N := M)
  have := hP
  have : FiniteDimensional k S := Module.Finite.of_injective
    (S.subtype.restrictScalars k) S.injective_subtype
  have : Module.Finite A S := Module.Finite.of_restrictScalars_finite k A S
  refine ⟨⟨FiniteModule.of S, p, hp, hm, ?_⟩⟩
  exact hr.trans (PDRadical.jacobson_eq_smul S).le

def cover (M : FiniteModule k A) : Cover k A M := Classical.choice (cover_nonempty M)

abbrev next (M : FiniteModule k A) : FiniteModule k A := by
  have : FiniteDimensional k (LinearMap.ker (cover M).π) :=
    Module.Finite.of_injective ((LinearMap.ker (cover M).π).subtype.restrictScalars k)
      (Submodule.injective_subtype _)
  exact FiniteModule.of (LinearMap.ker (cover M).π)

@[reducible] def syzygy (M : FiniteModule k A) : ℕ → FiniteModule k A
  | 0 => M
  | n+1 => next (syzygy M n)

abbrev term (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).source
abbrev augment (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).π

def differential (M : FiniteModule k A) (n : ℕ) : term M (n+1) →ₗ[A] term M n :=
  (LinearMap.ker (augment M n)).subtype.comp (augment M (n+1))

@[simp] theorem augment_differential (M : FiniteModule k A) (n : ℕ) :
    (augment M n).comp (differential M n) = 0 := by
  ext x
  exact (augment M (n+1) x).property

@[simp] theorem differential_comp (M : FiniteModule k A) (n : ℕ) :
    (differential M n).comp (differential M (n+1)) = 0 := by
  rw [differential, LinearMap.comp_assoc, augment_differential, LinearMap.comp_zero]

theorem range_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) = LinearMap.ker (augment M n) := by
  rw [differential, LinearMap.range_comp, LinearMap.range_eq_top.mpr (cover _).surjective,
    Submodule.map_top, Submodule.range_subtype]

theorem ker_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.ker (differential M n) = LinearMap.ker (augment M (n+1)) := by
  ext x
  change ((augment M (n+1) x : LinearMap.ker (augment M n)) : term M n) = 0 ↔
    augment M (n+1) x = 0
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg (fun z : LinearMap.ker (augment M n) => z.val) h

theorem exact_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M (n+1)) = LinearMap.ker (differential M n) := by
  rw [range_differential, ker_differential]

theorem differential_radical (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) ≤
      Ring.jacobson A • (⊤ : Submodule A (term M n)) := by
  rw [range_differential]
  exact (cover _).radical
end LittleFinitistic.PDMinimal

end

end OAI
