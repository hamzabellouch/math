import OAI.Algebra.AuslanderReiten.Fibers.FiniteModuleFiber
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R S : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [Ring S] (j : S →+* R)
variable (U₁ U₂ Y : FiniteLeftModule k R)

def fiberSourceSideEquiv :
    ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) ≃ₗ[S]
      (((ModuleCat.restrictScalars j).obj U₁.carrier) ×
        ((ModuleCat.restrictScalars j).obj U₂.carrier) ×
        ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]

theorem canonicalFreeCover_side :
    Module.Finite S ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier) := by
  let := canonicalFreeCover_finite Y
  let := canonicalFreeCover_projective Y
  exact ⟨restrict_finite j _, restrict_projective j _⟩

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₂.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₂.carrier)]

theorem fiberSource_side :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) := by
  obtain ⟨hfin, hproj⟩ := canonicalFreeCover_side j Y
  let := hfin
  let := hproj
  exact ⟨Module.Finite.equiv (fiberSourceSideEquiv j U₁ U₂ Y).symm,
    Module.Projective.of_equiv (fiberSourceSideEquiv j U₁ U₂ Y).symm⟩

theorem fiber_side [Module.Projective S ((ModuleCat.restrictScalars j).obj Y.carrier)]
    (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (fiber U₁ U₂ Y g₁ g₂).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (fiber U₁ U₂ Y g₁ g₂).carrier) := by
  obtain ⟨hfin, hproj⟩ := fiberSource_side j U₁ U₂ Y
  let := hfin
  let := hproj
  exact ⟨kernel_restrict_finite j (fiberMap U₁ U₂ Y g₁ g₂)
      (fiberMap_surjective U₁ U₂ Y g₁ g₂),
    kernel_restrict_projective j (fiberMap U₁ U₂ Y g₁ g₂)
      (fiberMap_surjective U₁ U₂ Y g₁ g₂)⟩

variable (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier)

def fiberInclusion : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ (fiberSource U₁ U₂ Y).carrier :=
  ModuleCat.ofHom (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom).subtype

def fiberProjection₁ : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ U₁.carrier :=
  fiberInclusion U₁ U₂ Y g₁ g₂ ≫ ModuleCat.ofHom (LinearMap.fst R _ _)

def fiberProjection₂ : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ U₂.carrier :=
  fiberInclusion U₁ U₂ Y g₁ g₂ ≫ ModuleCat.ofHom
    ((LinearMap.fst R _ _).comp (LinearMap.snd R _ _))

def fiberSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (fiberInclusion U₁ U₂ Y g₁ g₂) (fiberMap U₁ U₂ Y g₁ g₂) (by
    ext x
    exact x.property)

theorem fiberSequence_shortExact : (fiberSequence U₁ U₂ Y g₁ g₂).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property)
  mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (fiberMap_surjective U₁ U₂ Y g₁ g₂)

end ArExplicit.FiniteLeftModule

end

end OAI
