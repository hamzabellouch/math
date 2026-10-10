import OAI.Algebra.AuslanderReiten.Stable.CanonicalCosyzygy
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory
open scoped TensorProduct

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def canonicalFreeCover (Y : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (R ⊗[k] Y.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstanceAs (Module.Finite k (R ⊗[k] Y.carrier))

private def freeCoverMapScalar (Y : FiniteLeftModule k R) : R ⊗[k] Y.carrier →ₗ[k] Y.carrier :=
  TensorProduct.lift
    { toFun := fun r =>
        { toFun := fun y => r • y
          map_add' := smul_add r
          map_smul' := fun a y => by
            rw [← IsScalarTower.algebraMap_smul R a y, ← mul_smul,
              ← Algebra.commutes, mul_smul, IsScalarTower.algebraMap_smul]
            rfl }
      map_add' := fun r s => by ext y; exact add_smul r s y
      map_smul' := fun a r => by ext y; exact smul_assoc a r y }

def canonicalFreeCoverMap (Y : FiniteLeftModule k R) : Y.canonicalFreeCover.carrier ⟶ Y.carrier :=
  ModuleCat.ofHom
    { __ := (freeCoverMapScalar Y).toAddHom
      map_smul' r z := by
        change freeCoverMapScalar Y (r • z) = r • freeCoverMapScalar Y z
        induction z using TensorProduct.inductionOn with
        | add x y hx hy => simp [smul_add, hx, hy]
        | tmul s y => exact mul_smul r s y }

@[simp] theorem canonicalFreeCoverMap_tmul (Y : FiniteLeftModule k R) (r : R) (y : Y.carrier) :
    Y.canonicalFreeCoverMap.hom (r ⊗ₜ[k] y) = r • y := rfl

theorem canonicalFreeCoverMap_surjective (Y : FiniteLeftModule k R) :
    Function.Surjective Y.canonicalFreeCoverMap.hom := by
  intro y
  exact ⟨1 ⊗ₜ[k] y, one_smul R y⟩

theorem canonicalFreeCover_finite (Y : FiniteLeftModule k R) :
    Module.Finite R Y.canonicalFreeCover.carrier :=
  Module.Finite.of_basis ((Module.finBasis k Y.carrier).baseChange R)

theorem canonicalFreeCover_projective (Y : FiniteLeftModule k R) :
    Module.Projective R Y.canonicalFreeCover.carrier := by
  change Module.Projective R (R ⊗[k] Y.carrier)
  infer_instance

variable (U₁ U₂ Y : FiniteLeftModule k R)

def fiberSource : FiniteLeftModule k R where
  carrier := ModuleCat.of R (U₁.carrier × U₂.carrier × Y.canonicalFreeCover.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

def fiberMap (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    (fiberSource U₁ U₂ Y).carrier ⟶ Y.carrier :=
  ModuleCat.ofHom (g₁.hom.coprod (g₂.hom.coprod Y.canonicalFreeCoverMap.hom))

theorem fiberMap_surjective (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    Function.Surjective (fiberMap U₁ U₂ Y g₁ g₂).hom := by
  intro y
  obtain ⟨z, hz⟩ := canonicalFreeCoverMap_surjective Y y
  refine ⟨(0, 0, z), ?_⟩
  change g₁.hom 0 + (g₂.hom 0 + Y.canonicalFreeCoverMap.hom z) = y
  simpa using hz

def fiber (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) : FiniteLeftModule k R where
  carrier := kernelObject (fiberMap U₁ U₂ Y g₁ g₂)
  scalar := inferInstanceAs (Module k (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom))
  tower := inferInstanceAs (IsScalarTower k R (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom))
  finite := by
    change Module.Finite k (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom)
    exact Module.Finite.of_injective
      (((LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom).subtype).restrictScalars k) Subtype.val_injective

end ArExplicit.FiniteLeftModule

end

end OAI
