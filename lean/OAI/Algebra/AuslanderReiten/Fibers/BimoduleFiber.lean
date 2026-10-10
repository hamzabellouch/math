import OAI.Algebra.AuslanderReiten.Modules.BimoduleEnveloping
import OAI.Algebra.AuslanderReiten.Fibers.FiniteFiberSides
import OAI.Algebra.AuslanderReiten.Algebras.FrobeniusOpposite

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def twistedFiniteModule (σ : R ≃ₐ[k] R) : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ) where
  carrier := bimoduleEnvelopingObject k R (TwistedBimodule k R σ)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstanceAs (Module.Finite k (TwistedBimodule k R σ))

theorem twistedFiniteModule_left (σ : R ≃ₐ[k] R) :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) ∧
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) :=
  ⟨Module.Finite.equiv (bimoduleEnvelopingLeftEquiv k R (TwistedBimodule k R σ)).symm,
    Module.Projective.of_equiv (bimoduleEnvelopingLeftEquiv k R (TwistedBimodule k R σ)).symm⟩

theorem twistedFiniteModule_right (σ : R ≃ₐ[k] R) :
    Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) ∧
    Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) :=
  ⟨Module.Finite.equiv (bimoduleEnvelopingRightEquiv k R (TwistedBimodule k R σ)).symm,
    Module.Projective.of_equiv (bimoduleEnvelopingRightEquiv k R (TwistedBimodule k R σ)).symm⟩

namespace BimoduleFiber

variable (C₁ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

abbrev target := C₁.canonicalCosyzygies 4

variable (σ₁ σ₂ : R ≃ₐ[k] R)
variable (g₁ : (twistedFiniteModule σ₁).carrier ⟶ (target C₁).carrier)
variable (g₂ : (twistedFiniteModule σ₂).carrier ⟶ (target C₁).carrier)

abbrev finiteModule : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ) :=
  FiniteLeftModule.fiber (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂

abbrev bimodule := EnvelopingBimodule k R (finiteModule C₁ σ₁ σ₂ g₁ g₂).carrier

theorem target_left (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective R R]
    [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) ∧
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) := by
  let := tensorLeftRegular_finite k R Rᵐᵒᵖ
  let := tensorLeftRegular_projective k R Rᵐᵒᵖ
  exact C₁.canonicalCosyzygies_side (tensorLeftInclusion k R Rᵐᵒᵖ) τ 4

theorem target_right (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ]
    [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) ∧
    Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) := by
  let := tensorRightRegular_finite k R Rᵐᵒᵖ
  let := tensorRightRegular_projective k R Rᵐᵒᵖ
  exact C₁.canonicalCosyzygies_side (tensorRightInclusion k R Rᵐᵒᵖ) τ 4

theorem left (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective R R]
    [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite R (bimodule C₁ σ₁ σ₂ g₁ g₂) ∧
      Module.Projective R (bimodule C₁ σ₁ σ₂ g₁ g₂) := by
  let := tensorLeftRegular_finite k R Rᵐᵒᵖ
  let := tensorLeftRegular_projective k R Rᵐᵒᵖ
  obtain ⟨hYfin, hYproj⟩ := target_left C₁ τ
  let := hYfin
  let := hYproj
  obtain ⟨hU₁fin, hU₁proj⟩ := twistedFiniteModule_left σ₁
  let := hU₁fin
  let := hU₁proj
  obtain ⟨hU₂fin, hU₂proj⟩ := twistedFiniteModule_left σ₂
  let := hU₂fin
  let := hU₂proj
  obtain ⟨hfin, hproj⟩ := FiniteLeftModule.fiber_side (tensorLeftInclusion k R Rᵐᵒᵖ)
    (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂
  let := hfin
  let := hproj
  exact ⟨inferInstance, inferInstance⟩

theorem right (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ]
    [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite Rᵐᵒᵖ (bimodule C₁ σ₁ σ₂ g₁ g₂) ∧
      Module.Projective Rᵐᵒᵖ (bimodule C₁ σ₁ σ₂ g₁ g₂) := by
  let := tensorRightRegular_finite k R Rᵐᵒᵖ
  let := tensorRightRegular_projective k R Rᵐᵒᵖ
  obtain ⟨hYfin, hYproj⟩ := target_right C₁ τ
  let := hYfin
  let := hYproj
  obtain ⟨hU₁fin, hU₁proj⟩ := twistedFiniteModule_right σ₁
  let := hU₁fin
  let := hU₁proj
  obtain ⟨hU₂fin, hU₂proj⟩ := twistedFiniteModule_right σ₂
  let := hU₂fin
  let := hU₂proj
  obtain ⟨hfin, hproj⟩ := FiniteLeftModule.fiber_side (tensorRightInclusion k R Rᵐᵒᵖ)
    (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂
  let := hfin
  let := hproj
  exact ⟨inferInstance, inferInstance⟩

end BimoduleFiber
end ArExplicit

end

end OAI
