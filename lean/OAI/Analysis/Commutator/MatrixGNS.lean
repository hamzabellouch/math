import Mathlib
import OAI.Analysis.Commutator.CenteredSpace
import OAI.Analysis.Commutator.MatrixTrace
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

noncomputable def stageVector : Matrix I I ℂ →ₗ[ℂ] τ.GNS :=
  (algebraVector τ).comp φ.toLinearMap

noncomputable def centeredStageVector : Matrix I I ℂ →ₗ[ℂ] centeredSpace (vacuum τ) :=
  (center (vacuum τ)).toLinearMap.comp (stageVector τ φ)

omit [StarOrderedRing A] in
include hτ h1 in
lemma stage_trace (a : Matrix I I ℂ) :
    τ (φ a) = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  apply MatrixTrace.unique (τ.toLinearMap.comp φ.toLinearMap)
  · intro x y
    change τ (φ (x*y)) = τ (φ (y*x))
    simpa only [map_mul] using hτ (φ x) (φ y)
  · change τ (φ 1) = 1
    simpa using h1

include hτ h1 in
lemma stage_inner (a b : Matrix I I ℂ) :
    inner ℂ (stageVector τ φ a) (stageVector τ φ b) =
      (Fintype.card I : ℂ)⁻¹ * (star a * b).trace := by
  change inner ℂ (algebraVector τ (φ a)) (algebraVector τ (φ b)) = _
  rw [inner_algebraVector, ← map_star, ← map_mul, stage_trace τ hτ h1 φ]

omit [Nonempty I] in
lemma stage_vacuum : stageVector τ φ 1 = vacuum τ := by
  change algebraVector τ (φ 1) = vacuum τ
  rw [map_one]
  rfl

include hτ h1 in
lemma stage_centered (a : Matrix I I ℂ) :
    (centeredStageVector τ φ a : τ.GNS) =
      stageVector τ φ a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • vacuum τ := by
  change (center (vacuum τ) (algebraVector τ (φ a)) : τ.GNS) = _
  rw [coe_center _ (vacuum_norm τ h1), inner_vacuum_algebraVector,
    stage_trace τ hτ h1 φ]
  rfl

def stageUnitary (u : unitary (Matrix I I ℂ)) : unitary A :=
  ⟨φ u, Unitary.map_mem φ u.property⟩

omit [Nonempty I] in
lemma stage_conjugation (u : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    conjugation τ hτ (stageUnitary φ u) (stageVector τ φ a) =
      stageVector τ φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ)) := by
  change conjugation τ hτ (stageUnitary φ u)
    (τ.toPreGNS (φ a) : τ.GNS) = (_ : τ.GNS)
  rw [conjugation_coe]
  change (τ.toPreGNS ((φ (u : Matrix I I ℂ)) * φ a * star (φ (u : Matrix I I ℂ))) : τ.GNS) =
    (τ.toPreGNS (φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ))) : τ.GNS)
  simp only [map_mul, map_star]

omit [Nonempty I] in
include h1 in
lemma centered_stage_conjugation (u : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    centeredIsometry (vacuum τ) (conjugation τ hτ (stageUnitary φ u))
      (conjugation_vacuum τ hτ _) (centeredStageVector τ φ a) =
      centeredStageVector τ φ ((u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ)) := by
  change centeredIsometry _ _ _ (center _ (stageVector τ φ a)) = _
  rw [centeredIsometry_center _ (vacuum_norm τ h1), stage_conjugation]
  rfl

end Kadison.TracialGNS
end

end OAI
