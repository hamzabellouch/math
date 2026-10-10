import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.Dual

namespace OAI

noncomputable section
namespace Invariant233

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def HasOnlyTrivialInvariantProjections (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) : Prop :=
  ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
    (1 - p) * T * p = 0 → p = 0 ∨ p = 1

def IsProjectionAtom (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  p ∈ M ∧ IsStarProjection p ∧ p ≠ 0 ∧
    ∀ q : H →L[ℂ] H, q ∈ M → IsStarProjection q → q * p = q →
      q = 0 ∨ q = p

def IsAtomicVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p → p ≠ 0 →
    ∃ q : H →L[ℂ] H, IsProjectionAtom M q ∧ q * p = q

def IsAbelianVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ A B : H →L[ℂ] H, A ∈ M → B ∈ M → Commute A B

def IsDiffuseVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : H →L[ℂ] H, ¬ IsProjectionAtom M p

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  Nontrivial H ∧ ∀ A : H →L[ℂ] H, A ∈ M →
    (∀ B : H →L[ℂ] H, B ∈ M → Commute A B) →
      ∃ c : ℂ, A = c • (1 : H →L[ℂ] H)

def vectorTrace (ξ : H) (A : H →L[ℂ] H) : ℂ :=
  @inner ℂ H InnerProductSpace.toInner ξ (A ξ)

def IsFaithfulTracialVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  ‖ξ‖ = 1 ∧
    (∀ A B : H →L[ℂ] H, A ∈ M → B ∈ M →
      vectorTrace ξ (A * B) = vectorTrace ξ (B * A)) ∧
    (∀ A : H →L[ℂ] H, A ∈ M → A.IsPositive →
      vectorTrace ξ A = 0 → A = 0)

def IsTypeII1FactorWithVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  IsFactor M ∧ IsDiffuseVonNeumannAlgebra M ∧ IsFaithfulTracialVector M ξ

local instance instNormedAlgebraPredual : NormedAlgebra ℂ (H →L[ℂ] H) :=
  ContinuousLinearMap.toNormedAlgebra

def HasSeparablePredual (M : VonNeumannAlgebra H) : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (_ : TopologicalSpace.SeparableSpace X),
    Nonempty (StrongDual ℂ X ≃ₗᵢ[ℂ] M.toStarSubalgebra)

end Invariant233

end

end OAI
