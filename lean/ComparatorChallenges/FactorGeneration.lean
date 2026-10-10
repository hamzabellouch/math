import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section

namespace Generator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [-instance] instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace

def WOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S}

def wstar (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  sInf {S | WOTClosed S ∧ s ⊆ S}

structure IsII1Factor (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop where
  nonzero : (0 : H →L[ℂ] H) ≠ 1
  weaklyClosed : WOTClosed S
  factor : ∀ x : S, (∀ y : S, y * x = x * y) → ∃ c : ℂ, x = algebraMap ℂ S c
  finite : ∀ v : S, star v * v = 1 → v * star v = 1
  diffuse : ∀ p : S, IsStarProjection p → p ≠ 0 →
    ∃ q : S, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

def HasSeparablePredual (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (_ : TopologicalSpace.SeparableSpace X),
    Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

def SinglyGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ x ∈ S, wstar {x} = S

attribute [instance] instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace

theorem single_generation_of_II1_separable_predual
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (hsep : HasSeparablePredual S) : SinglyGenerated S := by
  sorry

end Generator

end

end OAI
