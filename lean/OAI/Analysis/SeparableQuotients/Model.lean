import Mathlib

namespace OAI

namespace SeparableQuotient

open MeasureTheory Cardinal

universe u

/-- The continuum hypothesis. -/
def CH : Prop := Cardinal.mk ℝ = Cardinal.aleph 1

/-- A bounded linear surjection onto an infinite-dimensional separable Banach space. -/
def HasSeparableQuotient (𝕜 : Type) [RCLike 𝕜]
    (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∃ (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace 𝕜 Y),
    CompleteSpace Y ∧ TopologicalSpace.SeparableSpace Y ∧
      (¬ FiniteDimensional 𝕜 Y) ∧ ∃ T : X →L[𝕜] Y, Function.Surjective T

/-- The separable quotient assertion at an arbitrary ambient universe. -/
def SQ (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    (¬ FiniteDimensional 𝕜 X) → HasSeparableQuotient 𝕜 X

/-- The probability measure is defined on the full powerset of the continuum.
The last clause quantifies over every smaller index set (represented as a
subset of ℝ); ENNReal tsum is the supremum of finite subsums. -/
def RealValuedMeasurableContinuum : Prop :=
  ∃ μ : @Measure ℝ ⊤,
    μ Set.univ = 1 ∧
    (∀ x : ℝ, μ {x} = 0) ∧
    ∀ (s : Set ℝ), Cardinal.mk s < Cardinal.mk ℝ →
      ∀ (A : s → Set ℝ), Pairwise (fun i j => Disjoint (A i) (A j)) →
        μ (⋃ i, A i) = ∑' i, μ (A i)

end SeparableQuotient

end OAI
