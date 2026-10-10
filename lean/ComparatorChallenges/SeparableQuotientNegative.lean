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

theorem negative_main (hCH : CH) : ¬ SQ.{u} ℝ ∧ ¬ SQ.{u} ℂ := by
  sorry

end SeparableQuotient

end OAI
