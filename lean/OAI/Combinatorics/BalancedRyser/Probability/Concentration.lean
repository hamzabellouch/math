import Mathlib.Probability.Martingale.Basic

namespace OAI

open MeasureTheory Real
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

universe u

def BoundedDriftConcentration : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ),
    1 ≤ T → 0 < L →
    (∀ j ≤ T, StronglyMeasurable[ℱ j] (X j)) →
    (∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L) →
    ∀ (u : ℝ), 0 < u → ∀ (t : ℕ), t ≤ T →
      μ.real {ω | u ≤ |X t ω - X 0 ω - ∑ j ∈ Finset.range t,
        μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω|} ≤
        2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2))

end Balanced

end OAI
