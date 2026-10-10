import Mathlib

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped BigOperators unitInterval NNReal

noncomputable def coordinateAverage {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → I) → ℝ) (x : Fin n → I) : ℝ := by
  classical
  exact ∫ y : Fin n → I, f (fun i => if i ∈ S then x i else y i)

def CubeJuntaStatement : Prop :=
  ∀ L : ℝ≥0, ∀ τ : ℝ, 0 < τ → ∃ J : ℕ, 1 ≤ J ∧
    ∀ n : ℕ, 0 < n → ∀ f : (Fin n → I) → ℝ,
      LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        Integrable (fun x => (f x - coordinateAverage S f x)^2) ∧
        (∫ x, (f x - coordinateAverage S f x)^2) < τ^2

end LargeIndependentSets

end OAI
