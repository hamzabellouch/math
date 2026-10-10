import OAI.Geometry.RCD.Heat.UniformCumulativeConstants

namespace OAI

/-! # The three actual heat estimates used by cumulative absorption -/

open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A common starting index, decrement constant and small-mass tolerance.
These estimates are proved from the heat equation and splitting data. -/
structure EventualHeatControls (Q : ℕ → E ≃L[ℝ] E)
    (N F : ℕ → E →L[ℝ] E) (J : ℕ) (ε C : ℝ) : Prop where
  step : ∀ i, J ≤ i → ∀ v,
    ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ
  decrement : ∀ i, J ≤ i → ∀ v,
    let d := ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ
    0 ≤ d ∧ ⟪v, N i v⟫_ℝ ≤ C * d ∧ d ≤ C * ⟪v, F i v⟫_ℝ
  small : ∀ i, J ≤ i → ∀ v, ⟪v, N i v⟫_ℝ ≤ ε * ⟪v, Q i v⟫_ℝ

end RegularPointCoordinates

end

end OAI
