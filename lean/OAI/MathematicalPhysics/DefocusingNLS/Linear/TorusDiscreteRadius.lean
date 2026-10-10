import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusLinearStep

namespace OAI

/-! # Equal similarity-time steps in the actual expanding radii -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def expandingDiscreteRadius (L : Radius) (T : ℝ≥0) (n : ℕ) : Radius :=
  ⟨expandingRadius L.1 ((n : ℝ) * T),
    L.2.trans (expandingRadius_ge L.1 _ L.2 (mul_nonneg (Nat.cast_nonneg n) T.2))⟩

theorem expandingDiscreteRadius_ge (L : Radius) (T : ℝ≥0) (n : ℕ) :
    L.1 ≤ (expandingDiscreteRadius L T n).1 :=
  expandingRadius_ge L.1 _ L.2 (mul_nonneg (Nat.cast_nonneg n) T.2)

@[simp] theorem expandingDiscreteRadius_zero (L : Radius) (T : ℝ≥0) :
    expandingDiscreteRadius L T 0 = L := by
  apply Subtype.ext
  simp [expandingDiscreteRadius, expandingRadius]

theorem expandingDiscreteRadius_succ (L : Radius) (T : ℝ≥0) (n : ℕ) :
    torusEndpointRadius T (expandingDiscreteRadius L T n) =
      expandingDiscreteRadius L T (n + 1) := by
  apply Subtype.ext
  change expandingRadius (expandingRadius L.1 ((n : ℝ) * T)) T =
    expandingRadius L.1 (((n + 1 : ℕ) : ℝ) * T)
  rw [expandingRadius_add]
  congr 1
  push_cast
  ring

end DefocusingNLS

end OAI
