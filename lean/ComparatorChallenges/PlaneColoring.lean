import Mathlib

namespace OAI

noncomputable section

namespace Problem160

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y

theorem properColoring_seven : ProperColoring 7 := by sorry

end Problem160

end

end OAI
