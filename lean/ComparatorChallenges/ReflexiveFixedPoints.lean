import Mathlib

namespace OAI

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Surjectivity of the canonical map into the continuous bidual. -/
def CanonicallyReflexive : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

variable {X}

/-- Every nonexpansive selfmap of a nonempty closed bounded convex set has
an actual fixed point, with nonexpansiveness stated in the original norm. -/
theorem exists_fixedPoint_of_canonicallyReflexive
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a := by
  sorry

end ReflexiveFixedPoints

end

end OAI
