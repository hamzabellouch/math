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

/-- Nonexpansiveness is measured in the original ambient norm. -/
def NonexpansiveOn (C : Set X) (F : C → C) : Prop :=
  ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖

/-- Every nonexpansive selfmap of every nonempty closed bounded convex set
has a fixed point, in the norm already carried by `X`. -/
def HasNonexpansiveFixedPointProperty (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (C : Set X), C.Nonempty → IsClosed C → Bornology.IsBounded C →
    Convex ℝ C → ∀ F : C → C, NonexpansiveOn C F → ∃ a : C, F a = a

end ReflexiveFixedPoints

end

end OAI
