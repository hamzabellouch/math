import Mathlib

namespace OAI

/-! Literal Boolean flips and ordinary sensitivity measures.
All maxima range over the actual finite input or block-family space. -/

noncomputable section
open scoped Classical

namespace Paper320

/-- Flip exactly the coordinates belonging to the specified block. -/
def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- The ordinary number of sensitive individual input coordinates. -/
def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

/-- Maximum ordinary sensitivity over all Boolean inputs. -/
def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

/-- Maximum size of a family of disjoint nonempty sensitive blocks at an input.
The empty family is allowed and contributes zero. Invalid families contribute zero. -/
def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

/-- Maximum block sensitivity over all Boolean inputs. -/
def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

end Paper320

end

end OAI
