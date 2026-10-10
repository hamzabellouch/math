import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

section Definitions

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m k : Type*} [Fintype m] [Fintype k]

def CuntzSubequiv (a : CStarMatrix m m A) (b : CStarMatrix k k A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : CStarMatrix k m A, ‖v.conjTranspose * b * v - a‖ < ε

def blockSum (a : CStarMatrix m m A) (b : CStarMatrix k k A) :
    CStarMatrix (m ⊕ k) (m ⊕ k) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0
    (CStarMatrix.ofMatrix.symm b))

def ProperlyInfinite (a : CStarMatrix m m A) : Prop :=
  CuntzSubequiv (blockSum a a) a

def diagonalCopies (n : ℕ) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a)

variable (A)

def WeaklyPurelyInfinite : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a)

def StronglyPurelyInfinite : Prop :=
  ∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ ε : ℝ, 0 < ε →
    ∃ s t : A, ‖star s * (a * a) * s - a * a‖ < ε ∧
      ‖star t * (b * b) * t - b * b‖ < ε ∧ ‖star s * a * b * t‖ < ε

end Definitions

end WeakPureInfiniteness
end

end OAI
