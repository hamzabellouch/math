import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation

universe u

inductive AlgebraicDescent : (N : Type u) → [Group N] → Prop
  | finite (N : Type u) [Group N] [Finite N] : AlgebraicDescent N
  | cyclic (N : Type u) [Group N]
      (φ : N →* Multiplicative ℤ) (hφ : Surjective φ)
      (hf : (φ.ker : Set N).Finite) : AlgebraicDescent N
  | plane (N : Type u) [Group N]
      (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
      (lower : ∀ J : Subgroup N, J≤φ.ker → AlgebraicDescent J) : AlgebraicDescent N

end CriticalPercolation
end
end
end

end OAI
