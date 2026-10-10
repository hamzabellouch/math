import Mathlib

namespace OAI

namespace Erdos970

namespace NumberTheoryLean.Targets

open Filter
open scoped Topology

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalQuadratic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2

end NumberTheoryLean.Targets

namespace Erdos970Final

theorem erdos_970_quadratic : NumberTheoryLean.Targets.JacobsthalQuadratic := by
  sorry

end Erdos970Final

end Erdos970

end OAI
