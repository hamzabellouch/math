import OAI.NumberTheory.Jacobsthal.Model

namespace OAI

namespace Erdos970.NumberTheoryLean.Targets

/-- The strengthened main theorem of Manuscript 293, revision ad16712e.
The interval, prime-factor and translation quantifiers are unchanged. -/
def JacobsthalIteratedLog : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2

end Erdos970.NumberTheoryLean.Targets

end OAI
