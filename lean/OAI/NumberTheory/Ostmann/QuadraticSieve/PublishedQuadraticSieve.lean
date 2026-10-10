import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # The published quadratic large-sieve input

D. R. Heath-Brown, *A mean value estimate for real character sums*,
Acta Arithmetica 72 (1995), 235–275, Theorem 1,
DOI 10.4064/aa-72-3-235-275.

Only the finite odd-squarefree coefficient inequality is retained. The
symbol is Mathlib's Jacobi symbol.
-/

namespace Ostmann

open scoped BigOperators Classical

def oddSquarefreeRange (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => Odd n ∧ Squarefree n

noncomputable def quadraticSieveSum (N : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ oddSquarefreeRange N, b n * (jacobiSym (n : ℤ) m : ℂ)

noncomputable def quadraticSieveEnergy (N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N, ‖b n‖ ^ 2

/-- Heath-Brown's Theorem 1, specialized to integer bounds and finite
coefficient arrays. This is an explicit hypothesis, not a global axiom. -/
def PublishedQuadraticLargeSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ b : ℕ → ℂ,
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b m‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b

end Ostmann

end OAI
