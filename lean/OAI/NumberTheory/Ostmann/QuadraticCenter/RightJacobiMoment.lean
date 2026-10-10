import OAI.NumberTheory.Ostmann.QuadraticCenter.ComplexMomentEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentCorrelation

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem actual_jacobi_complex_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (b : Finset P → ℂ) (B N : ℕ)
    (hb : ∀ s, B < primeSubsetProduct s → b s = 0)
    {l : ℕ} (hl : 1 ≤ l) :
    (∑ m ∈ (Finset.range N).filter Odd,
      ‖∑ s, b s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖ ^ (2 * l)) ≤
      (2 : ℝ) ^ l *
        ((N : ℝ) * (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * ‖b s‖ ^ 2) ^ l +
          (4 * (B : ℝ) ^ (2 * l)) * (∑ s, ‖b s‖) ^ (2 * l)) := by
  classical
  have ht := complex_character_moment_le_energy
    ((Finset.range N).filter Odd) (cutoffPrimeJacobi B) b hl
    (N : ℝ) (4 * (B : ℝ) ^ (2 * l)) (by positivity) (by positivity)
    (cutoffPrimeJacobi_correlation hP B N (2 * l))
  have heq (m : ℕ) (s : Finset P) :
      b s * (cutoffPrimeJacobi B m s : ℂ) =
        b s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ) := by
    by_cases hs : primeSubsetProduct s ≤ B
    · simp [cutoffPrimeJacobi, hs]
    · simp [cutoffPrimeJacobi, hs, hb s (lt_of_not_ge hs)]
  simpa only [heq] using ht

end Ostmann.QuadraticCenter

end OAI
