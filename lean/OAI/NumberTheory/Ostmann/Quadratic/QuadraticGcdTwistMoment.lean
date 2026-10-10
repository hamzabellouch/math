import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdRangeBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTwist

namespace OAI

/-! # Every actual signed gcd coefficient keeps the original moment budget -/

namespace Ostmann

theorem quadratic_gcd_twist_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R D : ℕ, Squarefree D → Odd D →
      ∀ u : ℤ, ∀ v : ℕ → ℂ,
        quadraticDivisorMoment (2 * quadraticGcdBlockSize R D)
          (quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)) ≤
            C * (2 * (R : ℝ)) ^ ε * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_gcd_block_divisor_moment ε hε
  refine ⟨C, hC, ?_⟩
  intro R D hD ho u v
  exact (quadraticFrequencyTwist_moment u 1 _ _).trans (hc R D hD ho v)

theorem quadratic_gcd_twist_lower {R D : ℕ} (hD : 0 < D)
    (u : ℤ) (v : ℕ → ℂ) (hv : ∀ n < R, v n = 0) {n : ℕ}
    (hn : n < quadraticGcdBlockSize R D) :
    quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v) n = 0 :=
  quadraticFrequencyTwist_zero u 1 _ (quadratic_gcd_block_lower hD v hv hn)

end Ostmann

end OAI
