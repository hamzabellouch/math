import OAI.Probability.SATVariance.LinearLower
import OAI.Probability.SATVariance.ReplacementSharpness
import OAI.Probability.SATVariance.Sharpness

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

theorem variance_main (k : ℕ) (hk : 3 ≤ k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k))) := by
  exact ⟨uncapped_variance_upper k hk, capped_variance_upper k hk, variance_linear_lower k hk⟩

end RandomKSAT

end

end OAI
