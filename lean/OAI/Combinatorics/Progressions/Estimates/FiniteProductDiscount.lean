import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Sampling.BufferedScoreDiscount

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_uniform_product_discount_cutoff {Ω : Type*} [Fintype Ω] {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ ∀ (S : Finset ℕ) (a b w : Ω → ℝ) (F : Ω → ℕ → ℝ) (score : ℝ),
      (∀ n ∈ S, N < n) → (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ b x) → (∀ x, 0 ≤ w x) →
      (∀ x n, n ∈ S → 0 ≤ F x n) →
      (∀ x n, n ∈ S → |F x n - 1| ≤ K / (n : ℝ) ^ 2) →
      score ≤ (𝔼 x, (a x - b x) * (w x * ∏ n ∈ S, F x n)) →
      score / (1 + ε / 4) ≤ 𝔼 x, (a x - (1 - ε) * b x) * w x := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_positive_product_cutoff hK
    (show 0 < ε / 4 by positivity) (show ε / 4 ≤ 1 by linarith)
  refine ⟨N, hN, ?_⟩
  intro S a b w F score hS ha hb hw hF he hscore
  have hprod (x) : |(∏ n ∈ S, F x n) - 1| ≤ ε / 4 := hcut S (F x) hS (hF x) (he x)
  apply positive_score_discount a b (fun x => w x * ∏ n ∈ S, F x n) w
    (show 0 ≤ ε / 4 by positivity) ha hb hw _ _ (quarter_discount_condition hε.le) hscore
  · intro x
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (hprod x)).1 (hw x)
    nlinarith
  · intro x
    have h := mul_le_mul_of_nonneg_left (abs_le.mp (hprod x)).2 (hw x)
    nlinarith

end Erdos3

end

end OAI
