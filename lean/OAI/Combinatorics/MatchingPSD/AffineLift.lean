import Mathlib
import OAI.Combinatorics.MatchingPSD.AffineFactorization
import OAI.Combinatorics.MatchingPSD.Main

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

theorem affine_lift_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ r : ℕ,
        HasAffineLift n r → (n : ℝ) ^ C < (r : ℝ) := by
  intro C hC
  obtain ⟨n₀, hn₀, hmain⟩ := main C hC
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn he r h
  have hn4 : 4 ≤ n := hn₀.trans hn
  have hf := affineLift_hasFactorization hn4 he h
  have hr := factorization_order_pos (by omega) he hf
  exact (hmain n hn he).trans_le (by exact_mod_cast psdRank_le hr hf)

end PerfectMatchingPSD

end OAI
