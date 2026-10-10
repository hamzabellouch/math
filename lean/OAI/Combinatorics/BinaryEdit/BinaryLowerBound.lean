import OAI.Combinatorics.BinaryEdit.FiniteSourceFamily
import OAI.Combinatorics.BinaryEdit.FixedLengthBinaryConversion

namespace OAI

namespace TreeEdit

open BinaryLower

/-- Introduction, `thm:binary`: actual equal-length binary witnesses for every
sufficiently large cap, from the finite-tree family and quadratic block code. -/
theorem binary_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  apply binary_lower_bound_of_finite_source_family ?_ exists_finite_source_family
  obtain ⟨M₀, hcode⟩ := fixed_length_binary_conversion.{0}
  refine ⟨M₀, ?_⟩
  intro M hM Γ inst hΓ1 hΓM
  obtain ⟨c, _, hc⟩ := hcode M hM Γ hΓ1 hΓM
  exact ⟨c, fun x y => (hc x y).1⟩

end TreeEdit

end OAI
