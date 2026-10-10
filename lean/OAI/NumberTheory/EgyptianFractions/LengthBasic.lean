import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The least length is bounded by every witnessed length. -/
theorem egyptianLength_le_of_expansion {a b k : ℕ}
    (h : ∃ n : Fin k → ℕ, IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    egyptianLength a b ≤ k := by
  exact csInf_le' h

/-- Existence is the only input needed to obtain a least expansion. -/
theorem egyptianLength_attained_of_exists {a b : ℕ}
    (h : ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    ∃ n : Fin (egyptianLength a b) → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n := by
  exact Nat.sInf_mem h

/-- A pointwise length is bounded by the maximum over proper numerators. -/
theorem egyptianLength_le_max {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    egyptianLength a b ≤ maxEgyptianLength b := by
  unfold maxEgyptianLength
  simpa only [ite_eq_left ha] using
    (Finset.le_sup (f := fun a => if 1 ≤ a then egyptianLength a b else 0)
      (Finset.mem_range.mpr hab))

/-- Uniform bounds on actual expansions descend to the maximum least length. -/
theorem maxEgyptianLength_le_of_bound {b K : ℕ}
    (h : ∀ a : ℕ, 1 ≤ a → a < b → egyptianLength a b ≤ K) :
    maxEgyptianLength b ≤ K := by
  unfold maxEgyptianLength
  apply Finset.sup_le
  intro a ha
  split_ifs with ha'
  · exact h a ha' (Finset.mem_range.mp ha)
  · exact Nat.zero_le K

end Problem337

end

end OAI
