import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.BinaryEdit.FiniteParameters

namespace OAI

namespace TreeEdit.BinaryLower

/-- Apply the numerical cap interpolation to actual finite sets of binary
words.  The hypothesis is exactly the output needed from the finite-tree
obstruction followed by the fixed-length binary code. -/
theorem binary_lower_bound_of_finite_family
    (hfamily : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ W : Finset (Word Bool (Parameters.finiteLength k)),
        2 ≤ W.card ∧ c₀ * ((k : ℝ) / 4) ^ k ≤ binarySetDistortion W) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  obtain ⟨c₀, hc₀, K, hfamily⟩ := hfamily
  obtain ⟨d₀, hd₀⟩ := Parameters.exists_finite_cap_parameters hc₀ K
  refine ⟨1 / 160, by norm_num, d₀, ?_⟩
  intro d hd
  obtain ⟨k, hkK, hk20, hkcap, hkgrowth⟩ := hd₀ d hd
  obtain ⟨W, hWcard, hWdist⟩ := hfamily k hkK
  refine ⟨Parameters.finiteLength k, ?_, hkcap, W, hWcard, ?_⟩
  · exact Parameters.finiteLength_pos (by omega : 0 < k)
  · exact hkgrowth.trans hWdist

end TreeEdit.BinaryLower

end OAI
