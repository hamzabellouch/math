import Mathlib

namespace OAI

namespace EuclideanSteinitzBergstrom

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def SignedPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
        ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤
            C * Real.sqrt d

def OrderingPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
      ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤
          C * Real.sqrt d

theorem main : ∃ C : ℝ, SignedPrefixBound C ∧ OrderingPrefixBound C := by
  sorry

end EuclideanSteinitzBergstrom

end OAI
