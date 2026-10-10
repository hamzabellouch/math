import Mathlib

namespace OAI

noncomputable section

namespace KKUltraTrace

open Filter Topology

noncomputable section

theorem ultrafilter_diagonal_indices (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (S : ℕ → Set ℕ) (hS : ∀ n, S n ∈ (ω : Filter ℕ)) :
    ∃ k : ℕ → ℕ, Tendsto k (ω : Filter ℕ) atTop ∧
      ∀ᶠ j in (ω : Filter ℕ), j ∈ S (k j) := by
  classical
  let P (j n : ℕ) := ∀ m ≤ n, j ∈ S m
  let k (j : ℕ) := Nat.findGreatest (P j) j
  have hP (n : ℕ) : ∀ᶠ j in (ω : Filter ℕ), P j n := by
    induction n with
    | zero => simpa [P] using hS 0
    | succ n ih =>
      filter_upwards [ih, hS (n+1)] with j hj hn
      intro m hm
      rcases Nat.le_or_eq_of_le_add_one hm with h | rfl
      · exact hj m h
      · exact hn
  refine ⟨k, tendsto_atTop.2 ?_, ?_⟩
  · intro n
    filter_upwards [hP n, hω (eventually_ge_atTop n)] with j hj hjn
    exact Nat.le_findGreatest hjn hj
  · filter_upwards [hP 0] with j hj
    have hg : P j (k j) := Nat.findGreatest_spec (Nat.zero_le j) hj
    exact hg (k j) le_rfl

end

end KKUltraTrace
end

end OAI
