import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- An expansion containing a proper unit fraction needs at least three terms. -/
theorem marker_length_ge_three {k m : ℕ} (hm : m ∈ D k) : 3 ≤ k := by
  rcases hm with ⟨hm, n, hn, i, hi⟩
  rcases hn with ⟨hpos, hmono, hsum⟩
  by_contra hk
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact Fin.elim0 i
  · have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Fin.sum_univ_one, hi] at hsum
    have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
    have hle : (1 : ℚ) / m ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmQ
    linarith
  · rw [Fin.sum_univ_two] at hsum
    have h01 : n 0 < n 1 := hmono (by decide)
    have hp0 := hpos 0
    have hp1 := hpos 1
    have hp1Q : (0 : ℚ) < n 1 := by exact_mod_cast (by omega : 0 < n 1)
    have hn0 : 2 ≤ n 0 := by
      by_contra h
      have heq : n 0 = 1 := by omega
      rw [heq] at hsum
      norm_num at hsum
      have := div_pos (by norm_num : (0 : ℚ) < 1) hp1Q
      linarith
    have hn1 : 3 ≤ n 1 := by omega
    have hle0 : (1 : ℚ) / n 0 ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn0)
    have hle1 : (1 : ℚ) / n 1 ≤ 1 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn1)
    linarith

/-- Exact marker padding implies monotonicity even at the empty small lengths. -/
theorem D_mono_of_padding
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m) :
    Monotone D := by
  intro r k hrk m hm
  have hr : 3 ≤ r := marker_length_ge_three hm
  induction k, hrk using Nat.le_induction with
  | base => exact hm
  | succ k hrk ih =>
    rcases ih with ⟨hm2, n, hn, hmarker⟩
    obtain ⟨n', hn', hmarker'⟩ := padding k (by omega) n hn m hmarker
    exact ⟨hm2, n', hn', hmarker'⟩

/-- Finitely many markers all occur at every sufficiently large exact length. -/
theorem bounded_markers_eventually
    (hmono : Monotone D)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (B : ℕ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, 2 ≤ m → m ≤ B → m ∈ D k := by
  induction B with
  | zero =>
    exact ⟨0, by intro k hk m hm hB; omega⟩
  | succ B ih =>
    obtain ⟨K, hK⟩ := ih
    by_cases hB : 2 ≤ B + 1
    · obtain ⟨r, hr⟩ := occurs (B + 1) hB
      refine ⟨max K r, ?_⟩
      intro k hk m hm hmB
      by_cases hle : m ≤ B
      · exact hK k (le_trans (le_max_left _ _) hk) m hm hle
      · have heq : m = B + 1 := by omega
        rw [heq]
        exact hmono (le_trans (le_max_right _ _) hk) hr
    · exact ⟨K, by intro k hk m hm hmB; omega⟩

end Problem337

end

end OAI
