import OAI.NumberTheory.PrimeGaps.Density

namespace OAI

namespace Problem344

theorem initialCount_le (A : Set ℕ) (N : ℕ) : initialCount A N ≤ N := by
  classical
  unfold initialCount
  calc
    ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card ≤ (Finset.Icc 1 N).card :=
      Finset.card_filter_le _ _
    _ = N := by simp

theorem initialCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) :
    initialCount A N ≤ initialCount B N := by
  classical
  unfold initialCount
  apply Finset.card_le_card
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, hA⟩
  exact Finset.mem_filter.mpr ⟨hn, hAB hA⟩

theorem initialCount_div_le_one (A : Set ℕ) (N : ℕ) :
    (initialCount A N : ℝ) / (N : ℝ) ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hNpos).2
    simpa using (show (initialCount A N : ℝ) ≤ N by exact_mod_cast initialCount_le A N)

theorem density_witnesses_bddAbove (A : Set ℕ) :
    BddAbove {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      d ≤ (initialCount A N : ℝ) / (N : ℝ)} := by
  refine ⟨1, ?_⟩
  rintro d ⟨N0, h⟩
  exact (h (N0 + 1) (by omega)).trans (initialCount_div_le_one A (N0 + 1))

theorem zero_mem_density_witnesses (A : Set ℕ) :
    (0 : ℝ) ∈ {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      d ≤ (initialCount A N : ℝ) / (N : ℝ)} := by
  refine ⟨0, ?_⟩
  intro N hN
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem lowerAsymptoticDensity_nonneg (A : Set ℕ) :
    0 ≤ lowerAsymptoticDensity A := by
  exact le_csSup (density_witnesses_bddAbove A) (zero_mem_density_witnesses A)

theorem lowerAsymptoticDensity_le_one (A : Set ℕ) :
    lowerAsymptoticDensity A ≤ 1 := by
  apply csSup_le ⟨0, zero_mem_density_witnesses A⟩
  rintro d ⟨N0, h⟩
  exact (h (N0 + 1) (by omega)).trans (initialCount_div_le_one A (N0 + 1))

theorem le_lowerAsymptoticDensity_of_linear_count (A : Set ℕ) (c : ℝ)
    (hcount : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    c ≤ lowerAsymptoticDensity A := by
  apply le_csSup (density_witnesses_bddAbove A)
  rcases hcount with ⟨N0, hcount⟩
  refine ⟨max N0 1, ?_⟩
  intro N hN
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (le_div_iff₀ hNpos).2 (hcount N hN0)

theorem positive_lowerAsymptoticDensity_of_linear_count (A : Set ℕ)
    (hcount : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    0 < lowerAsymptoticDensity A := by
  rcases hcount with ⟨c, hc, hcount⟩
  exact hc.trans_le (le_lowerAsymptoticDensity_of_linear_count A c hcount)

end Problem344

end OAI
