import OAI.NumberTheory.PrimeGaps.Density

namespace OAI

namespace Problem344

theorem initialCount_le_add_of_subset_above {A B : Set ℕ} {K : ℕ}
    (hAB : ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B) (N : ℕ) :
    initialCount A N ≤ initialCount B N + K := by
  classical
  have hsub : (Finset.Icc 1 N).filter (fun n => n ∈ A) ⊆
      (Finset.Icc 1 N).filter (fun n => n ∈ B) ∪ Finset.range K := by
    intro n hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
    by_cases hKn : K ≤ n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hAB n hKn hnA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (Nat.lt_of_not_ge hKn))
  calc
    initialCount A N ≤
        ((Finset.Icc 1 N).filter (fun n => n ∈ B) ∪ Finset.range K).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ B)).card + (Finset.range K).card :=
      Finset.card_union_le _ _
    _ = initialCount B N + K := by simp [initialCount]

theorem eventual_half_linear_count_of_subset_above {A B : Set ℕ} {K : ℕ} {c : ℝ}
    (hAB : ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B) (hc : 0 < c)
    (hA : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (c / 2) * (N : ℝ) ≤ (initialCount B N : ℝ) := by
  obtain ⟨NA, hNA⟩ := hA
  obtain ⟨NK, hNK⟩ := exists_nat_ge (2 * (K : ℝ) / c)
  refine ⟨max NA NK, ?_⟩
  intro N hN
  have hNA' : NA ≤ N := (le_max_left NA NK).trans hN
  have hNK' : NK ≤ N := (le_max_right NA NK).trans hN
  have hlarge : 2 * (K : ℝ) ≤ (N : ℝ) * c := by
    apply (div_le_iff₀ hc).mp
    exact hNK.trans (by exact_mod_cast hNK')
  have hcount : (initialCount A N : ℝ) ≤ (initialCount B N : ℝ) + (K : ℝ) := by
    exact_mod_cast initialCount_le_add_of_subset_above hAB N
  have hlinear := hNA N hNA'
  nlinarith

theorem positive_linear_count_of_eventual_subset {A B : Set ℕ}
    (hAB : ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B)
    (hA : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount B N : ℝ) := by
  obtain ⟨K, hK⟩ := hAB
  obtain ⟨c, hc, hA⟩ := hA
  exact ⟨c / 2, half_pos hc, eventual_half_linear_count_of_subset_above hK hc hA⟩

end Problem344

end OAI
