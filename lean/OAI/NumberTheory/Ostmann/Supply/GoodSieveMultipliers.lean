import OAI.NumberTheory.Ostmann.Supply.MultiplierWeightedBudget

namespace OAI

/-! # Simultaneously squarefree, coprime and low-weight sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def goodSieveMultipliers (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => Squarefree u ∧
    ¬ (∃ p ∈ T, p ∣ u) ∧ multiplierPrimeWeight P w u ≤ B)

/-- An explicit positive proportion.  The hypotheses will be furnished by
prime reciprocal and logarithmic-imbalance estimates in the application. -/
theorem goodSieveMultipliers_card_lower (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (B : ℝ) (hB : 0 < B)
    (hT : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ p ∈ P, w p / p) ≤ B / 16) :
    (U : ℝ) / 8 ≤ (goodSieveMultipliers U T P w B).card := by
  have hsubset : positiveMultipliers U ⊆
      ((goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) ∪
        badDivisorMultipliers U T) ∪ largeWeightMultipliers U P w B := by
    intro u hu
    by_cases hs : Squarefree u
    · by_cases hd : ∃ p ∈ T, p ∣ u
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hu, hd⟩))
      · by_cases hl : multiplierPrimeWeight P w u ≤ B
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, hs, hd, hl⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, lt_of_not_ge hl⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      obtain ⟨hu0, huU⟩ := Finset.mem_Icc.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hs⟩
  have hc : U ≤ (goodSieveMultipliers U T P w B).card +
      (nonSquarefreeMultipliers U).card + (badDivisorMultipliers U T).card +
        (largeWeightMultipliers U P w B).card := by
    have hh := Finset.card_le_card hsubset
    rw [positiveMultipliers_card] at hh
    have h1 := Finset.card_union_le (goodSieveMultipliers U T P w B) (nonSquarefreeMultipliers U)
    have h2 := Finset.card_union_le
      (goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) (badDivisorMultipliers U T)
    have h3 := Finset.card_union_le
      ((goodSieveMultipliers U T P w B ∪ nonSquarefreeMultipliers U) ∪ badDivisorMultipliers U T)
      (largeWeightMultipliers U P w B)
    omega
  have hcr : (U : ℝ) ≤ (goodSieveMultipliers U T P w B).card +
      (nonSquarefreeMultipliers U).card + (badDivisorMultipliers U T).card +
        (largeWeightMultipliers U P w B).card := by exact_mod_cast hc
  have hd : ((badDivisorMultipliers U T).card : ℝ) ≤ (U : ℝ) / 16 := by
    calc
      _ ≤ (U : ℝ) * ∑ p ∈ T, (p : ℝ)⁻¹ := badDivisorMultipliers_card_le U T
      _ ≤ (U : ℝ) * (1 / 16) := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg U)
      _ = _ := by ring
  have hl : ((largeWeightMultipliers U P w B).card : ℝ) ≤ (U : ℝ) / 16 := by
    apply (mul_le_mul_iff_right₀ hB).mp
    calc
      _ ≤ (U : ℝ) * ∑ p ∈ P, w p / p := largeWeightMultipliers_card_budget U P w hw B
      _ ≤ (U : ℝ) * (B / 16) := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg U)
      _ = _ := by ring
  linarith [nonSquarefreeMultipliers_real_card_le U]

end Ostmann

end OAI
