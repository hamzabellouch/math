import OAI.NumberTheory.Ostmann.Supply.SquarefreeMultiplierCount

namespace OAI

/-! # Elementary divisor and logarithmic budgets for sieve multipliers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def positiveMultipliers (U : ℕ) : Finset ℕ := Finset.Icc 1 U

@[simp] theorem positiveMultipliers_card (U : ℕ) : (positiveMultipliers U).card = U := by
  simp [positiveMultipliers, Nat.card_Icc]

theorem positiveMultipliers_dvd_card (U d : ℕ) :
    ((positiveMultipliers U).filter (fun u => d ∣ u)).card = U / d := by
  have he : (positiveMultipliers U).filter (fun u => d ∣ u) =
      positiveMultiplesUpTo U d := by
    ext u
    simp only [positiveMultipliers, positiveMultiplesUpTo, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_range]
    omega
  rw [he]
  exact Nat.card_multiples' U d

noncomputable def multiplierPrimeWeight (P : Finset ℕ) (w : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ u then w p else 0

theorem multiplierPrimeWeight_nonneg (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (u : ℕ) : 0 ≤ multiplierPrimeWeight P w u := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact hw p hp
  · exact le_rfl

theorem multiplierPrimeWeight_total_le (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    (∑ u ∈ positiveMultipliers U, multiplierPrimeWeight P w u) ≤
      (U : ℝ) * ∑ p ∈ P, w p / p := by
  unfold multiplierPrimeWeight
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  calc
    (∑ u ∈ positiveMultipliers U, if p ∣ u then w p else 0) =
        ∑ _u ∈ (positiveMultipliers U).filter (fun u => p ∣ u), w p := by
      rw [Finset.sum_filter]
    _ = ((U / p : ℕ) : ℝ) * w p := by simp [positiveMultipliers_dvd_card]
    _ ≤ ((U : ℝ) / p) * w p := mul_le_mul_of_nonneg_right Nat.cast_div_le (hw p hp)
    _ = (U : ℝ) * (w p / p) := by ring

noncomputable def badDivisorMultipliers (U : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => ∃ p ∈ P, p ∣ u)

theorem badDivisorMultipliers_card_le (U : ℕ) (P : Finset ℕ) :
    ((badDivisorMultipliers U P).card : ℝ) ≤ (U : ℝ) * ∑ p ∈ P, (p : ℝ)⁻¹ := by
  have hs : badDivisorMultipliers U P ⊆ P.biUnion
      (fun p => (positiveMultipliers U).filter (fun u => p ∣ u)) := by
    intro u hu
    obtain ⟨hu, p, hp, hpu⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hu, hpu⟩⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ((∑ p ∈ P, ((positiveMultipliers U).filter (fun u => p ∣ u)).card : ℕ) : ℝ) := by
      exact_mod_cast hc
    _ = ∑ p ∈ P, ((U / p : ℕ) : ℝ) := by simp [positiveMultipliers_dvd_card]
    _ ≤ ∑ p ∈ P, (U : ℝ) / p := Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum]

noncomputable def largeWeightMultipliers (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) : Finset ℕ :=
  (positiveMultipliers U).filter (fun u => B < multiplierPrimeWeight P w u)

theorem largeWeightMultipliers_card_budget (U : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (B : ℝ) :
    B * (largeWeightMultipliers U P w B).card ≤ (U : ℝ) * ∑ p ∈ P, w p / p := by
  calc
    _ = ∑ _u ∈ largeWeightMultipliers U P w B, B := by simp [mul_comm]
    _ ≤ ∑ u ∈ largeWeightMultipliers U P w B, multiplierPrimeWeight P w u := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.mem_filter.mp hu).2.le
    _ ≤ ∑ u ∈ positiveMultipliers U, multiplierPrimeWeight P w u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u _ _
      exact multiplierPrimeWeight_nonneg P w hw u
    _ ≤ _ := multiplierPrimeWeight_total_le U P w hw

end Ostmann

end OAI
