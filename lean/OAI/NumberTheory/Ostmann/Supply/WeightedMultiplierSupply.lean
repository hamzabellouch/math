import OAI.NumberTheory.Ostmann.Supply.MultiplierRatioProduct

namespace OAI

/-! # The weighted positive-density supply used in the sieve amplification -/

namespace Ostmann
open scoped Classical BigOperators

theorem goodSieveMultipliers_coprime (U : ℕ) (T P : Finset ℕ) (w : ℕ → ℝ)
    (B : ℝ) (hT : ∀ p ∈ T, Nat.Prime p) {u : ℕ}
    (hu : u ∈ goodSieveMultipliers U T P w B) : u.Coprime (∏ p ∈ T, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.symm
  apply (hT p hp).coprime_iff_not_dvd.mpr
  intro hd
  exact (Finset.mem_filter.mp hu).2.2.1 ⟨p, hp, hd⟩

theorem weighted_multiplier_supply (U : ℕ) (T P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (hTprime : ∀ p ∈ T, Nat.Prime p)
    (B : ℝ) (hB : 0 < B)
    (hT : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ p ∈ P, |Real.log (κ p)| / p) ≤ B / 16) :
    (U : ℝ) / 8 * Real.exp (-B) ≤
      ∑ u ∈ (positiveMultipliers U).filter
        (fun u => Squarefree u ∧ u.Coprime (∏ p ∈ T, p)), multiplierRatioProduct P κ u := by
  let G := goodSieveMultipliers U T P (fun p => |Real.log (κ p)|) B
  have hcard := goodSieveMultipliers_card_lower U T P (fun p => |Real.log (κ p)|)
    (fun _ _ => abs_nonneg _) B hB hT hP
  have hsubset : G ⊆ (positiveMultipliers U).filter
      (fun u => Squarefree u ∧ u.Coprime (∏ p ∈ T, p)) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2.1, goodSieveMultipliers_coprime U T P _ B hTprime hu⟩
  calc
    _ ≤ (G.card : ℝ) * Real.exp (-B) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = ∑ _u ∈ G, Real.exp (-B) := by simp
    _ ≤ ∑ u ∈ G, multiplierRatioProduct P κ u := by
      apply Finset.sum_le_sum
      intro u hu
      exact (goodSieveMultipliers_ratio_products U T P κ hκ B hu).1
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro u _ _
      unfold multiplierRatioProduct
      apply Finset.prod_nonneg
      intro p hp
      split_ifs
      · exact (hκ p hp).le
      · exact zero_le_one

/-- The same supply is available for the reciprocal imbalance factors. -/
theorem weighted_multiplier_supply_inv (U : ℕ) (T P : Finset ℕ) (κ : ℕ → ℝ)
    (hκ : ∀ p ∈ P, 0 < κ p) (hTprime : ∀ p ∈ T, Nat.Prime p)
    (B : ℝ) (hB : 0 < B)
    (hT : (∑ p ∈ T, (p : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ p ∈ P, |Real.log (κ p)| / p) ≤ B / 16) :
    (U : ℝ) / 8 * Real.exp (-B) ≤
      ∑ u ∈ (positiveMultipliers U).filter
        (fun u => Squarefree u ∧ u.Coprime (∏ p ∈ T, p)),
          multiplierRatioProduct P (fun p => (κ p)⁻¹) u := by
  apply weighted_multiplier_supply U T P (fun p => (κ p)⁻¹)
    (fun p hp => inv_pos.mpr (hκ p hp)) hTprime B hB hT
  simpa only [Real.log_inv, abs_neg] using hP

end Ostmann

end OAI
