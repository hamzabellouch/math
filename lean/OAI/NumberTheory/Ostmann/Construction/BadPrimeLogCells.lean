import OAI.NumberTheory.Ostmann.Arithmetic.PrimeWordCellGeometry
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCellChoice

namespace OAI

/-! # A logarithmic imbalance budget excludes only linearly many cells -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem finiteCellMass_sum_le (P I : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    (∑ h ∈ I, finiteCellMass P label μ h) ≤ ∑ p ∈ P, μ p := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show I ⊆ I ∪ P.image label from Finset.subset_union_left)
    (fun h _ _ => finiteCellMass_nonneg P label μ hμ h)
  exact h.trans_eq (finiteCellMass_sum P (I ∪ P.image label) label μ
    (fun p hp => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))

/-- `badPrimes` is the set removed by the balance or test-error threshold. -/
noncomputable def badPrimeLogCells (I badPrimes : Finset ℕ) : Finset ℕ :=
  I.filter (fun h => 1 ≤ h ∧ 1 / (8 * ((h : ℝ) + 1)) ≤
    finiteCellMass badPrimes primeLogIndex (fun p => (p : ℝ)⁻¹) h)

theorem badPrimeLogCells_card (I badPrimes : Finset ℕ)
    (hprime : ∀ p ∈ badPrimes, p.Prime) :
    (badPrimeLogCells I badPrimes).card / (16 : ℝ) ≤
      ∑ p ∈ badPrimes, Real.log (p : ℝ) / p := by
  have hcell (h : ℕ) (hh : h ∈ badPrimeLogCells I badPrimes) :
      (1 / 16 : ℝ) ≤ finiteCellMass badPrimes primeLogIndex
        (fun p => Real.log (p : ℝ) / p) h := by
    obtain ⟨_, hh1, hmass⟩ := Finset.mem_filter.mp hh
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have hmul := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg h (α := ℝ))
    have hlog : (h : ℝ) * finiteCellMass badPrimes primeLogIndex
        (fun p => (p : ℝ)⁻¹) h ≤
        finiteCellMass badPrimes primeLogIndex (fun p => Real.log (p : ℝ) / p) h := by
      unfold finiteCellMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpB, hph⟩ := Finset.mem_filter.mp hp
      have hbound := (primeLogIndex_bounds p (hprime p hpB)).1
      rw [hph] at hbound
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hbound.le
        (inv_nonneg.mpr (Nat.cast_nonneg p))
    have hn : (1 / 16 : ℝ) ≤ (h : ℝ) * (1 / (8 * ((h : ℝ) + 1))) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < 8 * ((h : ℝ) + 1))).mpr
      linarith
    exact hn.trans (hmul.trans hlog)
  have hs := Finset.sum_le_sum hcell
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hsum := finiteCellMass_sum_le badPrimes (badPrimeLogCells I badPrimes)
    primeLogIndex (fun p => Real.log (p : ℝ) / p) (fun p hp => by
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
        (Nat.cast_nonneg p))
  calc
    _ = (badPrimeLogCells I badPrimes).card * (1 / 16 : ℝ) := by ring
    _ ≤ _ := hs.trans hsum

theorem badPrimeLogCells_card_budget (I badPrimes : Finset ℕ) (C L : ℝ)
    (hprime : ∀ p ∈ badPrimes, p.Prime)
    (hbudget : (∑ p ∈ badPrimes, Real.log (p : ℝ) / p) ≤ C * L) :
    ((badPrimeLogCells I badPrimes).card : ℝ) ≤ 16 * C * L := by
  have h := (badPrimeLogCells_card I badPrimes hprime).trans hbudget
  linarith

end Ostmann

end OAI
