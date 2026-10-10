import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorHarmonicBudget

namespace OAI

/-! # Harmonic normalization for the selected bulk and complementary top slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_harmonic_normalization_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hrole : ∀ i, role (bulk i) = .word)
    (mass : CopyScheduleH role n → ℝ) (L : ℝ) (hL : 0 < L)
    (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (selectedBulkCoordinates role n m bulk hrole x).val) :
    (∏ h, (mass h)⁻¹) ≤ (L⁻¹) ^ (2 ^ n * m) *
      ∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹ := by
  rw [← Equiv.prod_comp (selectedSplitHCoordinates role n m bulk hrole), Fintype.prod_sum_type]
  change (∏ x : Fin (2 ^ n) × Fin m, (mass (selectedBulkCoordinates role n m bulk hrole x).val)⁻¹) *
      (∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹) ≤ _
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le))
  calc
    _ ≤ ∏ _x : Fin (2 ^ n) × Fin m, L⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro x _; exact (inv_pos.mpr (hmass _)).le
      · intro x _; simpa only [one_div] using one_div_le_one_div_of_le hL (hbulk x)
    _ = _ := by simp

theorem selected_anchor_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hrole : ∀ i, role (bulk i) = .word)
    (mass : CopyScheduleH role n → ℝ) (L z : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L) (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (selectedBulkCoordinates role n m bulk hrole x).val) :
    ((selectedAnchorMatchingSet role n m bulk hrole).card : ℝ) * (∏ h, (mass h)⁻¹) ≤
      (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial *
        (∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ)) := by
  let R : ℝ := ∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹
  have hR : 0 ≤ R := Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le)
  have hc : ((selectedAnchorMatchingSet role n m bulk hrole).card : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial := by
    exact_mod_cast selectedAnchorMatchingSet_card_le role n m bulk hrole
  have hp := selected_harmonic_normalization_bound role n m bulk hrole mass L hL hmass hbulk
  calc
    _ ≤ (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial) *
        ((L⁻¹) ^ (2 ^ n * m) * R) :=
      mul_le_mul hc hp (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h)).le)) (by positivity)
    _ = (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial * R *
        (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) * (L⁻¹) ^ (2 ^ n * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (anchor_harmonic_entropy (2 ^ n) m L z hL hz hm)
      (mul_nonneg (by positivity) hR)

end Ostmann

end OAI
