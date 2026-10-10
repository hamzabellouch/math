import OAI.NumberTheory.Ostmann.Characters.CharacterSelectedBulk
import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorBudget

namespace OAI

/-! # The actual character top, pivot and anchor normalizers fit the cell budget -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def selectedNonbulkCost {I : Type*} [Fintype I]
    (ρ : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, ρ (bulk i) = .word) (mass : CopyScheduleH ρ n → ℝ) : ℝ :=
  (Fintype.card (SelectedNonbulkH ρ n m bulk hbulk)).factorial *
    ∏ h : SelectedNonbulkH ρ n m bulk hbulk, (mass h.val)⁻¹

theorem eventual_selected_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (ρ : I → CopyScheduleRole) (m : ℕ) (bulk : Fin m ↪ I)
      (hbulk : ∀ i, ρ (bulk i) = .word),
      z * L / 2 ≤ (m : ℝ) →
      Nat.card {i : I // i ∉ Set.range bulk ∧ ρ i ≠ .outside} ≤ B →
      ∀ mass : CopyScheduleH ρ n → ℝ,
      (∀ h : SelectedNonbulkH ρ n m bulk hbulk, Real.exp (-c * L) ≤ mass h.val) →
      selectedNonbulkCost ρ n m bulk hbulk mass ≤
        Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_selected_anchor_nonbulk_cost n B c ε z hc hε hz hbudget] with L hL
  intro I instI ρ m bulk hbulk hm hcard mass hmass
  exact hL ρ m bulk hbulk hm (by simpa only [Nat.card_eq_fintype_card] using hcard) mass hmass

theorem eventual_character_nonbulk_cost {k : ℕ} (r : Fin k → ℕ) (f n : ℕ)
    (c ε z : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * (1 + ((∑ j, r j) + 2 * k) : ℕ) ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, z * L / 2 ≤ (m : ℝ) →
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    ∀ mass : CopyScheduleH ρ n → ℝ,
    (∀ h : SelectedNonbulkH ρ n m (characterBulk m r f) (characterBulk_role m r f),
      Real.exp (-c * L) ≤ mass h.val) →
    selectedNonbulkCost ρ n m (characterBulk m r f) (characterBulk_role m r f) mass ≤
      Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_selected_nonbulk_cost n (1 + ((∑ j, r j) + 2 * k))
    c ε z hc hε hz hbudget] with L hL
  intro m hm ρ mass hmass
  have hcard := character_original_nonbulk_card m r f
  rw [← Nat.card_eq_fintype_card] at hcard
  exact hL ρ m (characterBulk m r f) (characterBulk_role m r f) hm hcard mass hmass

end Ostmann

end OAI
