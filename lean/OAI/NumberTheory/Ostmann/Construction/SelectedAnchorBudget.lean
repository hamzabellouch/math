import OAI.NumberTheory.Ostmann.Characters.AnchorNonbulkBudget
import OAI.NumberTheory.Ostmann.Construction.SelectedBulkCoordinates

namespace OAI

/-! # The selected-bulk normalization includes the top slots exactly once per path -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_selected_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (role : I → CopyScheduleRole) (m : ℕ) (bulk : Fin m ↪ I)
      (hbulk : ∀ i, role (bulk i) = .word),
      z * L / 2 ≤ (m : ℝ) →
      Fintype.card {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} ≤ B →
      ∀ mass : CopyScheduleH role n → ℝ,
      (∀ h : SelectedNonbulkH role n m bulk hbulk, Real.exp (-c * L) ≤ mass h.val) →
      (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial *
        (∏ h : SelectedNonbulkH role n m bulk hbulk, (mass h.val)⁻¹) ≤
          Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_anchor_nonbulk_cost n B c ε z hc hε hz hbudget,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro I instI role m bulk hbulk hm hB mass hmass
  have hN : Fintype.card (SelectedNonbulkH role n m bulk hbulk) ≤ 2 ^ n * B :=
    (selectedNonbulkH_card_active role n m bulk hbulk).trans (Nat.mul_le_mul_left _ hB)
  have hf : ((Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial : ℝ) ≤
      nonbulkCombinatorialCost n B := by
    have hfac : ((Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial : ℝ) ≤
        (2 ^ n * B).factorial := by exact_mod_cast Nat.factorial_le hN
    have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) from
        Nat.one_le_iff_ne_zero.mpr (by positivity))
    unfold nonbulkCombinatorialCost
    exact hfac.trans (le_mul_of_one_le_left (by positivity) hA)
  have hp : (∏ h : SelectedNonbulkH role n m bulk hbulk, (mass h.val)⁻¹) ≤
      Real.exp (c * L * (2 ^ n * B : ℕ)) := by
    calc
      _ ≤ ∏ _h : SelectedNonbulkH role n m bulk hbulk, Real.exp (c * L) := by
        apply Finset.prod_le_prod₀
        · intro h _
          exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))
        · intro h _
          have he := one_div_le_one_div_of_le (Real.exp_pos (-c * L)) (hmass h)
          simpa only [one_div, show -c * L = -(c * L) by ring, Real.exp_neg,
            inv_inv] using he
      _ = Real.exp (c * L * Fintype.card (SelectedNonbulkH role n m bulk hbulk)) := by
        simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hN)
        (mul_nonneg hc hL0))
  exact (mul_le_mul hf hp
    (Finset.prod_nonneg (fun h _ => inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))))
    (nonbulkCombinatorialCost_pos n B).le).trans (hL m hm)

end Ostmann

end OAI
