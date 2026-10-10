import OAI.NumberTheory.TwoPoint.Bounds.LowRankColumnEncoding
import OAI.NumberTheory.TwoPoint.Walks.ColumnCodeUniverse

namespace OAI

/-! Actual low-rank columns lie in one coefficient-independent finite universe. -/

namespace TwoPointCorrelations

open Finset Filter

theorem low_rank_column_in_budget_universe {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s r : ℕ) (hs : 0 < s)
    (L : ℝ) (hL : 1 ≤ L) (hnL : (n : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount perfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ S : Finset (EqualLabelPairs (fun i : perfect => label i.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors (fun i : perfect => label i.val)
        (fun i => formalDeparture (columnNatLabel label hn) coefficient i.val.val)) S))
    (hgeometry : ShortColumnGeometry label hn coefficient perfect s) :
    ∃ code : BudgetColumnCode (2 * n) L,
      decodeBudgetColumnPattern (show n ≤ 2 * n by omega) code =
        fun i j => decide (label i = label j) := by
  obtain ⟨O, B, S, R, hO, hB, hS, hR, hSn, hRn, code, hcode⟩ :=
    low_rank_short_column_code label hn coefficient perfect s r hs hno hgeometry
  have hO' : (O : ℝ) ≤ 2 * L ^ (1 / 50 : ℝ) := by
    have : (O : ℝ) < 2 * r := by exact_mod_cast hO
    linarith
  have hbudget := column_budget_bound L hL n s (imperfectColumnCount perfect) O B S R
    hnL hsL hI hO' (by omega) hS hR
  obtain ⟨full, hfull⟩ := budget_column_code_of_counts (by omega : n ≤ 2 * n)
    (by omega : S ≤ 2 * n) (by omega : R ≤ 2 * n)
    ((imperfectColumnCount_le perfect).trans (by omega)) hbudget code
  exact ⟨full, hfull.trans hcode⟩

/-- This universe covers all low-rank admissible columns at the given
scale, while its size has an absolute exponential bound. -/
theorem eventually_low_rank_column_universe :
    ∀ᶠ L : ℝ in atTop, ∀ k : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 0 < k →
      (Nat.card (Set.range (@decodeBudgetColumnPattern (2 * k) (4 * k) L
        (show 2 * k ≤ 4 * k by omega))) : ℝ) ≤ Real.exp (64 * k) := by
  filter_upwards [eventually_budget_column_code_card] with L h
  intro k hklo hkhi hk
  have hc := h k (4 * k) hklo hkhi (by omega) le_rfl
  have hr := card_budget_column_patterns (L := L) (show 2 * k ≤ 4 * k by omega)
  exact (show (Nat.card (Set.range (@decodeBudgetColumnPattern (2 * k) (4 * k) L
    (show 2 * k ≤ 4 * k by omega))) : ℝ) ≤ Fintype.card (BudgetColumnCode (4 * k) L)
    by exact_mod_cast hr).trans hc

end TwoPointCorrelations

end OAI
