import OAI.NumberTheory.TwoPoint.Walks.ColumnPatternRecovery
import OAI.NumberTheory.TwoPoint.Walks.ColumnBudget

namespace OAI

/-! A fixed finite universe for every column with the proved numerical budget. -/

namespace TwoPointCorrelations

open Filter

noncomputable def columnBudgetCap (N : ℕ) (L : ℝ) : ℕ :=
  min N ⌊66 * L ^ (0.92 : ℝ)⌋₊

noncomputable abbrev BudgetColumnCode (N : ℕ) (L : ℝ) :=
  BoundedColumnDecoderCode N (columnBudgetCap N L) (columnBudgetCap N L) (columnBudgetCap N L)

noncomputable def decodeBudgetColumnPattern {n N : ℕ} {L : ℝ} (hn : n ≤ N)
    (code : BudgetColumnCode N L) : Fin n → Fin n → Bool :=
  decodeColumnPrefixPattern hn code.2.2.2

/-- The cap depends only on the common scale and forest size, not on the
numerical coefficients, the prime values, or the number of regular lines. -/
theorem budget_column_code_of_counts {n N S O I : ℕ} {L : ℝ}
    (hn : n ≤ N) (hS : S ≤ N) (hO : O ≤ N) (hI : I ≤ N)
    (hcost : ((2 * S + O + I : ℕ) : ℝ) ≤ 66 * L ^ (0.92 : ℝ))
    (code : ColumnDecoderCode N S O I) :
    ∃ full : BudgetColumnCode N L,
      decodeBudgetColumnPattern hn full = decodeColumnPrefixPattern hn code := by
  have htotal : 2 * S + O + I ≤ ⌊66 * L ^ (0.92 : ℝ)⌋₊ := Nat.le_floor hcost
  have hs : S < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  have ho : O < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  have hi : I < columnBudgetCap N L + 1 := by
    unfold columnBudgetCap
    omega
  exact ⟨⟨⟨S, hs⟩, ⟨O, ho⟩, ⟨I, hi⟩, code⟩, rfl⟩

/-- All permitted counts are included simultaneously. The factor 264 is
absorbed only into the large-scale threshold; the exponential constant 64
is the same for every column and every choice of numerical coefficients. -/
theorem eventually_budget_column_code_card :
    ∀ᶠ L : ℝ in atTop, ∀ k N : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      (Fintype.card (BudgetColumnCode N L) : ℝ) ≤ Real.exp (64 * k) := by
  filter_upwards [eventually_bounded_column_code_exponential 264 (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L h hL
  intro k N hklo hkhi hN hNk
  have hc : columnBudgetCap N L ≤ N := Nat.min_le_left _ _
  have hfloor : (columnBudgetCap N L : ℝ) ≤ 66 * L ^ (0.92 : ℝ) := by
    have hf := Nat.floor_le (show 0 ≤ 66 * L ^ (0.92 : ℝ) by positivity)
    have hm : (columnBudgetCap N L : ℝ) ≤ ⌊66 * L ^ (0.92 : ℝ)⌋₊ := by
      exact_mod_cast (Nat.min_le_right N ⌊66 * L ^ (0.92 : ℝ)⌋₊)
    exact hm.trans hf
  apply h k N _ _ _ hklo hkhi hN hNk hc hc hc
  push_cast
  nlinarith

theorem card_budget_column_patterns {n N : ℕ} {L : ℝ} (hn : n ≤ N) :
    Nat.card (Set.range (@decodeBudgetColumnPattern n N L hn)) ≤
      Fintype.card (BudgetColumnCode N L) := by
  let f := @decodeBudgetColumnPattern n N L hn
  have hr := Nat.card_le_card_of_surjective
    (fun c => (⟨f c, c, rfl⟩ : Set.range f)) (by
      rintro ⟨_, c, rfl⟩
      exact ⟨c, rfl⟩)
  simpa only [Nat.card_eq_fintype_card] using hr

noncomputable abbrev BudgetColumnArrayCode (J N : ℕ) (L : ℝ) :=
  Fin J → BudgetColumnCode N L

noncomputable instance budgetColumnArrayFintype (J N : ℕ) (L : ℝ) :
    Fintype (BudgetColumnArrayCode J N L) := by
  classical
  letI : Fintype (BudgetColumnCode N L) := inferInstance
  exact Pi.instFintype

noncomputable def decodeBudgetColumnArray {n J N : ℕ} {L : ℝ} (hn : n ≤ N)
    (code : BudgetColumnArrayCode J N L) : Fin J → Fin n → Fin n → Bool :=
  fun j => decodeBudgetColumnPattern hn (code j)

theorem budget_column_array_cover {n J N : ℕ} {L : ℝ} (hn : n ≤ N)
    (pattern : Fin J → Fin n → Fin n → Bool)
    (h : ∀ j, ∃ code : BudgetColumnCode N L, decodeBudgetColumnPattern hn code = pattern j) :
    ∃ code : BudgetColumnArrayCode J N L, decodeBudgetColumnArray hn code = pattern := by
  classical
  choose code hc using h
  exact ⟨code, funext hc⟩

/-- The full column pattern array has cost exponential in `J*k`, with
one universal finite set for all numerical assignments. -/
theorem eventually_budget_column_array_card :
    ∀ᶠ L : ℝ in atTop, ∀ k J N : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      (Fintype.card (BudgetColumnArrayCode J N L) : ℝ) ≤ Real.exp (64 * k * J) := by
  filter_upwards [eventually_budget_column_code_card] with L h
  intro k J N hklo hkhi hN hNk
  let : Fintype (BudgetColumnCode N L) := inferInstance
  have hc := h k N hklo hkhi hN hNk
  calc
    _ = (Fintype.card (BudgetColumnCode N L) : ℝ) ^ J := by
      simp only [BudgetColumnArrayCode, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    _ ≤ (Real.exp (64 * k)) ^ J := pow_le_pow_left₀ (by positivity) hc J
    _ = Real.exp (64 * k * J) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end TwoPointCorrelations

end OAI
