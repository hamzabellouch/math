import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousIntegerComparison

namespace OAI

/-! # Open integer cells retain their endpoint atoms -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem complexIntegerInterval_open_cell_bound (q a : ℕ) (u v G : ℝ)
    (W w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexIntegerInterval q a u v G W - complexIntegerInterval q a u v G w‖ ≤
      B * Real.exp (-G) := by
  let T := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  let S : Finset ℕ := {⌊Real.exp v⌋₊}
  have hC : 0 ≤ B * Real.exp (-G) := mul_nonneg hB (Real.exp_pos _).le
  have hatom (n : ℕ) : ‖(integerResidueAtom q a G n : ℂ)‖ ≤ Real.exp (-G) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integerResidueAtom_nonneg q a G n)]
    unfold integerResidueAtom
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hpoint (n : ℕ) (hn : n ∈ T) :
      ‖(W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ)‖ ≤
        if n ∈ S then B * Real.exp (-G) else 0 := by
    by_cases hS : n ∈ S
    · rw [ite_eq_left hS, norm_mul]
      exact mul_le_mul (hbound _ (log_mem_of_mem_exp_interval hn)) (hatom n) (norm_nonneg _) hB
    · rw [ite_eq_right hS]
      have hlog := log_mem_of_mem_exp_interval hn
      have hn0 : (0 : ℝ) < n := by
        have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
        exact_mod_cast this
      have hne : Real.log n ≠ v := by
        intro hv
        apply hS
        simp only [S, Finset.mem_singleton]
        rw [← hv, Real.exp_log hn0, Nat.floor_natCast]
      rw [heq _ ⟨hlog.1, lt_of_le_of_ne hlog.2 hne⟩, sub_self, zero_mul, norm_zero]
  have he : complexIntegerInterval q a u v G W - complexIntegerInterval q a u v G w =
      ∑ n ∈ T, (W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ) := by
    simp only [complexIntegerInterval, ← Finset.sum_sub_distrib, T, sub_mul]
  rw [he]
  calc
    _ ≤ ∑ n ∈ T, ‖(W (Real.log n) - w (Real.log n)) * (integerResidueAtom q a G n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ T, if n ∈ S then B * Real.exp (-G) else 0 := Finset.sum_le_sum hpoint
    _ = ((T.filter (· ∈ S)).card : ℝ) * (B * Real.exp (-G)) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (S.card : ℝ) * (B * Real.exp (-G)) := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (show T.filter (· ∈ S) ⊆ S from
        fun _ h => (Finset.mem_filter.mp h).2)
    _ = _ := by simp [S]

theorem open_cell_integer_comparison (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (W w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V B : ℝ)
    (hV : ∀ s : ℕ → ℝ, Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V)
    (hB : 0 ≤ B) (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexIntegerInterval q a u v G W -
      ∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)‖ ≤
        V * (2 * Real.exp (-G)) + B * Real.exp (-G) := by
  have h1 := complexIntegerInterval_open_cell_bound q a u v G W w B hB hbound heq
  have h2 := continuous_integer_comparison q a hq u v G huv w hwc V hV
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexIntegerInterval q a u v G w) _).trans
    (by linarith)

theorem piecewise_integer_comparison (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (W : ℝ → ℂ) (w : ℕ → ℝ → ℂ) (V B : ℕ → ℝ)
    (hwc : ∀ j < N, ContinuousOn (w j) (Set.Icc (s j) (s (j + 1))))
    (hV : ∀ j < N, ∀ r : ℕ → ℝ, Monotone r → ∀ M,
      r 0 = s j → r M = s (j + 1) → discreteVariation (fun k => w j (r k)) M ≤ V j)
    (hB : ∀ j < N, 0 ≤ B j)
    (hbound : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖W y - w j y‖ ≤ B j)
    (heq : ∀ j < N, ∀ y ∈ Set.Ioo (s j) (s (j + 1)), W y = w j y) :
    ‖complexIntegerInterval q a (s 0) (s N) G W -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        w j y * (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N, (V j * (2 * Real.exp (-G)) + B j * Real.exp (-G)) := by
  rw [← complexIntegerInterval_partition q a G s hs W N, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  exact open_cell_integer_comparison q a hq _ _ G (hs (Nat.le_succ _))
    W (w j) (hwc j hjN) (V j) (B j) (hV j hjN) (hB j hjN) (hbound j hjN) (heq j hjN)

end Ostmann

end OAI
