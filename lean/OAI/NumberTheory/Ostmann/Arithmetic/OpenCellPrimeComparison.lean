import OAI.NumberTheory.Ostmann.Construction.PrimeExceptionalPoints
import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousPrimeComparison

namespace OAI

/-! # Prime comparison on open root cells, with boundary atoms retained -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem complexPrimeInterval_open_cell_bound (q a : ℕ) (u v : ℝ)
    (W w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W - complexPrimeInterval q a u v w‖ ≤
      B * Real.exp (-u) := by
  have h := complexPrimeInterval_exceptional_bound q a u v W w {⌊Real.exp v⌋₊} B hB
    (fun p hp _ _ => hbound _ (log_mem_of_mem_exp_interval hp)) (by
      intro p hp hprime _ hnot
      have hlog := log_mem_of_mem_exp_interval hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hne : Real.log p ≠ v := by
        intro he
        apply hnot
        simp only [Finset.mem_singleton]
        rw [← he, Real.exp_log hp0, Nat.floor_natCast]
      exact heq _ ⟨hlog.1, lt_of_le_of_ne hlog.2 hne⟩)
  simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using h

/-- A cell's interior uses its continuous smooth factor; the right endpoint
is accounted for by its prime atom, even when it is an arithmetic root. -/
theorem PublishedProgressionInput.open_cell_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (W w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V B : ℝ)
    (hV : ∀ s : ℕ → ℝ, Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V)
    (hB : 0 ≤ B) (hbound : ∀ y ∈ Set.Ioc u v, ‖W y - w y‖ ≤ B)
    (heq : ∀ y ∈ Set.Ioo u v, W y = w y) :
    ‖complexPrimeInterval q a u v W -
      ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) + B * Real.exp (-u) := by
  have h1 := complexPrimeInterval_open_cell_bound q a u v W w B hB hbound heq
  have h2 := P.continuous_prime_comparison hQ hq hqQ ha u v hu huv hshort w hwc V hV
  exact (norm_sub_le_norm_sub_add_norm_sub _ (complexPrimeInterval q a u v w) _).trans
    (by linarith)

/-- Sum the actual prime weights over the constructed root partition. The
ideal term is the sum of its continuous cell integrals with the Page factor. -/
theorem PublishedProgressionInput.piecewise_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ) (hs0 : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    (W : ℝ → ℂ) (w : ℕ → ℝ → ℂ) (V B : ℕ → ℝ)
    (hwc : ∀ j < N, ContinuousOn (w j) (Set.Icc (s j) (s (j + 1))))
    (hV : ∀ j < N, ∀ r : ℕ → ℝ, Monotone r → ∀ M,
      r 0 = s j → r M = s (j + 1) → discreteVariation (fun k => w j (r k)) M ≤ V j)
    (hB : ∀ j < N, 0 ≤ B j)
    (hbound : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖W y - w j y‖ ≤ B j)
    (heq : ∀ j < N, ∀ y ∈ Set.Ioo (s j) (s (j + 1)), W y = w j y) :
    ‖complexPrimeInterval q a (s 0) (s N) W -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        w j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N, (V j *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + B j * Real.exp (-(s j))) := by
  rw [← complexPrimeInterval_partition q a s hs W N, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  apply P.open_cell_prime_comparison hQ hq hqQ ha _ _
    (hs0.trans (hs (Nat.zero_le _))) (hs (Nat.le_succ _))
  · have h1 := hs (by omega : j + 1 ≤ N)
    have h0 := hs (Nat.zero_le j)
    linarith
  · exact hwc j hjN
  · exact hV j hjN
  · exact hB j hjN
  · exact hbound j hjN
  · exact heq j hjN

end Ostmann

end OAI
