import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedProgressionRates
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellPrimeComparison

namespace OAI

/-! # The complete root-cell error retains a double-exponential saving -/

namespace Ostmann
open Filter
open scoped BigOperators
open MeasureTheory

theorem weighted_giant_atom_rate (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ u B : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      B ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      B * Real.exp (-u) ≤ Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
  filter_upwards [arithmetic_error_absorption (12 / 1000) (49 / 1000) (13 / 1000) C 1 d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hL
  intro u B hu hB
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((49 / 1000 : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hu)) (Real.exp_pos _).le
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hL

/-- The number of root cells is fixed before X grows. This estimate includes
both the weighted progression error and all retained endpoint-prime atoms. -/
theorem PublishedProgressionInput.root_cell_error_rate (P : PublishedProgressionInput)
    (C : ℝ) (d K : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ N : ℕ, N ≤ K → ∀ s V B : ℕ → ℝ,
      (∀ j < N, Real.exp ((49 / 1000 : ℝ) * L) ≤ s j) →
      (∀ j < N, V j ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      (∀ j < N, B j ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      (∑ j ∈ Finset.range N,
        (V j * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
          Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) + B j * Real.exp (-(s j)))) ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.weighted_giant_budget_rate C d, weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (2 * (K : ℝ)) 1 (13 / 1000) (125 / 10000)
      (by positivity) (by norm_num) (by norm_num) (by norm_num)] with L hP hA hK
  intro Q hQ hlog N hNK s V B hs hV hB
  calc
    _ ≤ ∑ _j ∈ Finset.range N, 2 * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN := Finset.mem_range.mp hj
      linarith [hP Q hQ hlog (s j) (V j) (hs j hjN) (hV j hjN),
        hA (s j) (B j) (hs j hjN) (hB j hjN)]
    _ = 2 * (N : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by simp; ring
    _ ≤ 2 * (K : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
      gcongr
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hK

/-- The complete smooth root-cell comparison, uniformly for every bounded
multiplier and every polynomial family within the stated numerical budget. -/
theorem PublishedProgressionInput.root_cell_prime_rate (P : PublishedProgressionInput)
    (C : ℝ) (d K k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q q a : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ), S.card + 1 ≤ K →
      (∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S) →
      ∀ (c : (S → Ordering) → ℂ) (B : ℝ), 0 ≤ B → (∀ code, ‖c code‖ ≤ B) →
      2 * B * smoothPolynomialBudget F ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ∃ (s : ℕ → ℝ) (N : ℕ) (b : ℕ → ℂ),
        Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧ (∀ j, ‖b j‖ ≤ B) ∧
        ‖complexPrimeInterval q a u v
            (fun y => c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)) -
          ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
            b j * smoothPolynomialWeight F (Real.exp y) *
              (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
            Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_cell_error_rate C d K, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro Q q a hQ hq hqQ ha hlog u v hu huv hshort F S hSK hroots c B hB hc hbudget
  have hu1 : 1 ≤ u := (Real.one_le_exp (by positivity)).trans hu
  obtain ⟨s, N, b, hs, hs0, hsN, hN, hb, herr⟩ := P.root_cell_prime_comparison
    hQ hq hqQ ha u v hu1 huv hshort F S hroots c B hB hc
  refine ⟨s, N, b, hs, hs0, hsN, hN, hb, herr.trans ?_⟩
  apply hL Q hQ hlog N (hN.trans hSK) s
    (fun j => ‖b j‖ * smoothPolynomialBudget F)
    (fun _ => 2 * B * smoothPolynomialBudget F)
  · intro j _
    exact hu.trans (by rw [← hs0]; exact hs (Nat.zero_le _))
  · intro j _
    have hbF := mul_le_mul_of_nonneg_right (hb j) (smoothPolynomialBudget_nonneg F)
    have hBF : 0 ≤ B * smoothPolynomialBudget F := mul_nonneg hB (smoothPolynomialBudget_nonneg F)
    nlinarith
  · intro j _
    exact hbudget

end Ostmann

end OAI
