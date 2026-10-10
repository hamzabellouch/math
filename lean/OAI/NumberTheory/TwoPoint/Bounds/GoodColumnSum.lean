import OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
import OAI.NumberTheory.TwoPoint.Walks.ColumnCodeUniverse
import OAI.NumberTheory.TwoPoint.Bounds.OccurrenceCounts

namespace OAI

/-! Sum the good column patterns with one reciprocal per observed prime. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- Unused elements of the ambient label type make no contribution. -/
lemma twice_observed_labels_le_slots_add_singletons
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] (label : τ → ι) :
    2 * (univ.image label).card ≤ Fintype.card τ + (singletonLabels label).card := by
  have hlocal (i : ι) :
      2 * (if 0 < (labelOccurrences label i).card then 1 else 0) ≤
        (labelOccurrences label i).card +
          (if (labelOccurrences label i).card = 1 then 1 else 0) := by
    split_ifs <;> omega
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hlocal i)
  rw [← mul_sum, sum_add_distrib, total_label_occurrences] at hs
  have hused : (∑ i : ι, if 0 < (labelOccurrences label i).card then (1 : ℕ) else 0) =
      (univ.image label).card := by
    have hi (i : ι) : 0 < (labelOccurrences label i).card ↔ i ∈ univ.image label := by
      rw [card_pos]
      simp [labelOccurrences, filter_nonempty_iff, mem_image]
    simp only [hi]
    simp
  have hsingle : (∑ i : ι, if (labelOccurrences label i).card = 1 then (1 : ℕ) else 0) =
      (singletonLabels label).card := by simp [singletonLabels, sum_boole]
  rwa [hused, hsingle] at hs

def columnSingletonCount {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : ℕ :=
  ∑ j, (singletonLabels (w j)).card

lemma column_observed_count {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    2 * (∑ j, (univ.image (w j)).card) ≤ J * R + columnSingletonCount w := by
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin J))) =>
    twice_observed_labels_le_slots_add_singletons (w j))
  simpa only [← mul_sum, sum_add_distrib, Fintype.card_fin, sum_const,
    card_univ, smul_eq_mul, columnSingletonCount] using hs

/-- At most `2*S` singleton labels leave at most `J*k+S` distinct primes
in a word with `2*k` occurrences per column. -/
lemma good_column_observed_count {J k S : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J (2 * k) P) (hs : columnSingletonCount w ≤ 2 * S) :
    (∑ j, (univ.image (w j)).card) ≤ J * k + S := by
  have h := column_observed_count w
  nlinarith

theorem covered_good_column_sum {J k S : ℕ} {Code : Type*} [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J (2 * k) P))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (A : ℝ) (hA : 1 ≤ A) (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ w ∈ F, columnSingletonCount w ≤ 2 * S)
    (hcover : ∀ w ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (w j i = w j l)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤ (Fintype.card Code : ℝ) * A ^ (J * k + S) :=
  covered_column_patterns_reciprocal_sum P F decode A (J * k + S) hA hmass
    (fun w hw => good_column_observed_count w (hsingle w hw)) hcover

/-- The universal forest decoder and the separate column masses give the
required good-word prime sum. The exponential constant is absolute. -/
theorem eventually_good_column_sum :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ, ∀ P : Fin J → Finset ℕ,
      ∀ F : Finset (ColumnPrimeAssignment J (2 * k) P), ∀ W : ℝ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ k → 1 ≤ W →
      (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ w ∈ F, columnSingletonCount w ≤ 2 * S) →
      (∀ w ∈ F, ∃ c : BudgetColumnArrayCode J (4 * k) L,
        ∀ j i l, decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega) c j i l =
          decide (w j i = w j l)) →
      (∑ w ∈ F, columnReciprocalWeight w) ≤
        Real.exp (64 * k * J) * (2 * W) ^ (J * k + S) := by
  filter_upwards [eventually_budget_column_array_card] with L h
  intro J k S P F W hklo hkhi hk hW hmass hsingle hcover
  apply (covered_good_column_sum P F
    (decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega)) (2 * W)
    (by linarith) hmass hsingle hcover).trans
  apply mul_le_mul_of_nonneg_right
  · exact h k J (4 * k) hklo hkhi (by omega) le_rfl
  · positivity

end TwoPointCorrelations

end OAI
