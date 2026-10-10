import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctAdaptiveNormalized
import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctSigns

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators Polynomial

theorem distinctGenerating_error_le_of_sum_nonneg {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1)
    (hn : 0 ≤ ∑ i ∈ I, (y i : ℝ)) {k : ℕ} (hk : 2 ≤ k) :
    |(k.factorial : ℝ) * (distinctGenerating I y).coeff k -
      (∑ i ∈ I, (y i : ℝ)) ^ k| ≤
    ((k : ℝ) + 1) * (k : ℝ) ^ 2 * I.card *
      ((∑ i ∈ I, (y i : ℝ)) + k * Real.sqrt (I.card : ℝ)) ^ (k - 2) := by
  let p := (I.filter (fun i => y i = 1)).card
  let m := (I.filter (fun i => y i = -1)).card
  have hs : (∑ i ∈ I, (y i : ℝ)) = (p : ℝ) - m := sum_signs_eq_counts I y hy
  have hmp : m ≤ p := by exact_mod_cast (show (m : ℝ) ≤ p by linarith)
  have hp : p ≤ I.card := Finset.card_filter_le _ _
  have hm : m ≤ I.card := Finset.card_filter_le _ _
  have hS : p - m ≤ I.card := (Nat.sub_le p m).trans hp
  have hcast : ((p - m : ℕ) : ℝ) = ∑ i ∈ I, (y i : ℝ) := by
    rw [Nat.cast_sub hmp, hs]
  have hb := paired_series_adaptive_error_bound hS hm hk
  rw [distinctGenerating_sign_counts I y hy]
  change |(k.factorial : ℝ) * (((1 + Polynomial.X : ℝ[X]) ^ p) *
    (1 - Polynomial.X) ^ m).coeff k - _| ≤ _
  rw [sign_count_pairing p m hmp, paired_generating_coeff]
  simpa only [hcast] using hb

theorem distinctGenerating_adaptive_error_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1)
    {k : ℕ} (hk : 2 ≤ k) :
    |(k.factorial : ℝ) * (distinctGenerating I y).coeff k -
      (∑ i ∈ I, (y i : ℝ)) ^ k| ≤
    ((k : ℝ) + 1) * (k : ℝ) ^ 2 * I.card *
      (|∑ i ∈ I, (y i : ℝ)| + k * Real.sqrt (I.card : ℝ)) ^ (k - 2) := by
  by_cases hn : 0 ≤ ∑ i ∈ I, (y i : ℝ)
  · simpa only [abs_of_nonneg hn] using
      distinctGenerating_error_le_of_sum_nonneg I y hy hn hk
  · have hy' : ∀ i ∈ I, -y i = -1 ∨ -y i = 0 ∨ -y i = 1 := by
      intro i hi
      rcases hy i hi with h | h | h <;> simp [h]
    have hn' : 0 ≤ ∑ i ∈ I, ((-y i : ℤ) : ℝ) := by
      simp only [Int.cast_neg, Finset.sum_neg_distrib]
      linarith
    have hb := distinctGenerating_error_le_of_sum_nonneg I (fun i => -y i) hy' hn' hk
    rw [distinctGenerating_error_neg] at hb
    simpa only [Int.cast_neg, Finset.sum_neg_distrib, abs_of_neg (lt_of_not_ge hn)] using hb

theorem distinct_subset_moment_adaptive_error_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1)
    {k : ℕ} (hk : 2 ≤ k) :
    |(k.factorial : ℝ) * (∑ s ∈ I.powersetCard k, ∏ i ∈ s, (y i : ℝ)) -
      (∑ i ∈ I, (y i : ℝ)) ^ k| ≤
    ((k : ℝ) + 1) * (k : ℝ) ^ 2 * I.card *
      (|∑ i ∈ I, (y i : ℝ)| + k * Real.sqrt (I.card : ℝ)) ^ (k - 2) := by
  simpa only [distinctGenerating_coeff] using distinctGenerating_adaptive_error_bound I y hy hk

end Ostmann.QuadraticCenter

end OAI
