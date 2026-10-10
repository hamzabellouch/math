import Mathlib.Data.Int.Interval
import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # The actual logarithmic cutoff weights in the initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every nonzero translate on this bounded range is retained, including
both boundary centers. -/
theorem logCellProfile_sum_centers (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hN : x ≤ N) :
    (∑ c ∈ Finset.Icc (0 : ℤ) N, logCellProfile (x - c)) = 1 := by
  have h := logCellProfile_partition_unity x
  rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) N) (fun c hc => ?_)] at h
  · exact h
  · apply logCellProfile_zero_outside
    have hc' : c < 0 ∨ (N : ℤ) < c := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hc
    rcases hc' with hc' | hc'
    · have hi : c ≤ -1 := by omega
      have hr : (c : ℝ) ≤ -1 := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ x - c by linarith).trans (le_abs_self _)
    · have hi : (N : ℤ) + 1 ≤ c := by omega
      have hr : (N : ℝ) + 1 ≤ c := by exact_mod_cast hi
      exact (show (1 : ℝ) ≤ -(x - c) by linarith).trans (neg_le_abs _)

/-- Pigeonholing selects a weight, without changing the underlying law. -/
theorem exists_weighted_log_sum_center {A : Type*} [Fintype A]
    (weight score : A → ℝ) (N : ℕ) (β : ℝ)
    (hmass : β ≤ ∑ a, weight a)
    (hscore : ∀ a, 0 ≤ score a ∧ score a ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      β / (N + 1) ≤ ∑ a, weight a * logCellProfile (score a - c) := by
  have hcard : ((Finset.Icc (0 : ℤ) N).card : ℝ) = N + 1 := by
    simp
  have hsum : (∑ c ∈ Finset.Icc (0 : ℤ) N,
      ∑ a, weight a * logCellProfile (score a - c)) = ∑ a, weight a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum, logCellProfile_sum_centers N (score a)
      (hscore a).1 (hscore a).2, mul_one]
  apply Finset.exists_le_of_sum_le (s := Finset.Icc (0 : ℤ) N)
    (Finset.nonempty_Icc.mpr (by omega))
  rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_div_cancel₀ _ (by positivity), hsum]
  exact hmass

noncomputable def balancedTupleSet {A : Type*} [Fintype A] (n : ℕ)
    (good : Fin n → A → Prop) : Finset (Fin n → A) :=
  Finset.univ.filter (fun x => ∀ i, good i (x i))

theorem balancedTupleSet_mass {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0) :
    δ ^ n ≤ ∑ x ∈ balancedTupleSet n good, productPrior μ x := by
  have he (x : Fin n → A) :
      (∏ i, if good i (x i) then μ i (x i) else 0) =
        if ∀ i, good i (x i) then productPrior μ x else 0 := by
    by_cases h : ∀ i, good i (x i)
    · simp [h, productPrior]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have hs : (∑ x ∈ balancedTupleSet n good, productPrior μ x) =
      ∏ i, ∑ a, if good i a then μ i a else 0 := by
    simp only [balancedTupleSet, Finset.sum_filter]
    simp_rw [← he]
    exact (Fintype.prod_sum (fun i a => if good i a then μ i a else 0)).symm
  rw [hs]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin n)))
      (fun _ _ => hδ) (fun i _ => hmass i))

/-- The lower bound used for each broad-band group in Section 7.2. -/
theorem exists_balanced_log_sum_center {A : Type*} [Fintype A] (n : ℕ)
    (μ : Fin n → A → ℝ) (good : Fin n → A → Prop) (score : (Fin n → A) → ℝ)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      δ ^ n / (N + 1) ≤ ∑ x ∈ balancedTupleSet n good,
        productPrior μ x * logCellProfile (score x - c) := by
  have hs := balancedTupleSet_mass n μ good δ hδ hmass
  have hm : δ ^ n ≤ ∑ x, if ∀ i, good i (x i) then productPrior μ x else 0 := by
    simpa only [balancedTupleSet, Finset.sum_filter] using hs
  obtain ⟨c, hc, h⟩ := exists_weighted_log_sum_center
    (fun x => if ∀ i, good i (x i) then productPrior μ x else 0) score N (δ ^ n) hm hscore
  refine ⟨c, hc, ?_⟩
  simpa only [balancedTupleSet, Finset.sum_filter, ite_mul, zero_mul] using h

end Ostmann

end OAI
