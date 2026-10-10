import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile

namespace OAI

/-! # Selecting a smooth prime cell from a positive empirical mean -/

namespace Ostmann
open scoped Classical BigOperators

/-- The integer translates that can occur in a finite prime set. -/
noncomputable def smoothPrimeCenters (P : Finset ℕ) : Finset ℤ :=
  P.biUnion (fun p => {⌊Real.log (p : ℝ)⌋, ⌊Real.log (p : ℝ)⌋ + 1})

theorem logCellProfile_zero_off_centers (x : ℝ) (n : ℤ)
    (hn : n ∉ ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ)) : logCellProfile (x - n) = 0 := by
  have hne : n ≠ ⌊x⌋ ∧ n ≠ ⌊x⌋ + 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  apply logCellProfile_zero_outside
  by_cases hle : n ≤ ⌊x⌋
  · have hi : n + 1 ≤ ⌊x⌋ := by omega
    have hr : (n : ℝ) + 1 ≤ (⌊x⌋ : ℤ) := by exact_mod_cast hi
    exact (show (1 : ℝ) ≤ x - n by linarith [Int.floor_le x]).trans (le_abs_self _)
  · have hi : ⌊x⌋ + 2 ≤ n := by omega
    have hr : ((⌊x⌋ : ℤ) : ℝ) + 2 ≤ n := by exact_mod_cast hi
    exact (show (1 : ℝ) ≤ -(x - n) by linarith [Int.lt_floor_add_one x]).trans (neg_le_abs _)

theorem smoothPrimeCenters_partition (P : Finset ℕ) (p : ℕ) (hp : p ∈ P) :
    (∑ n ∈ smoothPrimeCenters P, logCellProfile (Real.log p - n)) = 1 := by
  rw [← logCellProfile_partition_unity (Real.log p)]
  symm
  apply tsum_eq_sum
  intro n hn
  apply logCellProfile_zero_off_centers
  intro hm
  exact hn (Finset.mem_biUnion.mpr ⟨p, hp, hm⟩)

/-- A positive weighted mean selects a positive-mass smooth cell. The test may
be unbounded and may change sign; no hard-cell or positivity approximation is
used in passing to the original soft prior. -/
theorem smoothPrimeCell_exists (P : Finset ℕ) (ν f : ℕ → ℝ)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, ν p) < ∑ p ∈ P, ν p * f p) :
    ∃ n ∈ smoothPrimeCenters P,
      0 < ∑ p ∈ P, ν p * logCellProfile (Real.log p - n) ∧
      δ * (∑ p ∈ P, ν p * logCellProfile (Real.log p - n)) <
        ∑ p ∈ P, ν p * logCellProfile (Real.log p - n) * f p := by
  let mass := fun n : ℤ => ∑ p ∈ P, ν p * logCellProfile (Real.log p - n)
  let total := fun n : ℤ => ∑ p ∈ P, ν p * logCellProfile (Real.log p - n) * f p
  have hmass : (∑ n ∈ smoothPrimeCenters P, mass n) = ∑ p ∈ P, ν p := by
    unfold mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.mul_sum, smoothPrimeCenters_partition P p hp, mul_one]
  have htotal : (∑ n ∈ smoothPrimeCenters P, total n) = ∑ p ∈ P, ν p * f p := by
    unfold total
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    simp_rw [mul_right_comm (ν p) _ (f p)]
    rw [← Finset.mul_sum, smoothPrimeCenters_partition P p hp, mul_one]
  have hex : ∃ n ∈ smoothPrimeCenters P, δ * mass n < total n := by
    by_contra! h
    have hh := Finset.sum_le_sum h
    rw [← Finset.mul_sum, hmass, htotal] at hh
    linarith
  obtain ⟨n, hn, hlt⟩ := hex
  refine ⟨n, hn, ?_, hlt⟩
  have hnon : 0 ≤ mass n := Finset.sum_nonneg fun p hp =>
    mul_nonneg (hν p hp) (logCellProfile_nonneg _)
  by_contra! hz
  have he : mass n = 0 := le_antisymm hz hnon
  have hpzero : ∀ p ∈ P, ν p * logCellProfile (Real.log p - n) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun p hp =>
      mul_nonneg (hν p hp) (logCellProfile_nonneg _))).mp he
  have htzero : total n = 0 := Finset.sum_eq_zero fun p hp => by rw [hpzero p hp, zero_mul]
  rw [he, htzero, mul_zero] at hlt
  exact lt_irrefl _ hlt

/-- The selected cell uses exactly the manuscript's harmonic smooth prior,
including all primes in the ambient support. -/
theorem smoothGiantPrior_exists_positive_mean (P : Finset ℕ) (f : ℕ → ℝ) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, (p : ℝ)⁻¹) < ∑ p ∈ P, (p : ℝ)⁻¹ * f p) :
    ∃ n ∈ smoothPrimeCenters P,
      0 < smoothGiantMass P logCellProfile n ∧
      δ < ∑ p : P, smoothGiantPrior P logCellProfile n p * f p := by
  obtain ⟨n, hn, hmass, htotal⟩ := smoothPrimeCell_exists P (fun p => (p : ℝ)⁻¹) f
    (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg _)) δ hmean
  have hm : (∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n)) =
      smoothGiantMass P logCellProfile n := by
    unfold smoothGiantMass
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv, mul_comm]
  rw [hm] at hmass htotal
  refine ⟨n, hn, hmass, ?_⟩
  have hs : (∑ p : P, smoothGiantPrior P logCellProfile n p * f p) =
      (smoothGiantMass P logCellProfile n)⁻¹ *
        ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) * f p := by
    simp only [smoothGiantPrior, smoothGiantLogNormalizer, Real.exp_neg,
      Real.exp_log hmass, div_eq_mul_inv]
    rw [Finset.mul_sum]
    have he := Finset.sum_coe_sort P (fun p : ℕ =>
      (smoothGiantMass P logCellProfile n)⁻¹ * (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) * f p)
    convert he using 1 <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring
  rw [hs]
  apply (mul_lt_mul_iff_of_pos_left hmass).mp
  rw [← mul_assoc, mul_inv_cancel₀ hmass.ne', one_mul]
  simpa only [mul_comm δ] using htotal

end Ostmann

end OAI
