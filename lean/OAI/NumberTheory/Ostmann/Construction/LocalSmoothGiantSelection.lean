import OAI.NumberTheory.Ostmann.Construction.SoftPrimeCellSelection
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport

namespace OAI

/-! # Selecting a complete giant cell inside a prescribed finite window

The averaging family may cover boundary primes several times. Its exact
partition weight is retained, so selecting a cell never clips its prime law.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def logCellFamilyWeight (C : Finset ℤ) (p : ℕ) : ℝ :=
  ∑ n ∈ C, logCellProfile (Real.log p - n)

theorem logCellFamilyWeight_nonneg (C : Finset ℤ) (p : ℕ) :
    0 ≤ logCellFamilyWeight C p :=
  Finset.sum_nonneg fun _ _ => logCellProfile_nonneg _

theorem smoothGiantPrior_real_mean (P : Finset ℕ) (G : ℝ) (f : ℕ → ℝ)
    (hpos : 0 < smoothGiantMass P logCellProfile G) :
    (∑ p : P, smoothGiantPrior P logCellProfile G p * f p) =
      (smoothGiantMass P logCellProfile G)⁻¹ *
        ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p := by
  simp only [smoothGiantPrior, smoothGiantLogNormalizer, Real.exp_neg,
    Real.exp_log hpos, div_eq_mul_inv]
  rw [Finset.mul_sum]
  have he := Finset.sum_coe_sort P (fun p : ℕ =>
    (smoothGiantMass P logCellProfile G)⁻¹ * (p : ℝ)⁻¹ *
      logCellProfile (Real.log p - G) * f p)
  convert he using 1 <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

theorem local_smoothGiantPrior_exists_positive_mean
    (P : Finset ℕ) (C : Finset ℤ) (f : ℕ → ℝ) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p) <
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p) :
    ∃ n ∈ C, 0 < smoothGiantMass P logCellProfile n ∧
      δ < ∑ p : P, smoothGiantPrior P logCellProfile n p * f p := by
  let mass := fun n : ℤ => ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n)
  let total := fun n : ℤ => ∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) * f p
  have hm : (∑ n ∈ C, mass n) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p := by
    dsimp only [mass, logCellFamilyWeight]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have ht : (∑ n ∈ C, total n) = ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p := by
    dsimp only [total, logCellFamilyWeight]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_mul]
  obtain ⟨n, hn, hlt⟩ : ∃ n ∈ C, δ * mass n < total n := by
    by_contra! h
    have hh := Finset.sum_le_sum h
    rw [← Finset.mul_sum, hm, ht] at hh
    exact (not_lt_of_ge hh) hmean
  have hnon : 0 ≤ mass n := Finset.sum_nonneg fun p _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (logCellProfile_nonneg _)
  have hpos : 0 < mass n := by
    by_contra! hz
    have he : mass n = 0 := le_antisymm hz hnon
    have hpzero : ∀ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - n) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (logCellProfile_nonneg _))).mp he
    have htzero : total n = 0 := Finset.sum_eq_zero fun p hp => by rw [hpzero p hp, zero_mul]
    rw [he, htzero, mul_zero] at hlt
    exact lt_irrefl _ hlt
  have heq : mass n = smoothGiantMass P logCellProfile n := by
    dsimp only [mass, smoothGiantMass]
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_inv, mul_comm]
  rw [heq] at hpos hlt
  refine ⟨n, hn, hpos, ?_⟩
  rw [smoothGiantPrior_real_mean P n f hpos]
  apply (mul_lt_mul_iff_of_pos_left hpos).mp
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  simpa only [mul_comm δ] using hlt

/-- Extra primes of the ambient container have zero weight in the selected
cell. Both its normalizer and its numerator therefore equal the complete
cell expressions. -/
theorem smoothGiant_full_cell_sums (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (G : ℝ) (hsub : smoothGiantPrimeRange G ⊆ P) (f : ℕ → ℝ) :
    smoothGiantMass P logCellProfile G =
      smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
    (∑ p ∈ P, (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p) =
      ∑ p ∈ smoothGiantPrimeRange G,
        (p : ℝ)⁻¹ * logCellProfile (Real.log p - G) * f p := by
  have hz (p : ℕ) (hp : p ∈ P) (hn : p ∉ smoothGiantPrimeRange G) :
      logCellProfile (Real.log p - G) = 0 := by
    by_contra h
    exact hn (smoothGiant_prime_support logCellProfile G logCellProfile_zero_outside p (hP p hp) h)
  constructor
  · unfold smoothGiantMass
    exact (Finset.sum_subset hsub fun p hp hn => by rw [hz p hp hn, zero_div]).symm
  · exact (Finset.sum_subset hsub fun p hp hn => by rw [hz p hp hn, mul_zero, zero_mul]).symm

/-- A localized positive mean produces the original full smooth harmonic
prior, with no deletion of endpoint primes. -/
theorem complete_smoothGiantPrior_exists_positive_mean
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (C : Finset ℤ)
    (hsub : ∀ n ∈ C, smoothGiantPrimeRange n ⊆ P) (f : ℕ → ℝ) (δ : ℝ)
    (hmean : δ * (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p) <
      ∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight C p * f p) :
    ∃ n ∈ C, 0 < smoothGiantMass (smoothGiantPrimeRange n) logCellProfile n ∧
      δ < ∑ p : smoothGiantPrimeRange n,
        smoothGiantPrior (smoothGiantPrimeRange n) logCellProfile n p * f p := by
  obtain ⟨n, hn, hpos, hlt⟩ := local_smoothGiantPrior_exists_positive_mean P C f δ hmean
  obtain ⟨hm, ht⟩ := smoothGiant_full_cell_sums P hP n (hsub n hn) f
  refine ⟨n, hn, by rwa [← hm], ?_⟩
  rw [smoothGiantPrior_real_mean P n f hpos, hm, ht] at hlt
  rwa [smoothGiantPrior_real_mean _ n f (by rwa [← hm])]

end Ostmann

end OAI
