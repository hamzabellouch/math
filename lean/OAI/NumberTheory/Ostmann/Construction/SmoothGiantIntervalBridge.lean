import OAI.NumberTheory.Ostmann.Construction.PrimeExternalPartition
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport

namespace OAI

/-! # The normalized giant prior and its complete logarithmic cell -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiant_nonzero_in_log_cell (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hφ : φ (Real.log p - G) ≠ 0) :
    p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊ := by
  have hh : |Real.log p - G| < 1 := by
    by_contra h
    exact hφ (hout _ (le_of_not_gt h))
  have hh' := abs_lt.mp hh
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
    exact (Real.lt_log_iff_exp_lt hp').mp (by linarith)
  · apply Nat.le_floor
    exact (Real.log_le_iff_le_exp hp').mp (by linarith)

/-- The finite support may include extra endpoints, but those have zero
smooth weight; every contributing prime lies in the complete cell. -/
theorem smoothGiant_unnormalized_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p ∈ smoothGiantPrimeRange G,
      (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) =
    complexPrimeInterval 1 0 (G - 1) (G + 1)
      (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  let Q := (Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊).filter Nat.Prime
  have hQP : Q ⊆ smoothGiantPrimeRange G := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hprime.pos, ?_⟩, hprime⟩
    have hu : (p : ℝ) ≤ Real.exp (G + 1) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpI).2).trans (Nat.floor_le (Real.exp_nonneg _))
    exact_mod_cast hu.trans (Nat.le_ceil (Real.exp (G + 1)))
  have hs := Finset.sum_subset (f := fun (p : ℕ) =>
    (φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ)) hQP (fun p hp hn => by
    have hz : φ (Real.log p - G) = 0 := by
      by_contra hz
      apply hn
      exact Finset.mem_filter.mpr ⟨smoothGiant_nonzero_in_log_cell φ G hout p
        (smoothGiantPrimeRange_prime G p hp).pos hz, smoothGiantPrimeRange_prime G p hp⟩
    simp only [hz, Complex.ofReal_zero, zero_mul])
  rw [← hs]
  dsimp only [Q]
  rw [Finset.sum_filter]
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  simp only [Nat.modEq_one, and_true, Real.exp_log hp', Nat.floor_natCast]

/-- The normalizer is retained explicitly when the original giant law is
written as a prime logarithmic integral. -/
theorem smoothGiantPrior_interval (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℂ) :
    (∑ p : smoothGiantPrimeRange G,
      (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      complexPrimeInterval 1 0 (G - 1) (G + 1)
        (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  rw [← smoothGiant_unnormalized_interval φ G hout F, Finset.mul_sum]
  have he := Finset.sum_coe_sort (smoothGiantPrimeRange G) (fun p =>
    ((Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      ((φ (Real.log p - G) : ℂ) * F p * ((p : ℝ)⁻¹ : ℂ))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smoothGiantPrior, Complex.ofReal_div, Complex.ofReal_mul]
  ring

end Ostmann

end OAI
