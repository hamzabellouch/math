import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Elementary harmonic and padding-weight bounds for the crude enumeration. -/

namespace TwoPointCorrelations

open Finset

/-- Enlarging primes to all positive integers already gives enough mass
control for the negligible-word estimates. -/
lemma primeHarmonicMass_le_one_add_log (P : Finset ℕ) (B : ℕ)
    (hpos : ∀ p ∈ P, 1 ≤ p) (hB : ∀ p ∈ P, p ≤ B) :
    primeHarmonicMass P ≤ 1 + Real.log B := by
  have heq : primeHarmonicMass P = ∑ p ∈ P, (p : ℝ)⁻¹ := by
    simpa only [primeHarmonicMass, Finset.attach_eq_univ] using
      (Finset.sum_attach P (fun p : ℕ => (p : ℝ)⁻¹))
  rw [heq]
  calc
    _ ≤ ∑ p ∈ Icc 1 B, (p : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun p hp => mem_Icc.mpr ⟨hpos p hp, hB p hp⟩
      · intro p _ _
        positivity
    _ = (harmonic B : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log B

lemma primeHarmonicMass_le_one_add_scale (P : Finset ℕ) (B : ℕ) (L : ℝ)
    (hpos : ∀ p ∈ P, 1 ≤ p) (hB : ∀ p ∈ P, p ≤ B)
    (hBpos : 0 < B) (hscale : (B : ℝ) ≤ Real.exp L) :
    primeHarmonicMass P ≤ 1 + L := by
  apply (primeHarmonicMass_le_one_add_log P B hpos hB).trans
  have h := Real.log_le_log (by exact_mod_cast hBpos) hscale
  rw [Real.log_exp] at h
  linarith

/-- The actual padding weight `u(q)=4^ω(q)`. -/
noncomputable def crudePaddingWeight (q : ℕ) : ℝ := 4 ^ q.primeFactors.card

lemma crudePaddingWeight_le (q : ℕ) (L : ℝ) (hL : 0 < L)
    (hq : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    crudePaddingWeight q ≤ L ^ (100 * Real.log 4) := by
  have hfour : (0 : ℝ) < 4 := by norm_num
  unfold crudePaddingWeight
  calc
    _ = Real.exp ((q.primeFactors.card : ℝ) * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log hfour]
    _ ≤ Real.exp (Real.log L * (100 * Real.log 4)) := by
      apply Real.exp_le_exp.mpr
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hq hl4]
    _ = _ := (Real.rpow_def_of_pos hL _).symm

end TwoPointCorrelations

end OAI
