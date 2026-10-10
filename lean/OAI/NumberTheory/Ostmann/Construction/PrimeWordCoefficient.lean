import OAI.NumberTheory.Ostmann.Construction.WordCoefficientNorm
import OAI.NumberTheory.Ostmann.Construction.WordPrimeCheckBound

namespace OAI

/-! # The coefficient retaining the large-prime coprimality support -/

namespace Ostmann.WordFourierParameters

open scoped Classical

noncomputable def primeUnitRangedCoefficient {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) : ℂ :=
  if ∀ g ∈ C.checks template t ht .prime,
      g.Holds (expandedPrimeValues n (fun i => (x i : ℤ))) x then
    p.unitRangedCoefficient U D template t ht (expandedPrimeValues n (fun i => (x i : ℤ)))
  else 0

theorem primeUnitRangedCoefficient_norm {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    ‖p.primeUnitRangedCoefficient C U D template t ht x‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) := by
  unfold primeUnitRangedCoefficient
  split_ifs
  · exact p.unitRangedCoefficient_norm U D template t ht _
  · simpa only [norm_zero] using pow_nonneg
      ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) (2 ^ n)

/-- This identity also covers invalid histories: both coefficients vanish. -/
theorem primeUnitRangedCoefficient_nat {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    p.primeUnitRangedCoefficient C U D template t ht x =
      (if C.ValidAt template (expandedPrimeNatValues n x) x t then 1 else 0) *
        p.unitRangedCoefficient U D template t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  by_cases hv : ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable V n)) n
      (template.state (expandedPrimeNatValues n x)) t
  · have he := C.checks_iff template t ht .prime
      (expandedPrimeValues n (fun i => (x i : ℤ))) (expandedPrimeNatValues n x) x
      (by intro i; simp only [HistoryFormula.value_prime]; cases i <;>
        simp only [expandedPrimeValues, expandedPrimeNatValues, Int.cast_natCast, Int.cast_one, Nat.cast_one]) hv
    unfold primeUnitRangedCoefficient
    simp only [he]
    split_ifs <;> simp only [one_mul, zero_mul]
  · have hz : p.unitRangedCoefficient U D template t ht
        (expandedPrimeValues n (fun i => (x i : ℤ))) = 0 := by
      rw [← expandedPrimeNatValues_cast]
      simp only [unitRangedCoefficient, rangedCoefficient,
        p.coefficient_eq_zero_of_not_valid template t ht _ hv, mul_zero]
    simp only [primeUnitRangedCoefficient, hz, ite_self, mul_zero]

end Ostmann.WordFourierParameters

end OAI
