import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI


namespace InternalCatalan

open scoped BigOperators

def rationalPrimeSupport (q : ℚ) : Finset ℕ :=
  q.num.natAbs.primeFactors ∪ q.den.primeFactors

theorem prime_of_mem_rationalPrimeSupport (q : ℚ) {p : ℕ}
    (hp : p ∈ rationalPrimeSupport q) : p.Prime := by
  rcases Finset.mem_union.mp hp with hn | hd
  · exact Nat.prime_of_mem_primeFactors hn
  · exact Nat.prime_of_mem_primeFactors hd

theorem valuation_zero_outside_rationalPrimeSupport (q : ℚ) {p : ℕ}
    (hp : p.Prime) (hs : p ∉ rationalPrimeSupport q) : padicValRat p q = 0 := by
  have hn : p ∉ q.num.natAbs.factorization.support := by
    intro hn
    apply hs
    exact Finset.mem_union_left _ hn
  have hd : p ∉ q.den.factorization.support := by
    intro hd
    apply hs
    exact Finset.mem_union_right _ hd
  have hn0 := Finsupp.notMem_support_iff.mp hn
  have hd0 := Finsupp.notMem_support_iff.mp hd
  rw [Nat.factorization_def _ hp] at hn0
  rw [Nat.factorization_def _ hp] at hd0
  simp only [padicValRat, padicValInt, hn0, hd0, Nat.cast_zero, sub_self]

theorem log_nat_eq_sum_factorization_on (n : ℕ) (s : Finset ℕ)
    (hs : n.primeFactors ⊆ s) :
    Real.log (n : ℝ) = ∑ p ∈ s, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset hs
  intro p _ hp
  have hzero : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
  simp only [hzero, Nat.cast_zero, zero_mul]

theorem positive_rational_cast_eq_natAbs_num_div_den (q : ℚ) (hq : 0 < q) :
    (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
  have hn : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hnreal : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    calc
      (q.num.natAbs : ℝ) = ((q.num.natAbs : ℤ) : ℝ) := (Int.cast_natCast _).symm
      _ = (q.num : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hn
  rw [hnreal, Rat.cast_def]

theorem log_positive_rational_eq_sum_valuations (q : ℚ) (hq : 0 < q) :
    Real.log (q : ℝ) =
      ∑ p ∈ rationalPrimeSupport q, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  have hn : q.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq.ne')
  have hden : q.den ≠ 0 := q.den_ne_zero
  have hns : q.num.natAbs.primeFactors ⊆ rationalPrimeSupport q :=
    Finset.subset_union_left
  have hds : q.den.primeFactors ⊆ rationalPrimeSupport q :=
    Finset.subset_union_right
  rw [positive_rational_cast_eq_natAbs_num_div_den q hq,
    Real.log_div (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hden),
    log_nat_eq_sum_factorization_on _ _ hns,
    log_nat_eq_sum_factorization_on _ _ hds, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := prime_of_mem_rationalPrimeSupport q hp
  rw [Nat.factorization_def _ hprime, Nat.factorization_def _ hprime]
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast, sub_mul]

theorem log_positive_rational_eq_sum_valuations_on (q : ℚ) (hq : 0 < q)
    (s : Finset ℕ) (hs : rationalPrimeSupport q ⊆ s)
    (hprime : ∀ p ∈ s, p.Prime) :
    Real.log (q : ℝ) = ∑ p ∈ s, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  rw [log_positive_rational_eq_sum_valuations q hq]
  apply Finset.sum_subset hs
  intro p hp hps
  rw [valuation_zero_outside_rationalPrimeSupport q (hprime p hp) hps]
  simp only [Int.cast_zero, zero_mul]

@[simp] theorem rationalPrimeSupport_neg (q : ℚ) :
    rationalPrimeSupport (-q) = rationalPrimeSupport q := by
  simp [rationalPrimeSupport]

theorem log_abs_rational_eq_sum_valuations (q : ℚ) (hq : q ≠ 0) :
    Real.log |(q : ℝ)| =
      ∑ p ∈ rationalPrimeSupport q, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  by_cases hpos : 0 < q
  · have hreal : 0 < (q : ℝ) := by exact_mod_cast hpos
    rw [abs_of_pos hreal]
    exact log_positive_rational_eq_sum_valuations q hpos
  · have hneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hq
    have hreal : (q : ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hreal]
    have hformula := log_positive_rational_eq_sum_valuations (-q) (neg_pos.mpr hneg)
    simpa only [Rat.cast_neg, rationalPrimeSupport_neg, padicValRat.neg] using hformula

theorem log_abs_rational_eq_sum_valuations_on (q : ℚ) (hq : q ≠ 0)
    (s : Finset ℕ) (hs : rationalPrimeSupport q ⊆ s)
    (hprime : ∀ p ∈ s, p.Prime) :
    Real.log |(q : ℝ)| = ∑ p ∈ s, (padicValRat p q : ℝ) * Real.log (p : ℝ) := by
  rw [log_abs_rational_eq_sum_valuations q hq]
  apply Finset.sum_subset hs
  intro p hp hps
  rw [valuation_zero_outside_rationalPrimeSupport q (hprime p hp) hps]
  simp only [Int.cast_zero, zero_mul]

theorem log_abs_determinantRat_eq_sum_valuations (z : ℚ) (N : ℕ)
    (hdet : determinantRat z N ≠ 0) :
    Real.log |(determinantRat z N : ℝ)| =
      ∑ p ∈ rationalPrimeSupport (determinantRat z N),
        (padicValRat p (determinantRat z N) : ℝ) * Real.log (p : ℝ) :=
  log_abs_rational_eq_sum_valuations (determinantRat z N) hdet

end InternalCatalan

end OAI
