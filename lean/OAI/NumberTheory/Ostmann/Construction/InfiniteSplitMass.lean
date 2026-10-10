import OAI.NumberTheory.Ostmann.ZeroDensity.UnsignedPrimeTail
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeDivisorMass
import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiPrimeSeries
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSplitMass

namespace OAI

/-! # Passing the prime-series bounds to a finite set of split primes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def retainedSplitTerm (d : ℤ) (D Q : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ≤ Q ∧ ¬n ∣ D ∧ jacobiSym d n = 1 then unsignedPrimeTerm s n else 0

noncomputable def divisorPrimeTerm (D : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if n ∣ D then unsignedPrimeTerm s n else 0

theorem retainedSplitTerm_support (d : ℤ) (D Q : ℕ) (s : ℝ) (n : ℕ)
    (hn : n ∉ Nat.primesLE Q) : retainedSplitTerm d D Q s n = 0 := by
  by_cases hp : n.Prime
  · have hnQ : ¬n ≤ Q := fun h => hn (Nat.mem_primesLE.mpr ⟨h, hp⟩)
    simp [retainedSplitTerm, hnQ]
  · simp [retainedSplitTerm, unsignedPrimeTerm, hp]

theorem retainedSplitTerm_summable (d : ℤ) (D Q : ℕ) (s : ℝ) :
    Summable (retainedSplitTerm d D Q s) :=
  summable_of_ne_finset_zero (s := Nat.primesLE Q) (retainedSplitTerm_support d D Q s)

theorem retainedSplitTerm_tsum (d : ℤ) (D Q : ℕ) (s : ℝ) :
    (∑' n, retainedSplitTerm d D Q s n) =
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) ^ s := by
  rw [tsum_eq_sum (s := Nat.primesLE Q) (retainedSplitTerm_support d D Q s), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [retainedSplitTerm, unsignedPrimeTerm, (Nat.mem_primesLE.mp hp).1,
    (Nat.mem_primesLE.mp hp).2, ite_true, true_and]

theorem divisorPrimeTerm_support (D : ℕ) (hD : 0 < D) (s : ℝ) (n : ℕ)
    (hn : n ∉ D.primeFactors) : divisorPrimeTerm D s n = 0 := by
  by_cases hp : n.Prime
  · have hd : ¬n ∣ D := fun h => hn (Nat.mem_primeFactors.mpr ⟨hp, h, hD.ne'⟩)
    simp [divisorPrimeTerm, hd]
  · simp [divisorPrimeTerm, unsignedPrimeTerm, hp]

theorem divisorPrimeTerm_summable (D : ℕ) (hD : 0 < D) (s : ℝ) :
    Summable (divisorPrimeTerm D s) :=
  summable_of_ne_finset_zero (s := D.primeFactors) (divisorPrimeTerm_support D hD s)

theorem divisorPrimeTerm_mass (D Y : ℕ) (s : ℝ) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s) :
    (∑' n, divisorPrimeTerm D s n) ≤ Y + Real.log D / Y := by
  have hP : ∀ p ∈ D.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hf : D.primeFactors.filter (fun p => p ∣ D) = D.primeFactors :=
    Finset.filter_true_of_mem (fun p hp => (Nat.mem_primeFactors.mp hp).2.1)
  have hb := prime_divisor_mass_bound D.primeFactors D Y s hP hD hY hs
  rw [hf] at hb
  rw [tsum_eq_sum (s := D.primeFactors) (divisorPrimeTerm_support D hD s)]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [divisorPrimeTerm, unsignedPrimeTerm, (Nat.mem_primeFactors.mp hp).1,
    (Nat.mem_primeFactors.mp hp).2.1, ite_true]

/-- This is the pointwise split-prime identity, with explicit losses for
large primes and divisors of the excluded integer. -/
theorem split_prime_pointwise (d : ℤ) (D Q : ℕ) (s : ℝ) (hdD : d.natAbs ∣ D) (n : ℕ) :
    unsignedPrimeTerm s n + jacobiPrimeTerm d s n ≤
      2 * retainedSplitTerm d D Q s n + 2 * unsignedPrimeTail Q s n + 2 * divisorPrimeTerm D s n := by
  by_cases hp : n.Prime
  · let w := Real.log n / (n : ℝ) ^ s
    have hw : 0 ≤ w := by
      simpa only [w, unsignedPrimeTerm, ite_eq_left hp] using unsignedPrimeTerm_nonneg s n
    have hj : jacobiPrimeTerm d s n = w * (jacobiSym d n : ℝ) := by
      simp only [jacobiPrimeTerm, ite_eq_left hp, w]
      ring
    rw [hj]
    simp only [unsignedPrimeTerm, ite_eq_left hp, retainedSplitTerm, divisorPrimeTerm, unsignedPrimeTail]
    change w + w * (jacobiSym d n : ℝ) ≤
      2 * (if n ≤ Q ∧ ¬n ∣ D ∧ jacobiSym d n = 1 then w else 0) +
      2 * (if Q < n then w else 0) + 2 * (if n ∣ D then w else 0)
    rcases jacobiSym.trichotomy d n with hz | ho | hm
    · have hnD : n ∣ D := by
        by_contra hnot
        exact jacobi_ne_zero_of_prime_not_dvd d hp (fun h => hnot (h.trans hdD)) hz
      simp only [hz, Int.cast_zero, mul_zero, add_zero, hnD, ite_true]
      split_ifs <;> linarith
    · by_cases hnQ : n ≤ Q <;> by_cases hnD : n ∣ D <;>
        simp [ho, hnQ, hnD, show Q < n ↔ ¬n ≤ Q by omega] <;> linarith
    · simp only [hm, Int.cast_neg, Int.cast_one, mul_neg_one, add_neg_cancel]
      positivity
  · simp [unsignedPrimeTerm, jacobiPrimeTerm, retainedSplitTerm, unsignedPrimeTail,
      divisorPrimeTerm, hp]

/-- Infinite unsigned and signed series give a lower bound for the actual
finite retained set; all excluded-divisor weights are bounded explicitly. -/
theorem retained_split_mass_from_series (d : ℤ) (D Q Y : ℕ) (s L B T : ℝ)
    (hdD : d.natAbs ∣ D) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s)
    (hu : Summable (unsignedPrimeTerm s)) (hj : Summable (jacobiPrimeTerm d s))
    (ht : Summable (unsignedPrimeTail Q s))
    (hL : L ≤ ∑' n, unsignedPrimeTerm s n)
    (hB : -B ≤ ∑' n, jacobiPrimeTerm d s n)
    (hT : (∑' n, unsignedPrimeTail Q s n) ≤ T) :
    (L - B) / 2 - T - (Y + Real.log D / Y) ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) ^ s := by
  have hr := retainedSplitTerm_summable d D Q s
  have hd := divisorPrimeTerm_summable D hD s
  have hineq := (hu.add hj).tsum_le_tsum (split_prime_pointwise d D Q s hdD)
    (((hr.mul_left 2).add (ht.mul_left 2)).add (hd.mul_left 2))
  rw [hu.tsum_add hj, ((hr.mul_left 2).add (ht.mul_left 2)).tsum_add (hd.mul_left 2),
    (hr.mul_left 2).tsum_add (ht.mul_left 2), hr.tsum_mul_left, ht.tsum_mul_left, hd.tsum_mul_left,
    retainedSplitTerm_tsum] at hineq
  have hdiv := divisorPrimeTerm_mass D Y s hD hY hs
  linarith

end Ostmann

end OAI
