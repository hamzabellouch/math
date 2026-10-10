import OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

universe uIota

/-!
# The odd-coefficient obstruction modulo eight

The identity coefficient of an integer cyclic norm is the sum of the actual
coefficient squares. Every odd square is one modulo eight. Consequently an
odd-coefficient element in a cyclic group of order divisible by eight cannot
have norm scalar `4 * u^2` with `u` odd. The divisibility hypothesis excludes
order four, so the explicit order-four example is not ruled out.
-/

namespace CirculantHadamard

open scoped BigOperators

/-- Every odd integer square is congruent to one modulo eight. -/
theorem odd_sq_mod_eight {a : ℤ} (ha : Odd a) :
    Int.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  nlinarith [hm]

/-- A finite sum of odd integer squares is congruent to the number of terms. -/
theorem sum_odd_sq_mod_eight {ι : Type uIota} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by
  classical
  revert ha
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Int.ModEq]
  · intro i s hi ih ha
    have hiOdd : Odd (a i) := ha i (Finset.mem_insert_self i s)
    have hsOdd : ∀ j ∈ s, Odd (a j) :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, add_comm (s.card : ℤ) 1] using
      (odd_sq_mod_eight hiOdd).add (ih hsOdd)

/-- The same congruence for all members of a finite type. -/
theorem sum_univ_odd_sq_mod_eight {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) :
    Int.ModEq 8 (∑ i, a i ^ 2) (Fintype.card ι : ℤ) := by
  simpa using sum_odd_sq_mod_eight Finset.univ a (fun i _ => ha i)

/-- A multiple of eight odd squares cannot sum to four times an odd square. -/
theorem odd_sq_sum_ne_four_mul_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℤ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ 4 * u ^ 2 := by
  have hc : (8 : ℤ) ∣ (Fintype.card ι : ℤ) :=
    Int.natCast_dvd_natCast.mpr hcard
  have hzero : Int.ModEq 8 (∑ i, a i ^ 2) 0 :=
    (sum_univ_odd_sq_mod_eight a ha).trans (Int.modEq_zero_iff_dvd.mpr hc)
  have hfour : Int.ModEq 8 (4 * u ^ 2) 4 := by
    simpa using (odd_sq_mod_eight hu).mul_left 4
  intro hsum
  rw [hsum] at hzero
  have hbad : Int.ModEq 8 (0 : ℤ) 4 := hzero.symm.trans hfour
  norm_num [Int.ModEq] at hbad

/-- Natural norm parameters are cast only after forming the literal scalar. -/
theorem odd_sq_sum_ne_four_mul_nat_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℕ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ ((4 * u ^ 2 : ℕ) : ℤ) := by
  simpa using odd_sq_sum_ne_four_mul_sq a ha hcard ((Int.odd_coe_nat u).mpr hu)

/-- The actual cyclic norm equation is impossible for an all-odd row when
the cyclic order is divisible by eight and the norm parameter is odd. -/
theorem odd_norm_four_impossible {n u : ℕ} [NeZero n]
    (hcard : 8 ∣ n) (hu : Odd u) (T : CyclicRing.Elem ℤ n)
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar n ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  have hsum : (∑ a : ZMod n, T.coeff a ^ 2) = ((4 * u ^ 2 : ℕ) : ℤ) := by
    rw [← cyclicNorm_identity_coeff T, hnorm]
    simp
  exact odd_sq_sum_ne_four_mul_nat_sq (fun a : ZMod n => T.coeff a) hodd
    (by simpa using hcard) hu hsum

/-- For `k ≥ 3`, the order `2^k` meets the exact modulo-eight obstruction. -/
theorem odd_norm_four_impossible_two_pow {k u : ℕ} [NeZero (2 ^ k)]
    (hk : 3 ≤ k) (hu : Odd u) (T : CyclicRing.Elem ℤ (2 ^ k))
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ k) ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  apply odd_norm_four_impossible (u := u) ?_ hu T hodd hnorm
  exact (show 8 ∣ 2 ^ k from pow_dvd_pow 2 hk)

end CirculantHadamard

end OAI
