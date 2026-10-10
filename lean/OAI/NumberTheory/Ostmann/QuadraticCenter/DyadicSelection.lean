import Mathlib.Data.Nat.Log
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums

namespace OAI

open Erdos970

namespace Ostmann.QuadraticCenter
open scoped BigOperators

noncomputable def primeWeight (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.log p / p

def dyadicPrimeBlock (P : Finset ℕ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p => Nat.log 2 p = j)

lemma dyadicPrimeBlock_subset (P : Finset ℕ) (j : ℕ) : dyadicPrimeBlock P j ⊆ P :=
  Finset.filter_subset _ _

lemma dyadicPrimeBlock_bounds {P : Finset ℕ} {j p : ℕ}
    (hp : p ∈ dyadicPrimeBlock P j) (hpos : 0 < p) :
    2 ^ j ≤ p ∧ p < 2 * 2 ^ j := by
  have hj := (Finset.mem_filter.mp hp).2
  constructor
  · simpa only [hj] using Nat.pow_log_le_self 2 hpos.ne'
  · have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) p
    simpa only [hj, Nat.pow_succ, Nat.mul_comm] using h

lemma primeWeight_dyadic_le_card (P : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primeWeight (dyadicPrimeBlock P j) ≤
      ((dyadicPrimeBlock P j).card : ℝ) *
        (Real.log (2 * (2 ^ j : ℕ)) / (2 ^ j : ℕ)) := by
  unfold primeWeight
  calc
    _ ≤ ∑ _ ∈ dyadicPrimeBlock P j,
        Real.log (2 * (2 ^ j : ℕ)) / (2 ^ j : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := hprime p (dyadicPrimeBlock_subset P j hp)
      have hb := dyadicPrimeBlock_bounds hp hpp.pos
      have hz : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlo : ((2 ^ j : ℕ) : ℝ) ≤ p := by exact_mod_cast hb.1
      have hhi : (p : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast hb.2.le
      have hlog : Real.log p ≤ Real.log (2 * (2 ^ j : ℕ)) :=
        Real.log_le_log hpR hhi
      have hlog0 : 0 ≤ Real.log (2 * (2 ^ j : ℕ)) :=
        (Real.log_nonneg (by exact_mod_cast hpp.one_le)).trans hlog
      exact (div_le_div_of_nonneg_right hlog hpR.le).trans
        (div_le_div_of_nonneg_left hlog0 hz hlo)
    _ = _ := by simp

theorem exists_weighted_dyadic_prime_block (P : Finset ℕ) (N : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) :
    ∃ j : ℕ, j ≤ Nat.log 2 N ∧
      primeWeight P * (2 ^ j : ℕ) ≤
        (Nat.log 2 N + 1 : ℕ) * Real.log (2 * (2 ^ j : ℕ)) *
          (dyadicPrimeBlock P j).card := by
  classical
  let J := Finset.range (Nat.log 2 N + 1)
  have hJ : J.Nonempty := ⟨0, by simp [J]⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J
    (fun j => primeWeight (dyadicPrimeBlock P j)) hJ
  have hmap : ∀ p ∈ P, Nat.log 2 p ∈ J := by
    intro p hp
    simpa only [J, Finset.mem_range, Nat.lt_succ_iff] using Nat.log_mono_right (hN p hp)
  have he : (∑ j ∈ J, primeWeight (dyadicPrimeBlock P j)) = primeWeight P := by
    exact Finset.sum_fiberwise_of_maps_to hmap (fun p : ℕ => Real.log p / p)
  have hsum := Finset.sum_le_sum (fun k hk => hmax k hk)
  rw [he] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, J, Finset.card_range] at hsum
  have hcard := primeWeight_dyadic_le_card P j hprime
  have hnum := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg (Nat.log 2 N + 1))
  have hz : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hb := mul_le_mul_of_nonneg_right (hsum.trans hnum) hz.le
  refine ⟨j, by simpa only [J, Finset.mem_range, Nat.lt_succ_iff] using hj, ?_⟩
  calc
    _ ≤ _ := hb
    _ = _ := by field_simp

end Ostmann.QuadraticCenter

end OAI
