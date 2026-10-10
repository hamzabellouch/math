import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalFactors
import Mathlib.NumberTheory.LSeries.Basic

namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

lemma mrtTypical_count_pos {ι : Type*} {J : Finset ι} {P : ι → Finset ℕ}
    {j : ι} (hj : j ∈ J) {n : ℕ} (hn : mrtTypical J P n) :
    0 < finitePrimeDivisorCount (P j) n := by
  obtain ⟨p, hp, hpn⟩ := hn j hj
  exact finitePrimeDivisorCount_pos_of_mem hp hpn

lemma mrtTypical_prime_mul {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    {p : ℕ} (hp : p ∈ P j) (m : ℕ) :
    mrtTypical J P (p * m) ↔ mrtTypical (J.erase j) P m := by
  have hnot (i : ι) (hi : i ∈ J.erase j) : p ∉ P i := by
    intro hpi
    exact Finset.disjoint_left.mp (hdis (mem_erase.mp hi).2 hj (mem_erase.mp hi).1)
      hpi hp
  have hd : mrtPrimeAvoids ((J.erase j).biUnion P) p := by
    intro q hq hqp
    obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
    have he : q = p := (Nat.prime_dvd_prime_iff_eq
      (hP i (mem_erase.mp hi).2 q hqi) (hP j hj p hp)).mp hqp
    exact hnot i hi (he ▸ hqi)
  have hmul := mrtTypical_mul_of_avoids (J.erase j) P
    (fun i hi => hP i (mem_erase.mp hi).2) hd m
  constructor
  · intro h
    apply hmul.mp
    exact fun i hi => h i (mem_erase.mp hi).2
  · intro h i hi
    by_cases hij : i = j
    · subst i
      exact ⟨p, hp, dvd_mul_right p m⟩
    · exact hmul.mpr h i (mem_erase.mpr ⟨hij, hi⟩)

lemma mrtTypical_ramare_supported {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount (P j) n = 0 then 0 else
      if mrtTypical J P n then F n else 0) =
      if mrtTypical J P n then F n else 0 := by
  by_cases ht : mrtTypical J P n
  · have hpos := mrtTypical_count_pos hj ht
    simp only [ht, ite_true, ne_of_gt hpos, ite_false]
  · simp only [ht, ite_false, ite_self]

/-- Exact corrected typical-set decomposition at one prime band. -/
theorem mrt_typical_ramare_sum {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, if mrtTypical J P n then F n else 0) =
      ∑ p ∈ P j, ∑ m ∈ Icc 1 (N / p),
        if mrtTypical (J.erase j) P m then
          F (p * m) /
            (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount (P j) m : ℕ) : ℂ)
        else 0 := by
  have he := mrt_ramare_sum (P j) (hP j hj)
    (fun n => if mrtTypical J P n then F n else 0) N
  simp only [mrtTypical_ramare_supported J P hj F] at he
  rw [he]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro m _
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs <;> simp

/-- The same prime-square exceptional bound holds after restriction to all
the other typical-factorization bands. -/
theorem mrt_typical_ramare_error {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (N : ℕ) (hF : OneBounded F) :
    ‖(∑ n ∈ Icc 1 N, if mrtTypical J P n then F n else 0) -
      (∑ p ∈ P j, ∑ m ∈ Icc 1 (N / p),
        if mrtTypical (J.erase j) P m then
          F (p * m) / ((finitePrimeDivisorCount (P j) m + 1 : ℕ) : ℂ)
        else 0)‖ ≤ (N : ℝ) * ∑ p ∈ P j, (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hFb : OneBounded (fun n => if mrtTypical J P n then F n else 0) := by
    intro n hn
    dsimp only
    split_ifs
    · exact hF n hn
    · simp
  have he := mrt_ramare_error_of_bounded (P j) (hP j hj)
    (fun n => if mrtTypical J P n then F n else 0) N hFb
  simp only [mrtTypical_ramare_supported J P hj F] at he
  have hs : (∑ p ∈ P j, ∑ m ∈ Icc 1 (N / p),
      (if mrtTypical J P (p * m) then F (p * m) else 0) /
        ((finitePrimeDivisorCount (P j) m + 1 : ℕ) : ℂ)) =
      ∑ p ∈ P j, ∑ m ∈ Icc 1 (N / p),
        if mrtTypical (J.erase j) P m then
          F (p * m) / ((finitePrimeDivisorCount (P j) m + 1 : ℕ) : ℂ) else 0 := by
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro m _
    rw [mrtTypical_prime_mul J P hP hdis hj hp]
    split_ifs <;> simp
  rwa [hs] at he

lemma mrt_LSeries_term_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  rw [LSeries.term_of_ne_zero (Nat.mul_pos hm hn).ne', LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', hF m n hm hn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, div_mul_div_comm]

/-- The actual Dirichlet polynomial splits into a prime factor and a
cofactor polynomial with the corrected reciprocal prime-count weight. -/
theorem mrt_typical_dirichlet_factorization {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, if mrtTypical J P n then LSeries.term F s n else 0) =
      ∑ p ∈ P j, ∑ m ∈ Icc 1 (N / p),
        if mrtTypical (J.erase j) P m then
          (LSeries.term F s p * LSeries.term F s m) /
            (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount (P j) m : ℕ) : ℂ)
        else 0 := by
  rw [mrt_typical_ramare_sum J P hP hdis hj (LSeries.term F s) N]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro m hm
  rw [mrt_LSeries_term_mul F hF s (hP j hj p hp).pos (mem_Icc.mp hm).1]

end TwoPointCorrelations

end OAI
