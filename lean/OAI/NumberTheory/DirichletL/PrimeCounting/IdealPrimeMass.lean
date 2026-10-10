import OAI.NumberTheory.DirichletL.IdealMangoldt
import OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass

namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

def primeClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ Prime I} n

def higherClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ ¬Prime I} n

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply ite_eq_right
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, ite_eq_left hn, mul_zero]
  · rw [ite_eq_right hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

def primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset.filter
    (fun P => P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N)

@[simp] theorem mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) (P : Ideal O) :
    P ∈ primeIdealsBelow C N ↔ P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N := by
  simp only [primeIdealsBelow, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

theorem zero_not_mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) :
    (0 : Ideal O) ∉ primeIdealsBelow C N := by
  intro h
  exact ((mem_primeIdealsBelow C N 0).mp h).2.1.ne_zero rfl

def primeLogMass (C : Set (Ideal O)) (N : ℕ) : ℝ :=
  ∑ P ∈ primeIdealsBelow C N, Real.log (Ideal.absNorm P)

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

theorem primeLogMass_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => primeLogMass C N / N) atTop (𝓝 A) := by
  simpa only [primeLogMass_eq_cumsum] using primeClassCoeff_ratio_tendsto C h

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
