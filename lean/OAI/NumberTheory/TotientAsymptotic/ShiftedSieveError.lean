import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveRemainder

namespace OAI

/-! A polynomial bound for the complete error term of the concrete Selberg sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

lemma odd_sieve_divisor_weight {z d : ℕ} (hd : d ∣ ∏ p ∈ oddSievePrimes z,p) :
    (3:ℕ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
  have hsq := (oddSievePrimes_prod_squarefree z).squarefree_of_dvd hd
  have hlen : ArithmeticFunction.cardDistinctFactors d ≤ d.primeFactorsList.length :=
    d.primeFactorsList.dedup_sublist.length_le
  calc
    _ ≤ 3^d.primeFactorsList.length := Nat.pow_le_pow_right (by norm_num) hlen
    _ ≤ d.primeFactorsList.prod := List.pow_length_le_prod _ 3 (by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactorsList hp
      have hmem := mem_oddSievePrimes_of_dvd hprime ((Nat.dvd_of_mem_primeFactorsList hp).trans hd)
      have hh := mem_oddSievePrimes.mp hmem
      have := hprime.two_le
      omega)
    _ = d := Nat.prod_primeFactorsList hsq.ne_zero

lemma shiftedPrimeSieve_error_sum (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
      if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
        |rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d| else 0) ≤ 2*y^3 := by
  classical
  let P : ℕ := ∏ p ∈ oddSievePrimes z,p
  let T : Finset ℕ := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ y)
  have hP := oddSievePrimes_prod_squarefree z
  have hT (d : ℕ) (hd : d∈T) : d∣P ∧ 1≤d ∧ (d:ℝ)≤y := by
    obtain ⟨hd,hy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd,hP0⟩ := Nat.mem_divisors.mp hd
    have h0 : d≠0 := by
      intro h
      subst d
      exact hP0 (zero_dvd_iff.mp hd)
    exact ⟨hd,Nat.one_le_iff_ne_zero.mpr h0,hy⟩
  have hcard : (T.card:ℝ) ≤ y := by
    have hsub : T ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro d hd
      have hh := hT d hd
      exact Finset.mem_Icc.mpr ⟨hh.2.1,Nat.le_floor hh.2.2⟩
    have hh := Finset.card_le_card hsub
    have hc : (T.card:ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast (by simpa using hh : T.card ≤ ⌊y⌋₊)
    exact hc.trans (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter]
  change (∑ d ∈ T,(3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
      |rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d|) ≤ _
  calc
    _ ≤ ∑ _d ∈ T,2*y^2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd,h1,hdy⟩ := hT d hd
      have hweight : (3:ℝ)^ArithmeticFunction.cardDistinctFactors d ≤ d := by
        exact_mod_cast odd_sieve_divisor_weight hd
      have hrem := shiftedPrimeSieve_rem_le b X z y hy (hP.squarefree_of_dvd hd)
      have hdR : (1:ℝ)≤d := by exact_mod_cast h1
      have hh := mul_le_mul hweight hrem (abs_nonneg _) (by positivity : (0:ℝ)≤d)
      nlinarith
    _ = (T.card:ℝ)*(2*y^2) := by simp
    _ ≤ y*(2*y^2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- All arithmetic remainders in the two-linear-form sieve are now eliminated. -/
theorem shiftedPrimePairs_bound (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      X/selbergBoundingSum (shiftedPrimeSieve b X z y hy)+2*y^3 :=
  (shiftedPrimePairs_selberg b X z y hy).trans
    (add_le_add le_rfl (shiftedPrimeSieve_error_sum b X z y hy))

end TotientAsymptotic

end

end OAI
