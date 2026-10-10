import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveModel

namespace OAI

/-! Exact translation of simultaneous shifted primes into the Selberg sieve. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.omega
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def shiftedPrimePairs (b X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (b*q+1).Prime ∧ z<q ∧ z<b*q+1)

lemma shiftedPrimePair_coprime {b X z q : ℕ} (hq : q ∈ shiftedPrimePairs b X z) :
    (∏ p ∈ oddSievePrimes z,p).Coprime (shiftedSievePolynomial b q) := by
  obtain ⟨_,hprime,hshift,hzq,hzs⟩ := Finset.mem_filter.mp hq
  apply Nat.coprime_of_dvd
  intro p hp hpd hpv
  have hpz := (mem_oddSievePrimes.mp (mem_oddSievePrimes_of_dvd hp hpd)).1
  change p ∣ q*(b*q+1) at hpv
  rcases hp.dvd_mul.mp hpv with hd | hd
  · have he := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hd
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp hshift).mp hd
    omega

lemma shiftedPrimePairs_le_sifted (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      siftedSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) := by
  let f := shiftedSievePolynomial b
  have hinj := (shiftedSievePolynomial_strictMono b).injective
  have hsubset : (shiftedPrimePairs b X z).image f ⊆
      ((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ oddSievePrimes z,p).Coprime n) := by
    intro n hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,rfl⟩,
      shiftedPrimePair_coprime hq⟩
  have hh := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinj] at hh
  have he : siftedSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) =
      (((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ oddSievePrimes z,p).Coprime n)).card := by
    change (∑ d ∈ (Finset.Icc 1 X).image f,
      if (∏ p ∈ oddSievePrimes z,p).Coprime d then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hh

lemma shiftedPrimeSieve_multSum (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    multSum (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ) := by
  simp only [multSum,shiftedPrimeSieve]
  rw [Finset.sum_image]
  · simp only [Finset.sum_boole]
  · exact fun a _ b _ h => (shiftedSievePolynomial_strictMono _).injective h

/-- A genuine sieve bound for the actual prime pairs, with the exact local
remainders still visible for the next arithmetic estimate. -/
theorem shiftedPrimePairs_selberg (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    let s := shiftedPrimeSieve b X z y hy
    ((shiftedPrimePairs b X z).card:ℝ) ≤ X / selbergBoundingSum s +
      ∑ d ∈ (∏ p ∈ oddSievePrimes z,p).divisors,
        if (d:ℝ) ≤ y then (3:ℝ)^ArithmeticFunction.cardDistinctFactors d*
          |rem (s := s.toBoundingSieve) d| else 0 := by
  exact (shiftedPrimePairs_le_sifted b X z y hy).trans
    (selberg_bound_simple (shiftedPrimeSieve b X z y hy))

end TotientAsymptotic

end

end OAI
