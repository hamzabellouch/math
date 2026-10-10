import OAI.NumberTheory.TotientAsymptotic.TripleDensity

namespace OAI

/-! The actual simultaneous primes counted by the three-form sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def triplePrimeTuples (a b X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime ∧
    z < q ∧ z < a*q+1 ∧ z < b*q+1)

lemma triplePrimeTuples_coprime {a b X z q : ℕ} (hq : q ∈ triplePrimeTuples a b X z) :
    (∏ p ∈ tripleSievePrimes z,p).Coprime (tripleSievePolynomial a b q) := by
  obtain ⟨_,hq,ha,hb,hzq,hza,hzb⟩ := Finset.mem_filter.mp hq
  apply Nat.coprime_of_dvd
  intro p hp hpd hpv
  have hpz := (mem_tripleSievePrimes.mp (mem_tripleSievePrimes_of_dvd hp hpd)).1
  change p ∣ q*(a*q+1)*(b*q+1) at hpv
  rcases hp.dvd_mul.mp hpv with hqa|hb'
  · rcases hp.dvd_mul.mp hqa with hq'|ha'
    · have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hq'
      omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp ha).mp ha'
      omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp hb).mp hb'
    omega

lemma triplePrimeTuples_le_sifted (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ((triplePrimeTuples a b X z).card:ℝ) ≤
      siftedSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) := by
  let f := tripleSievePolynomial a b
  have hinj := (tripleSievePolynomial_strictMono a b).injective
  have hsubset : (triplePrimeTuples a b X z).image f ⊆
      ((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ tripleSievePrimes z,p).Coprime n) := by
    intro n hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,rfl⟩,
      triplePrimeTuples_coprime hq⟩
  have hh := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hinj] at hh
  have he : siftedSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) =
      (((Finset.Icc 1 X).image f).filter
        (fun n => (∏ p ∈ tripleSievePrimes z,p).Coprime n)).card := by
    change (∑ d ∈ (Finset.Icc 1 X).image f,
      if (∏ p ∈ tripleSievePrimes z,p).Coprime d then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hh

lemma triplePrimeSieve_multSum (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    multSum (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d =
      (((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ) := by
  simp only [multSum,triplePrimeSieve]
  rw [Finset.sum_image]
  · simp only [Finset.sum_boole]
  · exact fun r _ s _ h => (tripleSievePolynomial_strictMono _ _).injective h

lemma triplePrimeSieve_rem_le (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) {d : ℕ}
    (hd : Squarefree d) :
    |rem (s := (triplePrimeSieve a b X z y hy).toBoundingSieve) d| ≤ d+1 := by
  rw [rem,triplePrimeSieve_multSum]
  change |(((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ)-
    tripleSieveDensity a b d*(X:ℝ)| ≤ d+1
  have he : (X:ℝ)/d*(tripleRootCount d a b:ℝ) = tripleSieveDensity a b d*(X:ℝ) := by
    rw [tripleRootCount_density a b d hd]
    field_simp [show (d:ℝ) ≠ 0 by exact_mod_cast hd.ne_zero]
  rw [← he]
  calc
    _ ≤ |(((Finset.Icc 1 X).filter (fun q => d ∣ tripleSievePolynomial a b q)).card:ℝ)-
          (Nat.count (fun q => d ∣ tripleSievePolynomial a b q) X:ℝ)|+
        |(Nat.count (fun q => d ∣ tripleSievePolynomial a b q) X:ℝ)-
          (X:ℝ)/d*(tripleRootCount d a b:ℝ)| := abs_sub_le _ _ _
    _ ≤ 1+d := add_le_add (interval_count_discrepancy _ X)
      (tripleSieve_count_error a b d (Nat.pos_of_ne_zero hd.ne_zero) X)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
