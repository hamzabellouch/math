import OAI.NumberTheory.TotientAsymptotic.SuffixFactorization

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

lemma prime_dvd_le_largest {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hd : p ∣ n) :
    p ≤ largestPrimeFactor n :=
  primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hd)

/-- Taking a totient cannot introduce a prime larger than every prime of its
argument. This also covers `n = 0` under the existing largest-factor convention. -/
lemma largestPrimeFactor_totient_le (n : ℕ) :
    largestPrimeFactor n.totient ≤ largestPrimeFactor n := by
  by_cases hn : n = 0
  · subst n
    simp [largestPrimeFactor]
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro q hq hqφ _
  have hdiv : q ∣ n*∏ p ∈ n.primeFactors, (p-1) := by
    rw [← Nat.totient_mul_prod_primeFactors]
    exact hqφ.trans (dvd_mul_right _ _)
  rcases hq.dvd_mul.mp hdiv with hqn | hqp
  · exact prime_dvd_le_largest hq hn hqn
  · obtain ⟨p, hp, hqp⟩ := hq.prime.dvd_finsetProd_iff (fun p : ℕ => p-1) |>.mp hqp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hpp.one_lt) hqp
    exact hle.trans ((Nat.sub_le _ _).trans
      (prime_dvd_le_largest hpp hn (Nat.mem_primeFactors.mp hp).2.1))

lemma largestPrimeFactor_mul_le {a b z : ℕ}
    (ha : largestPrimeFactor a ≤ z) (hb : largestPrimeFactor b ≤ z) :
    largestPrimeFactor (a*b) ≤ z := by
  apply largestPrimeFactor_le_of_prime_divisors ((le_max_left _ _).trans ha)
  intro p hp hd hn
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · exact (prime_dvd_le_largest hp (left_ne_zero_of_mul hn) hpa).trans ha
  · exact (prime_dvd_le_largest hp (right_ne_zero_of_mul hn) hpb).trans hb

lemma largestPrimeFactor_prod_le {ι : Type*} (I : Finset ι) (f : ι → ℕ) {z : ℕ}
    (hz : 1 ≤ z) (hf : ∀ i ∈ I, largestPrimeFactor (f i) ≤ z) :
    largestPrimeFactor (∏ i ∈ I, f i) ≤ z := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa [largestPrimeFactor] using hz
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi]
    exact largestPrimeFactor_mul_le (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma largestPrimeFactor_prime {p : ℕ} (hp : p.Prime) : largestPrimeFactor p = p := by
  simp [largestPrimeFactor, hp.primeFactors, max_eq_right hp.one_lt.le]

/-- The actual residual integer after a cutoff is smooth below the next
prime. The final cofactor may repeat the last displayed prime. -/
theorem basic_suffix_totient_smooth {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hj : j < L x H) :
    largestPrimeFactor (suffixPreimage η j).totient ≤ remainderPrime η (j+1) := by
  apply (largestPrimeFactor_totient_le _).trans
  unfold suffixPreimage
  have hj' : j+1 ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hp := (hη.2.1 (j+1) hj').1
  apply largestPrimeFactor_mul_le
  · apply hη.2.2.2.1.trans
    rcases eq_or_lt_of_le (show j+1 ≤ L x H by omega) with he | he
    · rw [he]
    · exact (basic_remainder_prime_strictAnti hη hj'
        (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) he (he.trans hL)).le
  · apply largestPrimeFactor_prod_le _ _ hp.one_lt.le
    intro r hr
    have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
    rw [largestPrimeFactor_prime (hη.2.1 r hr').1]
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hr).1 with he | he
    · rw [he]
    · exact (basic_remainder_prime_strictAnti hη hj' hr' he
        ((Finset.mem_Icc.mp hj').2.trans_lt hL)).le

end TotientAsymptotic

end

end OAI
