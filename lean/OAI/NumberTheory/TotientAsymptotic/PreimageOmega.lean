import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Apart from the possible prime 2, every distinct prime contributes at
least one factor to the corresponding shifted-prime product. -/
lemma prime_shift_factor_count {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    1 ≤ (p-1).primeFactorsList.length := by
  by_contra! h
  have hnil : (p-1).primeFactorsList=[] := List.length_eq_zero_iff.mp (by omega)
  have he := Nat.prod_primeFactorsList (by have := hp.two_le; omega : p-1 ≠ 0)
  rw [hnil,List.prod_nil] at he
  have := hp.two_le
  omega

lemma preimage_factor_count {n : ℕ} (hn : 0 < n) :
    n.primeFactorsList.length ≤ n.totient.primeFactorsList.length+1 := by
  have hpn (p : ℕ) (hp : p ∈ n.primeFactors) : p ≠ 0 :=
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsn (p : ℕ) (hp : p ∈ n.primeFactors) : p-1 ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have he := congrArg (fun t : ℕ => t.primeFactorsList.length) (Nat.totient_mul_prod_primeFactors n)
  rw [omega_count_mul (Nat.totient_pos.mpr hn).ne' (Finset.prod_ne_zero_iff.mpr hpn),
    omega_count_mul hn.ne' (Finset.prod_ne_zero_iff.mpr hsn),
    omega_count_prod _ _ hpn,omega_count_prod _ _ hsn] at he
  have hpcount : (∑ p ∈ n.primeFactors, p.primeFactorsList.length)=n.primeFactors.card := by
    calc
      _ = ∑ _p ∈ n.primeFactors, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [Nat.primeFactorsList_prime (Nat.prime_of_mem_primeFactors hp)]
      _ = _ := by simp
  rw [hpcount] at he
  have hs : n.primeFactors.card ≤ 1+∑ p ∈ n.primeFactors, (p-1).primeFactorsList.length := by
    have hcard : n.primeFactors.card ≤ (n.primeFactors.erase 2).card+1 := by
      by_cases hm : 2 ∈ n.primeFactors
      · have := Finset.card_pos.mpr ⟨2,hm⟩
        rw [Finset.card_erase_of_mem hm]
        omega
      · simp [hm]
    have hsum : (n.primeFactors.erase 2).card ≤ ∑ p ∈ n.primeFactors.erase 2, (p-1).primeFactorsList.length := by
      calc
        _ = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun p hp => prime_shift_factor_count
          (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) (Finset.mem_erase.mp hp).1)
    have hsub := Finset.sum_le_sum_of_subset (Finset.erase_subset (a := 2) (s := n.primeFactors))
      (f := fun p => (p-1).primeFactorsList.length)
    omega
  omega

end TotientAsymptotic

end

end OAI
