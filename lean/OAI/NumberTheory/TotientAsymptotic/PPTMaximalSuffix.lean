import OAI.NumberTheory.TotientAsymptotic.PPTTrivialFibers

namespace OAI

/-!
The maximal common-prefix step in Ford, Section 5, between (5.19) and
(5.20).  The ordering of the candidate primes, rather than a bound for the
whole residual product, rules out a repeated leading prime.  Choosing the
last possible common prefix then forces every nontrivial residual
preimage to have a different largest prime.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- A prime larger than every prime of `a` cannot divide its totient. -/
lemma ppt_not_dvd_totient_of_prime_bound {p a : ℕ} (hp : p.Prime)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ a → q < p) : ¬p ∣ a.totient := by
  intro hdiv
  have hprod : p ∣ a * ∏ q ∈ a.primeFactors, (q-1) := by
    rw [← Nat.totient_mul_prod_primeFactors]
    exact hdiv.trans (dvd_mul_right _ _)
  rcases hp.dvd_mul.mp hprod with hpa | hpa
  · exact (Nat.lt_irrefl p) (hsmall p hp hpa)
  · obtain ⟨q, hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q-1)).mp hpa
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqp := hsmall q hqprime (Nat.dvd_of_mem_primeFactors hq)
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hqprime.one_lt) hpq
    omega

/-- Cancel a common largest prime from a nontrivial preimage.  Since the
prime does not divide the target totient, it occurs only once. -/
lemma ppt_remove_common_largest {d p a n : ℕ} (hp : p.Prime)
    (hcop : p.Coprime a) (hnot : ¬p ∣ d*a.totient)
    (hn : 0 < n) (hφ : n.totient = d*(p*a).totient)
    (hbad : ¬p*a ∣ n) (hpn : p ∣ n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p) :
    ∃ m : ℕ, 0 < m ∧ m.totient = d*a.totient ∧ ¬a ∣ m ∧
      (∀ q : ℕ, q.Prime → q ∣ m → q < p) ∧ n = p*m := by
  obtain ⟨m, rfl⟩ := hpn
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    simp only [hm0, mul_zero, lt_self_iff_false] at hn
  have htarget : (p*m).totient = (p-1)*(d*a.totient) := by
    rw [hφ, Nat.totient_mul hcop, Nat.totient_prime hp]
    ring
  have hpm : ¬p ∣ m := by
    intro hpm
    have hdiv : p ∣ (p*m).totient := by
      rw [Nat.totient_mul_of_prime_of_dvd hp hpm]
      exact dvd_mul_right _ _
    rw [htarget] at hdiv
    rcases hp.dvd_mul.mp hdiv with hprev | hrest
    · exact (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt)
        (Nat.sub_lt hp.pos (by decide))) hprev
    · exact hnot hrest
  have hφm : m.totient = d*a.totient := by
    rw [Nat.totient_mul (hp.coprime_iff_not_dvd.mpr hpm),
      Nat.totient_prime hp] at htarget
    exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.one_lt) htarget
  refine ⟨m, hm, hφm, ?_, ?_, rfl⟩
  · intro ham
    exact hbad (Nat.mul_dvd_mul_left p ham)
  · intro q hq hqm
    have hqp := hsmall q hq (hqm.trans (dvd_mul_left m p))
    exact lt_of_le_of_ne hqp (fun he => hpm (he ▸ hqm))

/-- The concrete suffix of a finite ordered candidate-prime list. -/
def pptSuffixProduct (p : ℕ → ℕ) (N j : ℕ) : ℕ :=
  ∏ i ∈ Finset.Ico j N, p i

lemma ppt_suffix_product_succ (p : ℕ → ℕ) {N j : ℕ} (hj : j < N) :
    pptSuffixProduct p N j = p j * pptSuffixProduct p N (j+1) := by
  exact Finset.prod_eq_prod_Ico_succ_bot hj p

lemma ppt_suffix_product_pos {p : ℕ → ℕ} {N j : ℕ}
    (hprime : ∀ i < N, (p i).Prime) : 0 < pptSuffixProduct p N j := by
  exact Finset.prod_pos (fun i hi => (hprime i (Finset.mem_Ico.mp hi).2).pos)

lemma ppt_suffix_prime_lt {p : ℕ → ℕ} {N j : ℕ}
    (hprime : ∀ i < N, (p i).Prime)
    (horder : ∀ i k : ℕ, i < k → k < N → p k < p i)
    {q : ℕ} (hq : q.Prime) (hdiv : q ∣ pptSuffixProduct p N (j+1)) :
    q < p j := by
  obtain ⟨i, hi, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have hi' := Finset.mem_Ico.mp hi
  have he : q = p i := (Nat.prime_dvd_prime_iff_eq hq (hprime i hi'.2)).mp hqi
  exact he ▸ horder j i (by omega) hi'.2

/-- A residual nontrivial preimage whose prime factors fit after the
already removed prefix.  At index zero there is no preceding bound. -/
def PPTPrefixWitness (d : ℕ) (p : ℕ → ℕ) (N j : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ n.totient = d*(pptSuffixProduct p N j).totient ∧
    ¬pptSuffixProduct p N j ∣ n ∧
    (j = 0 ∨ ∀ q : ℕ, q.Prime → q ∣ n → q < p (j-1))

private lemma ppt_largest_prime_data {p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (he : largestPrimeFactor n = p) :
    p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p := by
  have hsup : n.primeFactors.sup id = p := by
    rcases le_total 1 (n.primeFactors.sup id) with hh | hh
    · simpa only [largestPrimeFactor, max_eq_right hh] using he
    · have hp1 : p = 1 := by
        simpa only [largestPrimeFactor, max_eq_left hh] using he.symm
      exact False.elim (hp.ne_one hp1)
  have hnon : n.primeFactors.Nonempty := by
    by_contra hh
    have hempty : n.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    simp only [hempty, Finset.sup_empty, bot_eq_zero] at hsup
    exact hp.ne_zero hsup.symm
  obtain ⟨q, hq, hqsup⟩ := Finset.sup_mem_of_nonempty (f := id) hnon
  have hqp : q = p := hqsup.trans hsup
  refine ⟨hqp ▸ Nat.dvd_of_mem_primeFactors hq, ?_⟩
  intro q hq hqn
  have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩
  exact (Finset.le_sup (f := id) hmem).trans_eq hsup

/-- The last possible common prefix gives the precise largest-prime
mismatch used before Ford's injective bad-preimage association.  The
assumptions are only primeness, decreasing order, and primes above `d`. -/
theorem ppt_maximal_prefix_mismatch {d N : ℕ} (hd : 0 < d) (p : ℕ → ℕ)
    (hprime : ∀ i < N, (p i).Prime)
    (horder : ∀ i k : ℕ, i < k → k < N → p k < p i)
    (hlarge : ∀ i < N, d < p i)
    (hbad : ∃ n : ℕ, 0 < n ∧ n.totient = d*(pptSuffixProduct p N 0).totient ∧
      ¬pptSuffixProduct p N 0 ∣ n) :
    ∃ j < N, PPTPrefixWitness d p N j ∧
      ∀ n : ℕ, 0 < n → n.totient = d*(pptSuffixProduct p N j).totient →
        ¬pptSuffixProduct p N j ∣ n → largestPrimeFactor n ≠ p j := by
  classical
  let P : ℕ → Prop := PPTPrefixWitness d p N
  have hP0 : P 0 := by
    obtain ⟨n, hn, hφ, hnot⟩ := hbad
    exact ⟨n, hn, hφ, hnot, Or.inl rfl⟩
  have hPN : ¬P N := by
    rintro ⟨n, _, _, hnot, _⟩
    exact hnot (by simp [pptSuffixProduct])
  let j := Nat.findGreatest P N
  have hjle : j ≤ N := Nat.findGreatest_le N
  have hPj : P j := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hj : j < N := lt_of_le_of_ne hjle (fun he => hPN (he ▸ hPj))
  have hnext : ¬P (j+1) :=
    (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest P N = j from rfl)).2.2
      (Nat.lt_succ_self j) (by omega)
  refine ⟨j, hj, hPj, ?_⟩
  intro n hn hφ hnot he
  have hp := hprime j hj
  have htail : ∀ q : ℕ, q.Prime → q ∣ pptSuffixProduct p N (j+1) → q < p j :=
    fun q hq hqdiv => ppt_suffix_prime_lt hprime horder hq hqdiv
  have hcop : (p j).Coprime (pptSuffixProduct p N (j+1)) :=
    hp.coprime_iff_not_dvd.mpr (fun hh => (Nat.lt_irrefl _) (htail _ hp hh))
  have hnotval : ¬p j ∣ d*(pptSuffixProduct p N (j+1)).totient := by
    intro hh
    rcases hp.dvd_mul.mp hh with hpd | hpt
    · exact (Nat.not_dvd_of_pos_of_lt hd (hlarge j hj)) hpd
    · exact ppt_not_dvd_totient_of_prime_bound hp htail hpt
  have hdata := ppt_largest_prime_data hp hn he
  rw [ppt_suffix_product_succ p hj] at hφ hnot
  obtain ⟨u, hu, hφu, hnotu, hsmallu, _⟩ :=
    ppt_remove_common_largest hp hcop hnotval hn hφ hnot hdata.1 hdata.2
  apply hnext
  refine ⟨u, hu, hφu, hnotu, Or.inr ?_⟩
  simpa only [Nat.add_sub_cancel] using hsmallu

end TotientAsymptotic

end

end OAI
