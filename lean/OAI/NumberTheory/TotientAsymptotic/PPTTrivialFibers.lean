import OAI.NumberTheory.TotientAsymptotic.PublishedFiber

namespace OAI

/-!
The elementary part of Ford's full-fiber construction, *The distribution of
totients*, Section 5, p. 25, immediately after (5.18).  Its candidates have
every prime divisor larger than the fixed seed plus one.  Their target
preimages which contain the candidate are exactly its multiples by seed
preimages.  Thus the sieve only has to exclude preimages which do not
contain the candidate.

This reduction does not prove the abundance of candidates, or the bound on
the candidates with a nontrivial preimage.
-/

namespace TotientAsymptotic

open scoped BigOperators

/-- Every prime divisor of an inverse image of `d` is at most `d+1`. -/
lemma prime_le_seed_add_one {d m p : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hp : p.Prime) (hpm : p ∣ m) : p ≤ d+1 := by
  have hdiv : p-1 ∣ d := by
    simpa only [Nat.totient_prime hp, hm] using Nat.totient_dvd_of_dvd hpm
  have hle := Nat.le_of_dvd hd hdiv
  have hp1 := hp.one_lt
  omega

/-- A candidate supported on primes above `d+1` is coprime to every seed
preimage, independently of the number or exponents of its prime factors. -/
lemma seed_preimage_coprime {d b m : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) : b.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpb hpm
  exact (not_lt_of_ge (prime_le_seed_add_one hd hm hp hpm)) (hrough p hp hpb)

lemma seed_multiple_totient {d b m : ℕ} (hd : 0 < d) (hm : m.totient = d)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) :
    (b*m).totient = d*b.totient := by
  rw [Nat.totient_mul (seed_preimage_coprime hd hm hrough), hm, Nat.mul_comm]

/-- A repeated candidate prime in the residual factor would make the
totient at least that prime times the candidate totient, exceeding the
fixed multiplier `d`. -/
lemma target_multiple_coprime {d b m : ℕ} (hb : 0 < b) (hm : 0 < m)
    (heq : (b*m).totient = d*b.totient)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) : b.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpb hpm
  have hdiv : p*b ∣ b*m := by
    obtain ⟨q, hq⟩ := hpm
    refine ⟨q, ?_⟩
    rw [hq]
    ring
  have hφb := Nat.totient_pos.mpr hb
  have hφtarget : 0 < (b*m).totient := Nat.totient_pos.mpr (Nat.mul_pos hb hm)
  have hle := Nat.le_of_dvd hφtarget (Nat.totient_dvd_of_dvd hdiv)
  rw [Nat.totient_mul_of_prime_of_dvd hp hpb, heq] at hle
  have hpd : p ≤ d := Nat.le_of_mul_le_mul_right hle hφb
  have hlarge := hrough p hp hpb
  omega

/-- Every target preimage divisible by the candidate has exactly a seed
preimage as its residual factor. -/
lemma target_preimage_of_dvd {d b n : ℕ} (hb : 0 < b) (hn : 0 < n)
    (heq : n.totient = d*b.totient) (hbn : b ∣ n)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) :
    ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m := by
  obtain ⟨m, rfl⟩ := hbn
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    simp [hm0] at hn
  have hcop := target_multiple_coprime hb hm heq hrough
  have hφb := Nat.totient_pos.mpr hb
  refine ⟨m, hm, ?_, rfl⟩
  rw [Nat.totient_mul hcop, Nat.mul_comm d] at heq
  exact Nat.eq_of_mul_eq_mul_left hφb heq

/-- For Ford's rough candidates, full-fiber preservation is equivalent to
excluding target preimages which are not divisible by the candidate. -/
theorem fullFiber_iff_all_preimages_dvd {d b : ℕ} (hd : 0 < d) (hb : 0 < b)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p) :
    FullFiber d b ↔ ∀ n : ℕ, 0 < n → n.totient = d*b.totient → b ∣ n := by
  constructor
  · intro hfull n hn heq
    obtain ⟨m, _, _, rfl⟩ := (hfull n).mp ⟨hn, heq⟩
    exact dvd_mul_right b m
  · intro hdiv n
    constructor
    · rintro ⟨hn, heq⟩
      exact target_preimage_of_dvd hb hn heq (hdiv n hn heq) hrough
    · rintro ⟨m, hm, hφm, rfl⟩
      exact ⟨Nat.mul_pos hb hm, seed_multiple_totient hd hφm hrough⟩

/-- The roughness hypothesis is inherited by a finite product of primes. -/
lemma primeProduct_rough {ι : Type*} (I : Finset ι) (p : ι → ℕ) (d : ℕ)
    (hp : ∀ i ∈ I, (p i).Prime) (hlarge : ∀ i ∈ I, d+1 < p i) :
    ∀ q : ℕ, q.Prime → q ∣ ∏ i ∈ I, p i → d+1 < q := by
  intro q hq hdiv
  obtain ⟨i, hi, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have heq : q = p i := (Nat.prime_dvd_prime_iff_eq hq (hp i hi)).mp hqi
  simpa only [heq] using hlarge i hi

theorem primeProduct_fullFiber_iff {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    {d : ℕ} (hd : 0 < d) (hp : ∀ i ∈ I, (p i).Prime)
    (hlarge : ∀ i ∈ I, d+1 < p i) :
    FullFiber d (∏ i ∈ I, p i) ↔
      ∀ n : ℕ, 0 < n → n.totient = d*(∏ i ∈ I, p i).totient →
        (∏ i ∈ I, p i) ∣ n :=
  fullFiber_iff_all_preimages_dvd hd (Finset.prod_pos (fun i hi => (hp i hi).pos))
    (primeProduct_rough I p d hp hlarge)

end TotientAsymptotic

end OAI
