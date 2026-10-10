import OAI.NumberTheory.Ostmann.QuadraticCenter.Incidence

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def matchingPrimes (P : Finset ℕ) (a n : ℤ) (t : ℕ → ℤ) : Finset ℕ :=
  P.filter (fun p => (p : ℤ) ∣ n - a * t p)

@[simp] theorem mem_matchingPrimes {P : Finset ℕ} {a n : ℤ} {t : ℕ → ℤ} {p : ℕ} :
    p ∈ matchingPrimes P a n t ↔ p ∈ P ∧ (p : ℤ) ∣ n - a * t p := by
  simp [matchingPrimes]

theorem matchingPrimes_inter_dvd {P : Finset ℕ} {a n m : ℤ} {t : ℕ → ℤ}
    {p : ℕ} (hp : p ∈ matchingPrimes P a n t ∩ matchingPrimes P a m t) :
    p ∣ (n - m).natAbs := by
  rcases Finset.mem_inter.mp hp with ⟨hn, hm⟩
  have hd := dvd_sub (mem_matchingPrimes.mp hn).2 (mem_matchingPrimes.mp hm).2
  rw [sub_sub_sub_cancel_right] at hd
  exact Int.natCast_dvd.mp hd

theorem matchingPrimes_inter_prod_dvd {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (a n m : ℤ) (t : ℕ → ℤ) :
    (∏ p ∈ matchingPrimes P a n t ∩ matchingPrimes P a m t, p) ∣
      (n - m).natAbs := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hpP := (mem_matchingPrimes.mp (Finset.mem_inter.mp hp).1).1
    have hqP := (mem_matchingPrimes.mp (Finset.mem_inter.mp hq).1).1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hpP) (hP q hqP)).mpr hpq)
  · intro p hp
    exact matchingPrimes_inter_dvd hp

theorem matchingPrimes_inter_card_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (a n m : ℤ) (t : ℕ → ℤ)
    {Z k : ℕ} (hZ : 1 ≤ Z) (hlarge : ∀ p ∈ P, Z ≤ p) (hne : n ≠ m)
    (hbound : (n - m).natAbs < Z ^ (k + 1)) :
    (matchingPrimes P a n t ∩ matchingPrimes P a m t).card ≤ k := by
  let S := matchingPrimes P a n t ∩ matchingPrimes P a m t
  have hprod : Z ^ S.card ≤ ∏ p ∈ S, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    intro p hp
    exact hlarge p (mem_matchingPrimes.mp (Finset.mem_inter.mp hp).1).1
  have hd : (∏ p ∈ S, p) ∣ (n - m).natAbs :=
    matchingPrimes_inter_prod_dvd hP a n m t
  have hpos : 0 < (n - m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hsmall : Z ^ S.card < Z ^ (k + 1) :=
    (hprod.trans (Nat.le_of_dvd hpos hd)).trans_lt hbound
  by_contra hh
  have hc : k + 1 ≤ S.card := by dsimp [S]; omega
  exact (not_le_of_gt hsmall) (Nat.pow_le_pow_right hZ hc)

def primeMatchingRow (P : Finset ℕ) (a n : ℤ) (t : ℕ → ℤ) : Finset P :=
  (matchingPrimes P a n t).subtype (fun p => p ∈ P)

@[simp] theorem card_primeMatchingRow (P : Finset ℕ) (a n : ℤ) (t : ℕ → ℤ) :
    (primeMatchingRow P a n t).card = (matchingPrimes P a n t).card := by
  rw [primeMatchingRow, Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun p hp => (mem_matchingPrimes.mp hp).1)

@[simp] theorem card_primeMatchingRow_inter (P : Finset ℕ) (a n m : ℤ)
    (t : ℕ → ℤ) :
    (primeMatchingRow P a n t ∩ primeMatchingRow P a m t).card =
      (matchingPrimes P a n t ∩ matchingPrimes P a m t).card := by
  have he : primeMatchingRow P a n t ∩ primeMatchingRow P a m t =
      (matchingPrimes P a n t ∩ matchingPrimes P a m t).subtype (fun p => p ∈ P) := by
    ext p
    simp [primeMatchingRow]
  rw [he, Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr
    (fun p hp => (mem_matchingPrimes.mp (Finset.mem_inter.mp hp).1).1)

theorem common_integer_lift_from_moments {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (a : ℤ) (t : ℕ → ℤ)
    (lift : ι → ℤ) (hinj : Function.Injective lift)
    (n lo cutoff k mass Z : ℕ) (hZ : 1 ≤ Z) (hlarge : ∀ p ∈ P, Z ≤ p)
    (hlo : lo ≤ n + 1) (hpos : 0 < mass)
    (hmoment : mass + cutoff ^ (n + 1 - lo) *
        ∑ i, (matchingPrimes P a (lift i) t).card.descFactorial lo ≤
        ∑ i, (matchingPrimes P a (lift i) t).card.descFactorial (n + 1))
    (hbound : ∀ i j, i ≠ j → (lift i - lift j).natAbs < Z ^ (k + 1))
    (hgap : 2 * k * P.card ≤ cutoff ^ 2) :
    ∃ i, cutoff ≤ (matchingPrimes P a (lift i) t).card ∧
      (mass : ℝ) ≤ 2 * (P.card : ℝ) *
        ((matchingPrimes P a (lift i) t).card : ℝ) ^ n := by
  have h := common_center_from_moments
    (fun i => primeMatchingRow P a (lift i) t) n lo cutoff k mass hlo hpos
    (by simpa only [card_primeMatchingRow] using hmoment)
    (fun i j hij => by
      rw [card_primeMatchingRow_inter]
      exact matchingPrimes_inter_card_le hP a (lift i) (lift j) t hZ hlarge
        (fun he => hij (hinj he)) (hbound i j hij))
    (by simpa using hgap)
  simpa only [card_primeMatchingRow, Fintype.card_coe] using h

end Ostmann.QuadraticCenter

end OAI
