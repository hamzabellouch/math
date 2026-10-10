import OAI.NumberTheory.TotientAsymptotic.PrimeFactorBands
import OAI.NumberTheory.TotientFibers.FiniteFiber
import Mathlib.Data.Fin.Rev

namespace OAI

/-!
The actual low/high factorization of a chosen preimage in the PPT
construction.  Large square factors have already been excluded; the high
factor therefore has a strictly decreasing prime list.  No conclusion
about a mismatch with a second prime list is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_partAbove_eq_partBetween (n : ℕ) (S : ℝ) :
    partAbove n S = partBetween n S n := by
  unfold partAbove partBetween
  congr 1
  apply List.filter_congr
  intro p hp
  have hpn : (p : ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_mem_primeFactorsList hp)
  simp only [hpn, and_true]

lemma ppt_partAbove_pos (n : ℕ) (S : ℝ) : 0 < partAbove n S := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_pos n S n

lemma ppt_partAbove_dvd {n : ℕ} (hn : 0 < n) (S : ℝ) : partAbove n S ∣ n := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_dvd hn.ne' S n

lemma ppt_partAbove_prime_gt {n p : ℕ} {S : ℝ}
    (hp : p.Prime) (hpn : p ∣ partAbove n S) : S < (p : ℝ) := by
  have hm := (Nat.mem_primeFactorsList_iff_dvd (ppt_partAbove_pos n S).ne' hp).mpr hpn
  rw [ppt_partAbove_eq_partBetween] at hm
  have hf := (partBetween_factors n S n).mem_iff.mpr hm
  exact (of_decide_eq_true (List.mem_filter.mp hf).2).1

lemma ppt_partBelow_prime_le {n p : ℕ} {S : ℝ}
    (hp : p.Prime) (hpn : p ∣ partBelow n S) : (p : ℝ) ≤ S := by
  have hm := (Nat.mem_primeFactorsList_iff_dvd (partBelow_pos n S).ne' hp).mpr hpn
  have hf := (partBelow_factors n S).mem_iff.mpr hm
  exact of_decide_eq_true (List.mem_filter.mp hf).2

lemma ppt_low_high_coprime (n : ℕ) (S : ℝ) :
    (partBelow n S).Coprime (partAbove n S) := by
  apply Nat.coprime_of_dvd'
  intro p hp hlo hhi
  exact False.elim ((not_lt_of_ge (ppt_partBelow_prime_le hp hlo))
    (ppt_partAbove_prime_gt hp hhi))

lemma ppt_low_totient_smooth (n : ℕ) {S : ℝ} (hS : 1 ≤ S) :
    (largestPrimeFactor (partBelow n S).totient : ℝ) ≤ S := by
  have hl : largestPrimeFactor (partBelow n S) ≤ ⌊S⌋₊ := by
    apply largestPrimeFactor_le_of_prime_divisors
      (Nat.le_floor (by simpa only [Nat.cast_one] using hS))
    intro p hp hpn _
    exact Nat.le_floor (ppt_partBelow_prime_le hp hpn)
  exact (Nat.cast_le.mpr ((largestPrimeFactor_totient_le _).trans hl)).trans
    (Nat.floor_le (zero_le_one.trans hS))

lemma ppt_high_squarefree {n : ℕ} (hn : 0 < n) {S : ℝ}
    (hsq : SquarefreeAbove n S) : Squarefree (partAbove n S) := by
  rw [ppt_partAbove_eq_partBetween]
  exact partBetween_squarefree hn.ne' hsq

/-- The residual low totient and the ordered high primes give the exact
equation used for unequal-list alignment. Normality is inherited from the
actual preimage, and all high primes are strictly above the cutoff. -/
theorem ppt_preimage_prime_split_full {n : ℕ} {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p) :
    ∃ (h : ℕ) (p : Fin h → ℕ) (s : ℕ),
      0 < s ∧ n = s*∏ i, p i ∧ s.Coprime (∏ i, p i) ∧
      (largestPrimeFactor s.totient : ℝ) ≤ S ∧ StrictAnti p ∧
      (∀ i, IsNormalPrime S (p i) ∧ S < (p i : ℝ)) ∧
      n.totient = s.totient*shiftedProduct p ∧ s = partBelow n S := by
  classical
  let Q := (partAbove n S).primeFactors
  let e : Fin Q.card ↪o ℕ := Q.orderEmbOfFin rfl
  let p : Fin Q.card → ℕ := fun i => e i.rev
  have hpQ (i : Fin Q.card) : p i ∈ Q := Q.orderEmbOfFin_mem rfl i.rev
  have hpinj : Function.Injective p := e.injective.comp Fin.rev_injective
  have hanti : StrictAnti p := by
    intro i j hij
    exact e.strictMono (Fin.rev_lt_rev.mpr hij)
  have himage : Finset.univ.image p = Q := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact hpQ i
    · intro hr
      have hr' : r ∈ Finset.univ.image e := by
        change r ∈ Finset.univ.image (Q.orderEmbOfFin rfl)
        rwa [Q.image_orderEmbOfFin_univ rfl]
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr'
      obtain ⟨j, hj⟩ := Fin.rev_surjective i
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simpa only [p, hj] using hi⟩
  have hprodQ : (∏ i, p i) = ∏ r ∈ Q, r := by
    conv_rhs => rw [← himage, Finset.prod_image (fun i _ j _ he => hpinj he)]
  have hshiftQ : shiftedProduct p = ∏ r ∈ Q, (r-1) := by
    unfold shiftedProduct
    conv_rhs => rw [← himage, Finset.prod_image (fun i _ j _ he => hpinj he)]
  have hprod : (∏ i, p i) = partAbove n S :=
    hprodQ.trans (Nat.prod_primeFactors_of_squarefree (ppt_high_squarefree hn hsq))
  have hQprime : ∀ r ∈ Q, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hφ : (∏ i, p i).totient = shiftedProduct p := by
    rw [hprodQ, hshiftQ]
    exact TotientFibers.totient_prime_prod hQprime
  have hfactor : n = partBelow n S*∏ i, p i := by
    rw [hprod]
    exact (partBelow_mul_partAbove hn.ne' S).symm
  have hcop : (partBelow n S).Coprime (∏ i, p i) := by
    rw [hprod]
    exact ppt_low_high_coprime n S
  refine ⟨Q.card, p, partBelow n S, partBelow_pos n S, hfactor, hcop,
    ppt_low_totient_smooth n hS, hanti, ?_, ?_, rfl⟩
  · intro i
    have hi := Nat.dvd_of_mem_primeFactors (hpQ i)
    have hip := hQprime (p i) (hpQ i)
    exact ⟨hnormal (p i) hip (hi.trans (ppt_partAbove_dvd hn S)),
      ppt_partAbove_prime_gt hip hi⟩
  · calc
      n.totient = (partBelow n S*∏ i, p i).totient := congrArg Nat.totient hfactor
      _ = (partBelow n S).totient*(∏ i, p i).totient := Nat.totient_mul hcop
      _ = _ := by rw [hφ]

/-- Decomposition of a totient preimage for normality alignment. -/
theorem ppt_preimage_prime_split {n : ℕ} {S : ℝ} (hn : 0 < n) (hS : 1 ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime S p) :
    ∃ (h : ℕ) (p : Fin h → ℕ) (s : ℕ),
      0 < s ∧ n = s*∏ i, p i ∧ s.Coprime (∏ i, p i) ∧
      (largestPrimeFactor s.totient : ℝ) ≤ S ∧ StrictAnti p ∧
      (∀ i, IsNormalPrime S (p i) ∧ S < (p i : ℝ)) ∧
      n.totient = s.totient*shiftedProduct p := by
  obtain ⟨h, p, s, hs, hn, hc, hsmall, hanti, hp, hφ, _⟩ :=
    ppt_preimage_prime_split_full hn hS hsq hnormal
  exact ⟨h, p, s, hs, hn, hc, hsmall, hanti, hp, hφ⟩

end TotientAsymptotic

end

end OAI
