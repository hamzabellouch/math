import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterMoments
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterReduction

namespace OAI

/-! # Common-center extraction for the actual congruence matching sets -/

namespace Ostmann

open scoped BigOperators

def matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) : Finset P :=
  Finset.univ.filter fun p => (p.1 : ℤ) ∣ n - a * t p.1

theorem image_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) :
    (matchingPrimeSubtype P a t n).image Subtype.val = matchingPrimes P a t n := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨q.2, (Finset.mem_filter.mp hq).2⟩
  · intro hp
    obtain ⟨hP, hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨⟨p, hP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩

theorem card_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n : ℤ) :
    (matchingPrimeSubtype P a t n).card = (matchingPrimes P a t n).card := by
  rw [← image_matchingPrimeSubtype]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem card_inter_matchingPrimeSubtype (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (n m : ℤ) :
    (matchingPrimeSubtype P a t n ∩ matchingPrimeSubtype P a t m).card =
      (matchingPrimes P a t n ∩ matchingPrimes P a t m).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.image_inter _ _ Subtype.val_injective,
    image_matchingPrimeSubtype, image_matchingPrimeSubtype]

/-- The finite form of `quad-common-centre-size` and `quad-common-centre`.
The only moment assumptions are the explicit counts of integer lifts. -/
theorem exists_commonCenter_of_lift_moments (P : Finset ℕ) (N : Finset ℤ)
    (a : ℕ) (ha : 0 < a) (t : ℕ → ℤ) (k d K : ℕ) (hd : d ≤ k + 1)
    (A B L V : ℝ) (hA : 0 < A) (hV : 0 < V)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p)
    (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hspan : ∀ n ∈ N, ∀ m ∈ N, n ≠ m →
      Real.log ((n - m).natAbs : ℝ) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (hlo : (∑ n : N, ((matchingPrimes P a t n.1).card.descFactorial (k + 1 - d) : ℝ)) ≤ B)
    (hhi : L ≤ ∑ n : N, ((matchingPrimes P a t n.1).card.descFactorial (k + 1) : ℝ))
    (hpositive : 0 < L - A ^ d * B) :
    ∃ n ∈ N, ∃ h : ℤ, ∃ m : ℕ,
      0 < m ∧ m ≤ a ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
      A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
      L - A ^ d * B ≤ 2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
      ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
        let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
        (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  classical
  have hinter (n m : N) (hne : n ≠ m) :
      ((matchingPrimeSubtype P a t n.1 ∩ matchingPrimeSubtype P a t m.1).card : ℝ) ≤ K := by
    rw [card_inter_matchingPrimeSubtype]
    exact_mod_cast matchingPrimes_inter_card_le P a t n.1 m.1
      (fun h => hne (Subtype.ext h)) K V hV hprime hlog (hspan n n.2 m m.2 (fun h => hne (Subtype.ext h)))
  have hlo' : (∑ n : N, ((matchingPrimeSubtype P a t n.1).card.descFactorial (k + 1 - d) : ℝ)) ≤ B := by
    simpa only [card_matchingPrimeSubtype] using hlo
  have hhi' : L ≤ ∑ n : N, ((matchingPrimeSubtype P a t n.1).card.descFactorial (k + 1) : ℝ) := by
    simpa only [card_matchingPrimeSubtype] using hhi
  obtain ⟨n, hnsize, hnlarge⟩ := exists_commonCenter_from_factorial_moments
    (fun n : N => matchingPrimeSubtype P a t n.1) k d hd A K B L hA (Nat.cast_nonneg _)
    hinter (by simpa only [Fintype.card_coe] using hsmall) hlo' hhi' hpositive
  rw [card_matchingPrimeSubtype] at hnsize hnlarge
  obtain ⟨h, m, hm, hma, hred, hbound, heq⟩ := exists_reduced_commonCenter n.1 a ha
  refine ⟨n.1, n.2, h, m, hm, hma, hred, hbound, hnsize, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hnlarge
  · intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    let : Fact p.Prime := ⟨hprime p hpP⟩
    exact reduced_commonCenter_mod_prime n.1 h a m p ha (hap p hpP) hm hma heq (t p)
      (Finset.mem_filter.mp hp).2

end Ostmann

end OAI
