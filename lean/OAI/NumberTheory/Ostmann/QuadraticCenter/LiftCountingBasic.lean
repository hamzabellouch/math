import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeIncidence

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def boundedSubsetLifts (U : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (H : ℕ) : Finset ℤ :=
  (Finset.Icc (-(H : ℤ)) H).filter (fun n => ∀ p ∈ U, (p : ℤ) ∣ n - a * t p)

@[simp] theorem mem_boundedSubsetLifts {U : Finset ℕ} {a n : ℤ}
    {t : ℕ → ℤ} {H : ℕ} :
    n ∈ boundedSubsetLifts U a t H ↔
      -(H : ℤ) ≤ n ∧ n ≤ H ∧ ∀ p ∈ U, (p : ℤ) ∣ n - a * t p := by
  simp [boundedSubsetLifts, and_assoc]

theorem matchingPrimes_powersetCard (P : Finset ℕ) (a n : ℤ)
    (t : ℕ → ℤ) (k : ℕ) :
    (matchingPrimes P a n t).powersetCard k =
      (P.powersetCard k).filter (fun U : Finset ℕ => ∀ p ∈ U, (p : ℤ) ∣ n - a * t p) := by
  classical
  ext U
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hc⟩
    refine ⟨⟨fun p hp => (mem_matchingPrimes.mp (hU hp)).1, hc⟩, ?_⟩
    exact fun p hp => (mem_matchingPrimes.mp (hU hp)).2
  · rintro ⟨⟨hU, hc⟩, hd⟩
    exact ⟨fun p hp => mem_matchingPrimes.mpr ⟨hU hp, hd p hp⟩, hc⟩

theorem sum_matching_choose_eq_sum_lifts (P : Finset ℕ) (a : ℤ)
    (t : ℕ → ℤ) (H k : ℕ) :
    (∑ n ∈ Finset.Icc (-(H : ℤ)) H, Nat.choose (matchingPrimes P a n t).card k) =
      ∑ U ∈ P.powersetCard k, (boundedSubsetLifts U a t H).card := by
  classical
  simp_rw [← Finset.card_powersetCard, matchingPrimes_powersetCard,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [boundedSubsetLifts, Finset.sum_filter]

theorem sum_matching_descFactorial_eq (P : Finset ℕ) (a : ℤ)
    (t : ℕ → ℤ) (H k : ℕ) :
    (∑ n ∈ Finset.Icc (-(H : ℤ)) H, (matchingPrimes P a n t).card.descFactorial k) =
      k.factorial * ∑ U ∈ P.powersetCard k, (boundedSubsetLifts U a t H).card := by
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose]
  rw [← Finset.mul_sum, sum_matching_choose_eq_sum_lifts]

theorem lifted_subsets_le_matching_moments (P : Finset ℕ) (E : Finset (Finset ℕ))
    (a : ℤ) (t : ℕ → ℤ) (H k : ℕ)
    (hE : E ⊆ P.powersetCard k)
    (hlift : ∀ U ∈ E, (boundedSubsetLifts U a t H).Nonempty) :
    k.factorial * E.card ≤
      ∑ n ∈ Finset.Icc (-(H : ℤ)) H, (matchingPrimes P a n t).card.descFactorial k := by
  rw [sum_matching_descFactorial_eq]
  apply Nat.mul_le_mul_left
  calc
    E.card = ∑ U ∈ E, 1 := by simp
    _ ≤ ∑ U ∈ E, (boundedSubsetLifts U a t H).card := by
      apply Finset.sum_le_sum
      intro U hU
      exact (hlift U hU).card_pos
    _ ≤ _ := Finset.sum_le_sum_of_subset hE

theorem boundedSubsetLifts_prod_dvd_sub {U : Finset ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p) {a n m : ℤ} {t : ℕ → ℤ} {H : ℕ}
    (hn : n ∈ boundedSubsetLifts U a t H) (hm : m ∈ boundedSubsetLifts U a t H) :
    (∏ p ∈ U, p) ∣ (n - m).natAbs := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hU p hp) (hU q hq)).mpr hpq)
  · intro p hp
    have hd := dvd_sub ((mem_boundedSubsetLifts.mp hn).2.2 p hp)
      ((mem_boundedSubsetLifts.mp hm).2.2 p hp)
    rw [sub_sub_sub_cancel_right] at hd
    exact Int.natCast_dvd.mp hd

end Ostmann.QuadraticCenter

end

end OAI
