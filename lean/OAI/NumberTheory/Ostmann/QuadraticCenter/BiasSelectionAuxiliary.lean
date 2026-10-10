import Mathlib.NumberTheory.Primorial
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionBalanced
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionNatural

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries Filter
open scoped BigOperators

def BalancedResiduePrime (d : Decomposition) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, letI : NeZero p := ⟨hp.ne_zero⟩
    1 / 3 ≤ d.residueDensity p ∧ d.residueDensity p ≤ 2 / 3

lemma balancedResiduePrime_prime {d : Decomposition} {p : ℕ}
    (h : BalancedResiduePrime d p) : p.Prime := h.choose

theorem eventually_balanced_dyadic_prime_block (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ (P : Finset (PrimeUpTo (collisionScale 4 X))) (N : ℕ),
      (∀ p ∈ P, p.val ≤ N) →
      ∃ (j : ℕ) (G : Finset ℕ), j ≤ Nat.log 2 N ∧ G ⊆ P.image Subtype.val ∧
        (∀ p ∈ G, BalancedResiduePrime d p ∧ 2 ^ j ≤ p ∧ p < 2 * 2 ^ j) ∧
        (boundedPrimeWeight P - 3 * collisionConstant 4 * Real.log (Real.log (X : ℝ))) *
          (2 ^ j : ℕ) ≤
          (Nat.log 2 N + 1 : ℕ) * Real.log (2 * (2 ^ j : ℕ)) * G.card := by
  classical
  filter_upwards [eventually_balanced_prime_weight d] with X hX
  intro P N hN
  let B := balancedBoundedPrimes d (collisionScale 4 X) P
  let S := B.image Subtype.val
  have hS : S ⊆ P.image Subtype.val := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩
  have hbalance : ∀ p ∈ S, BalancedResiduePrime d p := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨primeUpTo_prime p, (Finset.mem_filter.mp hp).2⟩
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => balancedResiduePrime_prime (hbalance p hp)
  have hNS : ∀ p ∈ S, p ≤ N := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hS hp)
    exact hN q hq
  obtain ⟨j, hj, hcard⟩ := exists_weighted_dyadic_prime_block S N hprime hNS
  refine ⟨j, dyadicPrimeBlock S j, hj, (dyadicPrimeBlock_subset S j).trans hS, ?_, ?_⟩
  · intro p hp
    have hs := dyadicPrimeBlock_subset S j hp
    exact ⟨hbalance p hs, dyadicPrimeBlock_bounds hp (hprime p hs).pos⟩
  · have hw : boundedPrimeWeight P -
        3 * collisionConstant 4 * Real.log (Real.log (X : ℝ)) ≤ primeWeight S := by
      have h := hX P
      rw [show primeWeight S = boundedPrimeWeight B from primeWeight_image_val B]
      linarith
    exact (mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ (2 ^ j : ℕ))).trans hcard

theorem exists_balanced_prime_subproduct (d : Decomposition) (P : Finset ℕ)
    (hP : ∀ p ∈ P, BalancedResiduePrime d p) (K U Z : ℕ)
    (hK : K ≤ P.card) (hU : ∀ p ∈ P, p ≤ U) (hUZ : U < Z) :
    ∃ F : Finset ℕ, F ⊆ P ∧ F.card = K ∧
      Squarefree (∏ p ∈ F, p) ∧ (∏ p ∈ F, p) ≤ U ^ K ∧
      (∀ p ∈ F, BalancedResiduePrime d p) ∧
      (∀ q : ℕ, Z ≤ q → q ∉ F) := by
  classical
  obtain ⟨F, hF, hcard⟩ := Finset.exists_subset_card_eq hK
  have hp : ∀ p ∈ F, p.Prime := fun p hm => balancedResiduePrime_prime (hP p (hF hm))
  refine ⟨F, hF, hcard, ?_, ?_, fun p hm => hP p (hF hm), ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp' q hq' hpq => ?_)
      (fun p hp' => (hp p hp').squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hp p hp') (hp q hq')).mpr hpq
  · have h := Finset.prod_le_pow_card F (fun p : ℕ => p) U (fun p hp => hU p (hF hp))
    simpa only [hcard] using h
  · intro q hq hqF
    exact (not_le_of_gt (lt_of_le_of_lt (hU q (hF hqF)) hUZ)) hq

end Ostmann.QuadraticCenter

end

end OAI
