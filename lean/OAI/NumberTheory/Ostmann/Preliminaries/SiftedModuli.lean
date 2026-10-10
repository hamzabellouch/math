import OAI.NumberTheory.Ostmann.Preliminaries.SiftedMertens

namespace OAI

open Erdos970

namespace Ostmann.SiftedWeights
open Finset

def sieveModuli (P : Finset ℕ) (Q : ℕ) : Finset ℕ :=
  (P.powerset.filter (fun t => (∏ p ∈ t, p) ≤ Q)).image (fun t => ∏ p ∈ t, p)

theorem prime_product_squarefree (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq)
  · intro p hp
    exact (ht p hp).squarefree

theorem prime_product_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (↑P.powerset : Set (Finset ℕ)) := by
  intro t ht s hs h
  have ht' : (∏ p ∈ t, p).primeFactors = t := Nat.primeFactors_prod
    (fun p hp => hP p ((mem_powerset.mp ht) hp))
  have hs' : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod
    (fun p hp => hP p ((mem_powerset.mp hs) hp))
  rw [← ht', ← hs']
  exact congrArg Nat.primeFactors h

theorem mem_sieveModuli {P : Finset ℕ} {Q q : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hq : q ∈ sieveModuli P Q) :
    0 < q ∧ q ≤ Q ∧ Squarefree q ∧ q.primeFactors ⊆ P := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ht, htQ⟩ := Finset.mem_filter.mp ht
  have hsub := mem_powerset.mp ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => hP p (hsub hp)
  refine ⟨Finset.prod_pos (fun p hp => (hprime p hp).pos), htQ,
    prime_product_squarefree t hprime, ?_⟩
  rwa [Nat.primeFactors_prod hprime]

theorem sum_sieveModuli (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : ℕ) (w : ℕ → ℝ) :
    (∑ q ∈ sieveModuli P Q, ∏ p ∈ q.primeFactors, w p) =
      ∑ t ∈ P.powerset with (∏ p ∈ t, p) ≤ Q, ∏ p ∈ t, w p := by
  rw [sieveModuli, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Nat.primeFactors_prod (fun p hp => hP p ((mem_powerset.mp (mem_filter.mp ht).1) hp))]
  · intro t ht s hs h
    exact prime_product_injective P hP (mem_filter.mp ht).1 (mem_filter.mp hs).1 h

theorem sieveModuli_weight_lower (j K : ℕ) (hjK : j ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ N Q : ℕ, max K 2 ≤ N → 1 < Q →
      (j : ℝ)*(Real.log (N : ℝ)+(Real.log 4+4)) ≤ Real.log (Q : ℝ)/2 →
      c*(Real.log (N : ℝ))^j ≤
        ∑ q ∈ sieveModuli (primeWindow K N) Q,
          ∏ p ∈ q.primeFactors, (j : ℝ)/((p : ℝ)-j) := by
  obtain ⟨c, hc, h⟩ := window_truncated_weight_lower j K hjK
  refine ⟨c, hc, ?_⟩
  intro N Q hN hQ hm
  rw [sum_sieveModuli (primeWindow K N) (fun p hp => (mem_primeWindow.mp hp).1)]
  exact h N Q hN hQ hm

end Ostmann.SiftedWeights

end OAI
