import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionActual
import OAI.NumberTheory.Ostmann.QuadraticCenter.DyadicSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

lemma primeWeight_image_val {Q : ℕ} (P : Finset (PrimeUpTo Q)) :
    primeWeight (P.image Subtype.val) = boundedPrimeWeight P := by
  classical
  unfold primeWeight boundedPrimeWeight
  rw [Finset.sum_image]
  intro a ha b hb he
  exact Subtype.ext he

theorem eventually_oriented_bias_natural (d : Decomposition) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ P : Finset (PrimeUpTo (collisionScale 4 X)),
      ∃ G : Finset ℕ, G ⊆ P.image Subtype.val ∧ ∃ ε t : ℕ → ℤ,
        (∀ p ∈ G, p.Prime ∧ p ≠ 2 ∧ (ε p = 1 ∨ ε p = -1) ∧
          δ / 4 ≤ (∑ a ∈ positiveIntegerWindow d.A X,
            ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) /
              (positiveIntegerWindow d.A X).card ∧
          (∑ a ∈ negativeIntegerWindow d.B X,
            ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) /
              (negativeIntegerWindow d.B X).card ≤ -δ / 4) ∧
        boundedPrimeWeight (quadraticBiasedPrimes d (collisionScale 4 X) δ P) ≤
          primeWeight G + biasSelectionCost δ * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_oriented_biased_subset d hδ] with X hX
  intro P
  obtain ⟨G₀, hG₀, ε₀, t₀, hmeans, hweight⟩ := hX P
  let Q := collisionScale 4 X
  let ε : ℕ → ℤ := fun n => if hn : n ∈ Q.primesLE then ε₀ ⟨n, hn⟩ else 1
  let t : ℕ → ℤ := fun n => if hn : n ∈ Q.primesLE then t₀ ⟨n, hn⟩ else 0
  have hε (p : PrimeUpTo Q) : ε p.val = ε₀ p := by simp [ε, p.property]
  have ht (p : PrimeUpTo Q) : t p.val = t₀ p := by simp [t, p.property]
  refine ⟨G₀.image Subtype.val, ?_, ε, t, ?_, ?_⟩
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp (hG₀ hp)).1, rfl⟩
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hodd := (Finset.mem_filter.mp (hG₀ hp)).2.1
    refine ⟨primeUpTo_prime p, hodd, ?_⟩
    simpa only [hε p, ht p] using hmeans p hp
  · rw [primeWeight_image_val]
    exact hweight

theorem eventually_biased_dyadic_prime_block (d : Decomposition) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ (P : Finset (PrimeUpTo (collisionScale 4 X))) (N : ℕ),
      (∀ p ∈ P, p.val ≤ N) →
      ∃ (j : ℕ) (G : Finset ℕ) (ε t : ℕ → ℤ),
        j ≤ Nat.log 2 N ∧ G ⊆ P.image Subtype.val ∧
        (∀ p ∈ G, p.Prime ∧ p ≠ 2 ∧ 2 ^ j ≤ p ∧ p < 2 * 2 ^ j ∧
          (ε p = 1 ∨ ε p = -1) ∧
          δ / 4 ≤ (∑ a ∈ positiveIntegerWindow d.A X,
            ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) /
              (positiveIntegerWindow d.A X).card ∧
          (∑ a ∈ negativeIntegerWindow d.B X,
            ((ε p * jacobiSym (a - t p) p : ℤ) : ℝ)) /
              (negativeIntegerWindow d.B X).card ≤ -δ / 4) ∧
        (boundedPrimeWeight (quadraticBiasedPrimes d (collisionScale 4 X) δ P) -
          biasSelectionCost δ * Real.log (Real.log (X : ℝ))) * (2 ^ j : ℕ) ≤
          (Nat.log 2 N + 1 : ℕ) * Real.log (2 * (2 ^ j : ℕ)) * G.card := by
  classical
  filter_upwards [eventually_oriented_bias_natural d hδ] with X hX
  intro P N hN
  obtain ⟨S, hS, ε, t, hmeans, hweight⟩ := hX P
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hmeans p hp).1
  have hNS : ∀ p ∈ S, p ≤ N := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hS hp)
    exact hN q hq
  obtain ⟨j, hj, hcard⟩ := exists_weighted_dyadic_prime_block S N hprime hNS
  refine ⟨j, dyadicPrimeBlock S j, ε, t, hj,
    (dyadicPrimeBlock_subset S j).trans hS, ?_, ?_⟩
  · intro p hp
    have hsp := dyadicPrimeBlock_subset S j hp
    have hm := hmeans p hsp
    have hb := dyadicPrimeBlock_bounds hp hm.1.pos
    exact ⟨hm.1, hm.2.1, hb.1, hb.2, hm.2.2⟩
  · have hw : boundedPrimeWeight (quadraticBiasedPrimes d (collisionScale 4 X) δ P) -
        biasSelectionCost δ * Real.log (Real.log (X : ℝ)) ≤ primeWeight S := by linarith
    exact (mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ (2 ^ j : ℕ))).trans hcard

end Ostmann.QuadraticCenter

end

end OAI
