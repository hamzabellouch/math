import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic

namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def retainedPrimeDivisors (S : Finset ℕ) : Finset ℕ :=
  S.powerset.image (fun U => ∏ p ∈ U, p)

lemma primeSubset_product_injective (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) S.powerset := by
  intro U hU V hV heq
  have hU' : U ⊆ S := mem_powerset.mp hU
  have hV' : V ⊆ S := mem_powerset.mp hV
  have hprimeU : ∀ p ∈ U, Nat.Prime p := fun p hp => hS p (hU' hp)
  have hprimeV : ∀ p ∈ V, Nat.Prime p := fun p hp => hS p (hV' hp)
  have hfactors := congrArg Nat.primeFactors heq
  simpa only [Nat.primeFactors_prod hprimeU, Nat.primeFactors_prod hprimeV] using hfactors

lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)

lemma retainedPrimeDivisor_factors (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : u.primeFactors ⊆ S := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  have hUS : U ⊆ S := mem_powerset.mp hU
  rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp))]
  exact hUS

lemma retainedPrimeDivisor_card_factors (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : u.primeFactors.card ≤ S.card :=
  card_le_card (retainedPrimeDivisor_factors S hS hu)

theorem retainedPrimeDivisors_weighted_mass (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (w : ℕ → ℝ) :
    (∑ u ∈ retainedPrimeDivisors S, (∏ p ∈ u.primeFactors, w p) / (u : ℝ)) =
      ∏ p ∈ S, (1 + w p / (p : ℝ)) := by
  unfold retainedPrimeDivisors
  rw [sum_image (primeSubset_product_injective S hS)]
  calc
    _ = ∑ U ∈ S.powerset, ∏ p ∈ U, (w p / (p : ℝ)) := by
      apply sum_congr rfl
      intro U hU
      have hUS : U ⊆ S := mem_powerset.mp hU
      rw [Nat.primeFactors_prod (fun p hp => hS p (hUS hp)), Nat.cast_prod,
        prod_div_distrib]
    _ = _ := (prod_one_add S).symm

end TwoPointCorrelations

end OAI
