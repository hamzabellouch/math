import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace OAI

/-! Elementary symmetric sums for the six-entry cubic classification. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def elementarySum (v : (Fin 6) → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin 6)).powersetCard k, ∏ i ∈ s, v i

theorem unit_product_complement (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (s : Finset (Fin 6)) :
    (∏ i, v i) * conj (∏ i ∈ s, v i) = ∏ i ∈ sᶜ, v i := by
  rw [← Finset.prod_mul_prod_compl s v, map_prod]
  calc
    ((∏ i ∈ s, v i) * ∏ i ∈ sᶜ, v i) * ∏ i ∈ s, conj (v i) =
        (∏ i ∈ sᶜ, v i) * ∏ i ∈ s, (v i * conj (v i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∏ i ∈ sᶜ, v i := by simp [Complex.mul_conj, hv]

theorem elementarySum_reciprocal (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (k : ℕ) (hk : k ≤ 6) :
    (∏ i, v i) * conj (elementarySum v k) = elementarySum v (6 - k) := by
  unfold elementarySum
  rw [map_sum, Finset.mul_sum]
  simp_rw [unit_product_complement v hv]
  refine Finset.sum_bij (fun s _ => sᶜ) ?_ ?_ ?_ ?_
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    simp [Finset.mem_powersetCard, Finset.card_compl, hc]
  · intro s _hs t _ht h
    simpa using congrArg (fun u : Finset (Fin 6) => uᶜ) h
  · intro t ht
    refine ⟨tᶜ, ?_, by simp⟩
    have hc := (Finset.mem_powersetCard.mp ht).2
    have hsub : 6 - (6 - k) = k := by omega
    simp [Finset.mem_powersetCard, Finset.card_compl, hc, hsub]
  · intro _subset _membership
    rfl

theorem elementarySum_zero (v : (Fin 6) → ℂ) : elementarySum v 0 = 1 := by
  simp [elementarySum]

theorem elementarySum_six (v : (Fin 6) → ℂ) : elementarySum v 6 = ∏ i, v i := by
  have h : (Finset.univ : Finset (Fin 6)).powersetCard 6 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 6))
  simp [elementarySum, h]

theorem elementarySum_one (v : (Fin 6) → ℂ) : elementarySum v 1 = ∑ i, v i := by
  simp [elementarySum, Finset.powersetCard_one]

private theorem coordinate_pairs :
    (Finset.univ : Finset (Fin 6)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
       {1, 2}, {1, 3}, {1, 4}, {1, 5},
       {2, 3}, {2, 4}, {2, 5}, {3, 4}, {3, 5}, {4, 5}} := by
  decide

/-- Newton's identity at degree two, specialized to exactly six entries. -/
theorem elementarySum_two_identity (v : (Fin 6) → ℂ) :
    (∑ i, v i) ^ 2 = (∑ i, v i ^ 2) + 2 * elementarySum v 2 := by
  simp (disch := decide) [elementarySum, coordinate_pairs, Fin.sum_univ_succ]
  ring

theorem elementarySum_one_two_zero (v : (Fin 6) → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 1 = 0 ∧ elementarySum v 2 = 0 := by
  refine ⟨by simpa [elementarySum_one] using h1, ?_⟩
  have h := elementarySum_two_identity v
  rw [h1, h2] at h
  linear_combination -h / 2

theorem elementarySum_four_five_zero (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 4 = 0 ∧ elementarySum v 5 = 0 := by
  obtain ⟨h1', h2'⟩ := elementarySum_one_two_zero v h1 h2
  constructor
  · simpa [h2'] using (elementarySum_reciprocal v hv 2 (by decide)).symm
  · simpa [h1'] using (elementarySum_reciprocal v hv 1 (by decide)).symm

end MUB6

end

end OAI
