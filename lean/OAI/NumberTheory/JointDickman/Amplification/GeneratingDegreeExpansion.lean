import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeSubsets

namespace OAI

/-! # Splitting the generating model into ordered prime degrees -/
namespace JointDickman
open Finset

noncomputable def primeGeneratingDegree (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) : ℝ := by
  classical
  exact ∑ D ∈ P.powersetCard h,
    if (∏ p ∈ D, p) ≤ N then (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ) else 0

theorem primeGeneratingModel_sum_degree (P : Finset ℕ) (z : ℕ → ℝ) (N J : ℕ)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    primeGeneratingModel P z N = ∑ h ∈ range (J+1), primeGeneratingDegree P z N h := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card) (s := boundedPrimeSubsets P N)
    (t := range (J+1)) (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (hcard D hD)))
    (fun D => (∏ p ∈ D, (z p-1))/(∏ p ∈ D, p : ℕ))
  rw [primeGeneratingModel, ← hf]
  apply sum_congr rfl
  intro h hh
  have he : (boundedPrimeSubsets P N).filter (fun D => D.card = h) =
      (P.powersetCard h).filter (fun D => (∏ p ∈ D, p) ≤ N) := by
    ext D
    simp only [boundedPrimeSubsets, mem_filter, mem_powersetCard, mem_powerset]
    tauto
  rw [he, sum_filter]
  rfl

open Classical in
theorem primeGeneratingDegree_ordered (P : Finset ℕ) (z : ℕ → ℝ) (N h : ℕ) :
    primeGeneratingDegree P z N h = ∑ v ∈ orderedPrimeTuples P h,
      if (∏ i, v i) ≤ N then (∏ i, (z (v i)-1))/(∏ i, v i : ℕ) else 0 := by
  classical
  rw [primeGeneratingDegree, sum_powersetCard_eq_ordered_tuples]
  apply sum_congr rfl
  intro v hv
  have hm := (orderedPrimeTuples_mem.mp hv).2
  have hp : (∏ p ∈ univ.image v, p : ℕ) = ∏ i, v i := prod_image hm.injective.injOn
  rw [hp, ordered_tuple_prod hm]

@[simp] theorem primeGeneratingDegree_zero (P : Finset ℕ) (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    primeGeneratingDegree P z N 0 = 1 := by
  classical
  simp [primeGeneratingDegree, hN.ne']

end JointDickman

end OAI
