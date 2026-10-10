import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductTail

namespace OAI

/-! # Cutoff tails for the squarefree divisor expansion -/
namespace JointDickman
open Finset

noncomputable def primeSubsetTail (P : Finset ℕ) (Y N : ℝ) : ℝ := by
  classical
  exact ∑ D ∈ P.powerset.filter
    (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N),
      1/(∏ p ∈ D, (p:ℝ))

theorem primeSubsetTail_degree_le (P : Finset ℕ) (h : ℕ) (Y N : ℝ) :
    (∑ D ∈ P.powersetCard h,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0) ≤ reciprocalPrimeTupleTail P h Y N := by
  classical
  rw [sum_powersetCard_eq_ordered_tuples,reciprocalPrimeTupleTail,sum_filter]
  calc
    _ = ∑ v ∈ orderedPrimeTuples P h,
        if Y < (∏ i, (v i:ℝ)) ∧ (∏ i, (v i:ℝ)) ≤ N
        then 1/(∏ i, (v i:ℝ)) else 0 := by
      apply sum_congr rfl
      intro v hv
      rw [ordered_tuple_prod (orderedPrimeTuples_mem.mp hv).2]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by
      intro v _ _
      split_ifs <;> positivity)

theorem primeSubsetTail_sum_degree (P : Finset ℕ) (J : ℕ) (Y N : ℝ)
    (hcard : ∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) :
    primeSubsetTail P Y N = ∑ h ∈ range (J+1), ∑ D ∈ P.powersetCard h,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0 := by
  classical
  let T := P.powerset.filter
    (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N)
  have hf := sum_fiberwise_of_maps_to (g := Finset.card) (s := T)
    (t := range (J+1)) (fun D hD => mem_range.mpr (Nat.lt_succ_of_le
      (hcard D (mem_filter.mp hD).1 (mem_filter.mp hD).2.2)))
    (fun D : Finset ℕ => 1/(∏ p ∈ D, (p:ℝ)))
  change (∑ D ∈ T, 1/(∏ p ∈ D, (p:ℝ))) = _
  rw [← hf]
  apply sum_congr rfl
  intro h _
  have he : T.filter (fun D : Finset ℕ => D.card = h) = (P.powersetCard h).filter
      (fun D : Finset ℕ => Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N) := by
    ext D
    simp only [T,mem_filter,mem_powersetCard,mem_powerset]
    tauto
  rw [he,sum_filter]

/-- Only finitely many degrees occur when every prime exceeds a fixed
positive power of the cutoff. No distinctness estimate is needed here. -/
theorem primeSubsetTail_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (J : ℕ) (y Y N : ℝ), 2 ≤ y → 1 ≤ Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ)) →
      (∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) →
      primeSubsetTail P Y N ≤ ((Real.log (N/Y)+C)/Real.log y)*
        ∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h := by
  classical
  obtain ⟨C,hC,hbound⟩ := reciprocalPrimeTupleTail_bound
  refine ⟨C,hC,?_⟩
  intro P J y Y N hy hY hYN hP hcard
  rw [primeSubsetTail_sum_degree P J Y N hcard,sum_range_succ']
  have hz : (∑ D ∈ P.powersetCard 0,
      if Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N
      then 1/(∏ p ∈ D, (p:ℝ)) else 0) = 0 := by
    simp [not_lt_of_ge hY]
  rw [hz,add_zero,mul_sum]
  apply sum_le_sum
  intro h _
  exact (primeSubsetTail_degree_le P (h+1) Y N).trans
    (hbound P h y Y N hy (by linarith) hYN hP)

end JointDickman

end OAI
