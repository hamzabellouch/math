import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPhysicalVariance
import OAI.Combinatorics.ContingencyTables.Transport.RectangleCompletions

namespace OAI

/-! # Literal padded residual completions of each positive physical state -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def residualRows (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) (i : I) : ℕ :=
  r i-smallRow small (smallView small (physicalProfile small B r c L z) false) i+rowLargeCount small i*L

noncomputable def residualColumns (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) (j : J) : ℕ :=
  c j-smallColumn small B (smallView small (physicalProfile small B r c L z) true) j+columnLargeCount small j*L

lemma physical_weight_completions (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    hardMarginal small B r c L (physicalProfile small B r c L z)=
      (Fintype.card (LargeCompletion small (residualRows small B r c L z)
        (residualColumns small B r c L z)):ℝ) := by
  have h := hardMarginal_eq_completionCount small B r c L
    (physicalProfile small B r c L z) (naturalProfile_bounded z.val.val) hcap
  split_ifs at h with hres
  · exact h
  · have hp := z.property
    change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
    rw [h] at hp
    exact False.elim (lt_irrefl _ hp)

lemma physical_completions_nonempty (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    Nonempty (LargeCompletion small (residualRows small B r c L z)
      (residualColumns small B r c L z)) := by
  apply Fintype.card_pos_iff.mp
  have hp := z.property
  change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
  rw [physical_weight_completions small B r c L z hcap] at hp
  exact_mod_cast hp

lemma physical_residual_totals (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    (∑ i,residualRows small B r c L z i)=∑ j,residualColumns small B r c L z j := by
  obtain ⟨A⟩ := physical_completions_nonempty small B r c L z hcap
  calc
    _ = ∑ i,∑ j,A.val.val i j := by simp_rw [A.val.property.1]
    _ = ∑ j,∑ i,A.val.val i j := Finset.sum_comm
    _ = _ := by simp_rw [A.val.property.2]

/-- Rows outside the large-margin rectangle have zero residual, as
forced by the actual positive completion count. -/
lemma physical_residual_row_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (i : I) (hi : ¬U ≤ r i) :
    residualRows (firstPaperSmall r c U) B r c L z i=0 := by
  obtain ⟨A⟩ := physical_completions_nonempty _ B r c L z hcap
  rw [← A.val.property.1 i]
  apply Finset.sum_eq_zero
  intro j _
  apply A.property
  apply Bool.eq_true_of_ne_false
  intro hs
  exact hi ((firstPaperSmall_false_iff r c U i j).mp hs).1

lemma physical_residual_column_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (j : J) (hj : ¬U ≤ c j) :
    residualColumns (firstPaperSmall r c U) B r c L z j=0 := by
  obtain ⟨A⟩ := physical_completions_nonempty _ B r c L z hcap
  rw [← A.val.property.2 j]
  apply Finset.sum_eq_zero
  intro i _
  apply A.property
  apply Bool.eq_true_of_ne_false
  intro hs
  exact hj ((firstPaperSmall_false_iff r c U i j).mp hs).2

/-- Thus the marginal used by the variance proof is exactly the number
of ordinary tables on the large rectangle, including empty rectangles. -/
theorem physical_weight_rectangle (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L z)=
      (Fintype.card (Table
        (fun i : {i // U ≤ r i} => residualRows (firstPaperSmall r c U) B r c L z i.val)
        (fun j : {j // U ≤ c j} => residualColumns (firstPaperSmall r c U) B r c L z j.val)):ℝ) := by
  rw [physical_weight_completions _ B r c L z hcap]
  convert congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr (rectangleCompletionEquiv (firstPaperSmall r c U)
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (residualRows _ B r c L z) (residualColumns _ B r c L z)
    (physical_residual_row_zero r c U L B z hcap)
    (physical_residual_column_zero r c U L B z hcap))) using 1
  all_goals
    congr 3
    all_goals exact Subsingleton.elim _ _

end ContingencyTables.SmallGraphProfiles

end OAI
