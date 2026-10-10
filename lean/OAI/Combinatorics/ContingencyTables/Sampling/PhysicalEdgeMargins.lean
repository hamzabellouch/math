import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRepairMargins
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalSmallGraph

namespace OAI

/-! # Every actual small-graph edge changes each residual margin by at most two -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres SmallContextCoordinates
open SmallContextEnumeration RowMajorEnumeration

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma designated_repair_residual_margins (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L)
    (hsource : naturalProfile z.val=physicalProfile _ B r c L x)
    (htarget : rawChoice (firstPaperSmall r c U) U
      (wordChoices _ U (repairWord r c U L B hB z))=physicalProfile _ B r c L y) :
    (∀ i,|(residualRows (firstPaperSmall r c U) B r c L y i:ℤ)-residualRows _ B r c L x i| ≤ 1) ∧
    (∀ j,|(residualColumns (firstPaperSmall r c U) B r c L y j:ℤ)-residualColumns _ B r c L x j| ≤ 1) := by
  let st := defectLabels (firstPaperSmall r c U) B r c L z
  have hd := defectLabels_spec (firstPaperSmall r c U) B r c L z
  have hcap := repair_small_capacity r c U L B hB (naturalProfile z.val)
    (naturalProfile_bounded z.val) st.1.val st.2.val st.1.property st.2.property hd z.property.2
  have he := htarget.symm.trans (repairWord_profile r c U L B hB z)
  rw [hsource] at hd hcap he
  exact repair_residual_margins _ B r c L x y hxcap hycap st.1.val st.2.val hd st.2.property hcap he

theorem physical_edge_residual_margins (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L,∀ i j,
      firstPaperSmall r c U i j=false → (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    (∀ i,|(residualRows (firstPaperSmall r c U) B r c L y i:ℤ)-residualRows _ B r c L x i| ≤ 2) ∧
    (∀ j,|(residualColumns (firstPaperSmall r c U) B r c L y j:ℤ)-residualColumns _ B r c L x j| ≤ 2) := by
  rcases Finset.mem_union.mp hxy with he|he
  · exact exchange_residual_margins _ B r c L x y (hcap x) (hcap y) (Finset.mem_filter.mp he).2
  · rcases Finset.mem_union.mp he with he|he
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp he
      have hm := designated_repair_residual_margins r c U L B hB x y (hcap x) (hcap y) z
        (congrArg Prod.fst he) (congrArg Prod.snd he)
      exact ⟨fun i => (hm.1 i).trans (by norm_num),fun j => (hm.2 j).trans (by norm_num)⟩
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp he
      have hm := designated_repair_residual_margins r c U L B hB y x (hcap y) (hcap x) z
        (congrArg Prod.snd he) (congrArg Prod.fst he)
      constructor
      · intro i
        rw [abs_sub_comm]
        exact (hm.1 i).trans (by norm_num)
      · intro j
        rw [abs_sub_comm]
        exact (hm.2 j).trans (by norm_num)

end ContingencyTables.SmallGraphProfiles

end OAI
