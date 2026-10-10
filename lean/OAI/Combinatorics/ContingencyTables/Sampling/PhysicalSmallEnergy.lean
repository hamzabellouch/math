import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalSmallGraph
import OAI.Combinatorics.ContingencyTables.Transport.FiniteSupportEnergy

namespace OAI

/-! # Exact energy on the positive physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration RowMajorEnumeration
open IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma fullEdges_vertices (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (p : SmallProfile (firstPaperSmall r c U)×SmallProfile (firstPaperSmall r c U))
    (hp : p ∈ fullEdges r c U L B hB) :
    p.1 ∈ vertices (firstPaperSmall r c U) B ∧ p.2 ∈ vertices (firstPaperSmall r c U) B := by
  have hd (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      naturalProfile z.val ∈ vertices (firstPaperSmall r c U) B :=
    (mem_vertices_iff _ B _).mpr ⟨naturalProfile_bounded z.val,Or.inr z.property.1⟩
  have ht (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      rawChoice (firstPaperSmall r c U) U (wordChoices _ U (repairWord r c U L B hB z)) ∈
        vertices (firstPaperSmall r c U) B :=
    (mem_vertices_iff _ B _).mpr ⟨rawChoice_bounded _ B U hB _,Or.inl (rawChoice_balanced _ B U hB _)⟩
  rcases Finset.mem_union.mp hp with hp|hp
  · exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hd z,ht z⟩
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨ht z,hd z⟩

lemma positive_vertex_is_physical (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (v : SmallProfile small)
    (hv : v ∈ vertices small B) (hp : 0 < hardMarginal small B r c L v) :
    ∃ z : PhysicalStates small B r c L,physicalProfile small B r c L z=v := by
  obtain ⟨hb,hpattern⟩ := (mem_vertices_iff small B v).mp hv
  let b : BoundedProfile small B := fun a => ⟨v a,Nat.lt_succ_of_le (hb a)⟩
  let p : Profiles small B := ⟨b,hpattern⟩
  exact ⟨⟨p,hp⟩,rfl⟩

/-- Deleting zero-weight vertices preserves the exact unnormalized energy,
not merely an inequality for a restricted class of observables. -/
theorem fullEnergy_physical_eq (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    fullEnergy r c U L B hB (physicalExtension _ B r c L H)=
      (∑ x,∑ y,if physicalAdjacent r c U L B hB x y then
        min (hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L x))
          (hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L y))*
          (H x-H y)^2 else 0)/2 := by
  have he := symmetricEnergy_restrict_observable (fullEdges r c U L B hB)
    (hardMarginal (firstPaperSmall r c U) B r c L) (physicalExtension _ B r c L H)
    (hardMarginal_nonnegative _ B r c L) (physicalProfile _ B r c L)
    (physicalProfile_injective _ B r c L) (by
      intro p hp
      have hv := fullEdges_vertices r c U L B hB p hp
      constructor
      · intro h
        exact positive_vertex_is_physical _ B r c L p.1 hv.1
          (lt_of_le_of_ne (hardMarginal_nonnegative _ B r c L p.1) (Ne.symm h))
      · intro h
        exact positive_vertex_is_physical _ B r c L p.2 hv.2
          (lt_of_le_of_ne (hardMarginal_nonnegative _ B r c L p.2) (Ne.symm h))) H (physicalExtension_at _ B r c L H)

  convert he using 1
  · rfl
  · apply congrArg (fun a : ℝ => a/2)
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    unfold physicalAdjacent
    split_ifs <;> rfl

end ContingencyTables.SmallGraphProfiles

end OAI
