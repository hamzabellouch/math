import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalGraphDegree
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPhysicalVariance

namespace OAI

/-! # The finite graph on positive-weight physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open CompletionCounts SmallContextEnumeration IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma fullEdges_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : SmallProfile (firstPaperSmall r c U)) :
    (x,y) ∈ fullEdges r c U L B hB ↔ (y,x) ∈ fullEdges r c U L B hB := by
  suffices hs : ∀ x y,(x,y) ∈ fullEdges r c U L B hB → (y,x) ∈ fullEdges r c U L B hB from
    ⟨hs x y,hs y x⟩
  intro x y he
  rcases Finset.mem_union.mp he with he|he
  · apply Finset.mem_union_left
    obtain ⟨hp,D,i,j,hij,hi,hj,hx,hy⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr (Finset.mem_product.mp hp).symm,
      D,j,i,hij.symm,hj,hi,hy,hx⟩
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp he with he|he
    · apply Finset.mem_union_right
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨z,hz,Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)⟩
    · apply Finset.mem_union_left
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨z,hz,Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)⟩

noncomputable def physicalAdjacent (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L) : Prop :=
  (physicalProfile _ B r c L x,physicalProfile _ B r c L y) ∈ fullEdges r c U L B hB

lemma physicalAdjacent_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L) :
    physicalAdjacent r c U L B hB x y ↔ physicalAdjacent r c U L B hB y x :=
  fullEdges_symmetric r c U L B hB _ _

lemma physicalAdjacent_degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (Finset.univ.filter (physicalAdjacent r c U L B hB x)).card ≤
      5*(Fintype.card (Cells (firstPaperSmall r c U)))^2+1 := by
  let p := physicalProfile (firstPaperSmall r c U) B r c L
  have hsub : (Finset.univ.filter (physicalAdjacent r c U L B hB x)).image p ⊆
      fullNeighbors r c U L B hB (p x) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(p x,p z),Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).2,rfl⟩,rfl⟩
  calc
    _ = ((Finset.univ.filter (physicalAdjacent r c U L B hB x)).image p).card :=
      (Finset.card_image_of_injective _ (physicalProfile_injective _ B r c L)).symm
    _ ≤ (fullNeighbors r c U L B hB (p x)).card := Finset.card_le_card hsub
    _ ≤ _ := fullNeighbors_card_le r c U L B hB (p x)

lemma physicalAdjacent_degree_allowance (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (Finset.univ.filter (physicalAdjacent r c U L B hB x)).card ≤
      5*(dimensionAllowance (I := I) (J := J))^2+1 := by
  have hc : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I := I) (J := J) := by
    calc
      _ ≤ Fintype.card (I×J) := Fintype.card_subtype_le _
      _ = Fintype.card I*Fintype.card J := Fintype.card_prod _ _
      _ ≤ _ := dimension_le_allowance
  exact (physicalAdjacent_degree r c U L B hB x).trans (by gcongr)

end ContingencyTables.SmallGraphProfiles

end OAI
