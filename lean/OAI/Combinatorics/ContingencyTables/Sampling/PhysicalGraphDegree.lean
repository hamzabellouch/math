import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRepairGraph
import OAI.Combinatorics.ContingencyTables.Transport.FiniteExchangeDegree
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRepairDegree

namespace OAI

/-! # The manuscript's finite neighbor bound on the physical small graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open CompletionCounts SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def fullNeighbors (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :=
  ((fullEdges r c U L B hB).filter (fun p => p.1=v)).image Prod.snd

lemma fullNeighbors_subset (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :
    fullNeighbors r c U L B hB v ⊆ exchangeCandidates v ∪
      repairNeighbors
        (fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val)
        (fun z => rawChoice (firstPaperSmall r c U) U
          (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))) v := by
  intro y hy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨he,hv⟩ := Finset.mem_filter.mp hp
  rcases Finset.mem_union.mp he with he|he
  · apply Finset.mem_union_left
    have ha := (Finset.mem_filter.mp he).2
    rw [hv] at ha
    exact adjacent_mem_candidates ha
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp he
      subst p
      exact mem_repairNeighbors_forward _ _ v z hv
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp he
      subst p
      exact mem_repairNeighbors_reverse _ _ v z hv

/-- Counting distinct neighbors, with repeated exchange/repair edges
removed by the finite-set union, gives exactly the source bound. -/
theorem fullNeighbors_card_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :
    (fullNeighbors r c U L B hB v).card ≤ 5*(Fintype.card (Cells (firstPaperSmall r c U)))^2+1 := by
  let x := fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val
  let y := fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    rawChoice (firstPaperSmall r c U) U (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  have hx : Function.Injective x := by
    intro a b he
    apply Subtype.ext
    exact naturalProfile_injective _ B he
  have hy : Function.Injective (fun z => (defectLabels _ B r c L z,y z)) := by
    intro a b he
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only at hl hr
    have hw : repairWord r c U L B hB a=repairWord r c U L B hB b :=
      (wordChoices (firstPaperSmall r c U) U).injective
        (rawChoice_injective (firstPaperSmall r c U) U hr)
    exact repairWord_type_injective r c U L B hB (Prod.ext hl hw)
  have hr := repairNeighbors_card_le x y hx (defectLabels _ B r c L) hy v
  have hc := exchangeCandidates_card_le v
  have hs := (Finset.card_le_card (fullNeighbors_subset r c U L B hB v)).trans (Finset.card_union_le _ _)
  change (fullNeighbors r c U L B hB v).card ≤ (exchangeCandidates v).card+(repairNeighbors x y v).card at hs
  have hcoord : Fintype.card (LargePairEnumeration.SmallView (fun a : I×J => firstPaperSmall r c U a.1 a.2))=
      2*Fintype.card (Cells (firstPaperSmall r c U)) := by
    change Fintype.card (Cells (firstPaperSmall r c U)×Bool)=_
    rw [Fintype.card_prod,Fintype.card_bool]
    omega
  rw [Fintype.card_prod] at hr
  change (repairNeighbors x y v).card ≤ _ at hr
  rw [hcoord] at hc
  nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
