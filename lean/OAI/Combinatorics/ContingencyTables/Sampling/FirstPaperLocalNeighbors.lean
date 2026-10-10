import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFeasibility
import OAI.Combinatorics.ContingencyTables.Transport.IntegerExchangeArithmetic
import OAI.Combinatorics.ContingencyTables.Sampling.SmallDefectLabels
import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairCandidates

namespace OAI

/-! # Arithmetic enumeration of the first-paper chain's neighbors

The list is obtained from ordered coordinate and cell pairs, then filtered
by arithmetic edge and feasibility tests. It never enumerates all states.
-/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open PhysicalCompletionFibres SmallContextFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts SmallContextCoordinates SmallContextEnumeration
open RowMajorEnumeration IntegerWeightedTransport

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => d^20
local notation "L" => d^12
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c
local notation "profile" => physicalProfile small B r c L

/-- A directed repair is identified by its two defect cells. -/
def ArithmeticRepair (v w : SmallProfile small) : Prop :=
  ∃ st : Cells small×Cells small,
    IsDefect (smallView small v false) (smallQ small B v) st.1.val st.2.val ∧
      w=repairedProfile small B v st.1.val st.2.val

/-- All predicates are bounded integer-coordinate tests. -/
def ArithmeticEdge (v w : SmallProfile small) : Prop :=
  (∃ i j,i≠j ∧ 0<v j ∧ w=exchangeTarget v i j) ∨
    ArithmeticRepair r c v w ∨ ArithmeticRepair r c w v

lemma arithmeticRepair_iff (x y : PaperStates r c) :
    ArithmeticRepair r c (profile x) (profile y) ↔
      ∃ z : PositiveDefects small B r c L,
        naturalProfile z.val=profile x ∧
        rawChoice small U (wordChoices small U
          (repairWord r c U L B (stateCapacity_small r c) z))=profile y := by
  constructor
  · rintro ⟨st,hd,hy⟩
    let z : PositiveDefects small B r c L :=
      ⟨x.val.val,⟨st.1.val,st.2.val,st.1.property,st.2.property,hd⟩,x.property⟩
    refine ⟨z,rfl,?_⟩
    rw [repairWord_profile]
    have hl : defectLabels small B r c L z=st := defectLabels_eq_of_spec small B r c L z st hd
    rw [hl]
    exact hy.symm
  · rintro ⟨z,hx,hy⟩
    refine ⟨defectLabels small B r c L z,?_,?_⟩
    · rw [←hx]
      exact defectLabels_spec small B r c L z
    · rw [←hy,repairWord_profile,hx]

/-- On actual states the arithmetic test is exactly the graph relation
used in the Poincare and mixing proofs. -/
theorem arithmeticEdge_iff (x y : PaperStates r c) :
    ArithmeticEdge r c (profile x) (profile y) ↔
      physicalAdjacent r c U L B (stateCapacity_small r c) x y := by
  have hx : profile x ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded x.val.val,x.val.property⟩
  have hy : profile y ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded y.val.val,y.val.property⟩
  rw [ArithmeticEdge,←adjacent_iff_arithmetic,arithmeticRepair_iff,arithmeticRepair_iff]
  change _ ↔ (profile x,profile y) ∈ physicalEdges small B ∪
    repairEdges r c U L B (stateCapacity_small r c)
  simp only [Finset.mem_union,physicalEdges,Finset.mem_filter,Finset.mem_product,
    hx,hy,true_and,repairEdges,Finset.mem_image,Finset.mem_univ,Prod.mk.injEq]
  constructor
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)

def localCandidates (v : SmallProfile small) : Finset (SmallProfile small) :=
  exchangeCandidates v ∪ localRepairCandidates small B v

lemma localCandidates_card (v : SmallProfile small) :
    (localCandidates r c v).card ≤ 6*(Fintype.card (Cells small))^2 := by
  have he := exchangeCandidates_card_le v
  have hr := localRepairCandidates_card small B v
  have hs := Finset.card_union_le (exchangeCandidates v) (localRepairCandidates small B v)
  have hcoord : Fintype.card (LargePairEnumeration.SmallView (fun a : I×J => small a.1 a.2))=
      2*Fintype.card (Cells small) := by
    change Fintype.card (Cells small×Bool)=_
    rw [Fintype.card_prod,Fintype.card_bool]
    omega
  rw [hcoord] at he
  change (localCandidates r c v).card ≤ _ at hs
  nlinarith

/-- Passing candidates are decoded with the arithmetic feasibility test. -/
def localNeighborList (x : PaperStates r c) : List (PaperStates r c) :=
  ((localCandidates r c (profile x)).toList.filter
    (fun w => ArithmeticEdge r c (profile x) w)).filterMap (decodeProfile r c)

lemma localNeighborList_nodup (x : PaperStates r c) :
    (localNeighborList r c x).Nodup := by
  apply List.Nodup.filterMap
  · intro a b y ha hb
    have hya := (decodeProfile_eq_some_iff r c a y).mp ha
    have hyb := (decodeProfile_eq_some_iff r c b y).mp hb
    exact hya.symm.trans hyb
  · exact (Finset.nodup_toList _).filter _

theorem mem_localNeighborList (x y : PaperStates r c) :
    y ∈ localNeighborList r c x ↔
      physicalAdjacent r c U L B (stateCapacity_small r c) x y := by
  simp only [localNeighborList,List.mem_filterMap,List.mem_filter,Finset.mem_toList,
    decide_eq_true_eq]
  constructor
  · rintro ⟨w,⟨_,he⟩,hy⟩
    have hw := (decodeProfile_eq_some_iff r c w y).mp hy
    rw [←hw] at he
    exact (arithmeticEdge_iff r c x y).mp he
  · intro he
    refine ⟨profile y,⟨?_,(arithmeticEdge_iff r c x y).mpr he⟩,?_⟩
    · apply fullNeighbors_local r c U L B (stateCapacity_small r c) (profile x)
      exact Finset.mem_image.mpr ⟨(profile x,profile y),Finset.mem_filter.mpr ⟨he,rfl⟩,rfl⟩
    · exact (decodeProfile_eq_some_iff r c _ y).mpr rfl

theorem localNeighborList_length (x : PaperStates r c) :
    (localNeighborList r c x).length ≤ 6*d^2 := by
  have h := (List.length_filterMap_le (decodeProfile r c)
    ((localCandidates r c (profile x)).toList.filter
      (fun w => ArithmeticEdge r c (profile x) w))).trans
        (List.length_filter_le _ _)
  rw [Finset.length_toList] at h
  have hc : Fintype.card (Cells small) ≤ d :=
    (Fintype.card_subtype_le _).trans ((Fintype.card_prod I J).le.trans dimension_le_allowance)
  exact h.trans ((localCandidates_card r c _).trans (by gcongr))

end
end ContingencyTables.SmallGraphProfiles

end OAI
