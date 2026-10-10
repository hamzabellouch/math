import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportMatched
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryBulkReferenceTests HistoryPairBulkTransport HistoryPairKernelReplacement
open HistoryBulkFibreGiantApproximation HistoryPairSourceLaws HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}

private theorem resampledSlot_self (q : SmallSlot) : resampledSlot q q.value=q := by
  cases q
  rfl

private theorem root_bulk_source (h : History l)
    (hh : Template.Matches (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) h.root.small)
    (i : Fin h.root.small.length) (hi : (h.root.small.get i).role=.bulk) :
    C.sources (h.root.small.get i).origin=C.bulk := by
  obtain ⟨j,rfl⟩ := (matchedRootPosition hh).surjective i
  have hr := matchedRootPosition_role hh j
  have ho := congrArg SourceSlot.origin (matches_get_source hh j)
  change (h.root.small.get (matchedRootPosition hh j)).origin = _ at ho
  rw [ho]
  exact current_bulk_source (bulkSize depth L/2) depth l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card)
    ⟨j,hr.symm.trans hi⟩

private theorem orderedSource_positive (x : Frame.Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0)
    (u : Fin (2^l)×Fin (2*(bulkSize depth L/2))) :
    PositiveSourceValue C.bulk
      (orderedIntegerSourceValues C.sources (2*(bulkSize depth L/2)) depth l x u) := by
  let i := (currentBulkPositionEquiv (2*(bulkSize depth L/2)) depth l).symm u
  have hs : C.sources ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l)[i.val].origin)=C.bulk :=
    current_bulk_source (bulkSize depth L/2) depth l C.bulk
      (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) i
  rw [←hs]
  exact ⟨x i.val,rfl,assignmentPrior_component_mass_ne_zero C.sources _ x hx i.val⟩

theorem fixedB_sourceSamples (r : Frame (l:=l) C outside)
    (x : Frame.Source (C:=C) (l:=l))
    (hx : (assignmentPrior C.sources _).mass x≠0) :
    SmallSourceSamples C.sources r.left r.right (r.fixedB x) := by
  classical
  have hhl := root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat r.leftSource r.leftChoices)
  have hkr := root_matches (assignedLabels C.sources _ _ l r.t r.P.toNat r.Q.toNat r.rightSource r.rightChoices)
  have hl : ∀q∈r.left.root.small,sourceMass C.sources q≠0 := by
    simpa only [Frame.left,assignedHistory,decodeHistory_root,assignedRoot] using
      assignedSlots_source_mass_ne_zero C.sources _ r.leftSource r.left_mass
  have hr : ∀q∈r.right.root.small,sourceMass C.sources q≠0 := by
    simpa only [Frame.right,assignedHistory,decodeHistory_root,assignedRoot] using
      assignedSlots_source_mass_ne_zero C.sources _ r.rightSource r.right_mass
  have hil := decoded_internalSlot_mass C.sources _ _ l
    (assignedRoot C.sources _ r.s r.P.toNat r.Q.toNat r.leftSource)
    r.leftChoices r.left_choices_mass
  have hir := decoded_internalSlot_mass C.sources _ _ l
    (assignedRoot C.sources _ r.t r.P.toNat r.Q.toNat r.rightSource)
    r.rightChoices r.right_choices_mass
  constructor
  · intro i
    rcases i with i | i
    · by_cases hb : leftMap r.left r.right (.inr (.inl i)) ∈ bulkCoordinates r.left r.right
      · have hrole : (r.left.root.small.get i).role=.bulk := by
          by_contra hn
          exact left_nonbulk_not_mem r.left r.right r.left_supported i hn hb
        unfold Frame.fixedB integerInsertOrderedGiants
        rw [dite_eq_right (left_small_not_mem r.left r.right (.inl i)),dite_eq_left hb]
        apply PositiveSourceValue.sourceMass
        change PositiveSourceValue (C.sources (r.left.root.small.get i).origin) _
        rw [root_bulk_source r.left hhl i hrole]
        exact orderedSource_positive x hx _
      · refine ⟨(r.left.root.small.get i).value,?_,?_⟩
        · simp only [Frame.fixedB,integerInsertOrderedGiants,
            dite_eq_right (left_small_not_mem r.left r.right (.inl i)),dite_eq_right hb,
            leftMap_sample,integerSample]
        · simpa only [smallSlotAt,Sum.elim_inl,resampledSlot] using hl _ (List.get_mem _ i)
    · refine ⟨(internalSlot r.left i).value,?_,?_⟩
      · exact fixedB_representative r x (label r.left r.right (.inl i))
      · change sourceMass C.sources (resampledSlot (internalSlot r.left i) (internalSlot r.left i).value)≠0
        rw [resampledSlot_self]
        exact hil i
  · intro i
    rcases i with i | i
    · by_cases hb : rightMap r.left r.right (.inr (.inl i)) ∈ bulkCoordinates r.left r.right
      · have hrole : (r.right.root.small.get i).role=.bulk := by
          by_contra hn
          exact right_nonbulk_not_mem r.left r.right r.left_supported r.matching i hn hb
        unfold Frame.fixedB integerInsertOrderedGiants
        rw [dite_eq_right (right_small_not_mem r.left r.right (.inl i)),dite_eq_left hb]
        apply PositiveSourceValue.sourceMass
        change PositiveSourceValue (C.sources (r.right.root.small.get i).origin) _
        rw [root_bulk_source r.right hkr i hrole]
        exact orderedSource_positive x hx _
      · refine ⟨(r.right.root.small.get i).value,?_,?_⟩
        · simp only [Frame.fixedB,integerInsertOrderedGiants,
            dite_eq_right (right_small_not_mem r.left r.right (.inl i)),dite_eq_right hb]
          rfl
        · simpa only [smallSlotAt,Sum.elim_inl,resampledSlot] using hr _ (List.get_mem _ i)
    · refine ⟨(internalSlot r.right i).value,?_,?_⟩
      · exact fixedB_representative r x (label r.left r.right (.inr i))
      · change sourceMass C.sources (resampledSlot (internalSlot r.right i) (internalSlot r.right i).value)≠0
        rw [resampledSlot_self]
        exact hir i

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
