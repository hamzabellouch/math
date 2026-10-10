import OAI.Combinatorics.BalancedRyser.Candidates.CandidateBasics
import OAI.Combinatorics.BalancedRyser.Incidence.AffinePlaneInstance
import OAI.Combinatorics.BalancedRyser.Selection.Selection

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev AvailableCandidate (M : MergedPairs F) :=
  {v : CandidateVertex F // v ∈ candidateVertices M}

def actualCandidateGraph (M : MergedPairs F) : SimpleGraph (AvailableCandidate M) where
  Adj v w := CandidateAdjacent M v.val w.val
  symm := ⟨fun _ _ h => candidateAdjacent_symm h⟩
  loopless := ⟨fun v => candidateAdjacent_irrefl M v.val⟩

def candidateSelectionInput (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) :
    Selection.Input (Slot F) (AvailableCandidate M) where
  graph := actualCandidateGraph M
  slot v := v.val.1
  exceptional v := (J v).subtype (fun w => w ∈ candidateVertices M)

private theorem subtype_card_of_subset {α : Type*} [DecidableEq α]
    (s t : Finset α) (h : s ⊆ t) :
    (s.subtype (fun x => x ∈ t)).card = s.card := by
  rw [Finset.card_subtype]
  rw [Finset.filter_eq_self.mpr h]

private theorem subtype_inter {α : Type*} [DecidableEq α]
    (s t U : Finset α) :
    s.subtype (fun x => x ∈ U) ∩ t.subtype (fun x => x ∈ U) =
      (s ∩ t).subtype (fun x => x ∈ U) := by
  ext x
  simp

theorem candidateSelection_slot_eq (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    Selection.slotVertices (candidateSelectionInput M J) s =
      (candidateSlot M s).subtype (fun w => w ∈ candidateVertices M) := by
  ext v
  simp only [Selection.slotVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [candidateSelectionInput, candidateSlot, v.property]

theorem candidateSelection_neighbors_eq (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (v : AvailableCandidate M) :
    Selection.neighbors (candidateSelectionInput M J) v =
      (candidateNeighbors M v.val).subtype (fun w => w ∈ candidateVertices M) := by
  ext w
  simp only [Selection.neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [candidateSelectionInput, actualCandidateGraph,
    candidateNeighbors, w.property]

theorem candidateSelection_slot_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    (Selection.slotVertices (candidateSelectionInput M J) s).card =
      (candidateSlot M s).card := by
  rw [candidateSelection_slot_eq]
  exact subtype_card_of_subset _ _ (Finset.filter_subset _ _)

theorem candidateSelection_neighbors_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (v : AvailableCandidate M) :
    (Selection.neighbors (candidateSelectionInput M J) v).card =
      (candidateNeighbors M v.val).card := by
  rw [candidateSelection_neighbors_eq]
  exact subtype_card_of_subset _ _ (Finset.filter_subset _ _)

theorem candidateSelection_neighbor_slot_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (v : AvailableCandidate M) (s : Slot F) :
    ((Selection.neighbors (candidateSelectionInput M J) v) ∩
      Selection.slotVertices (candidateSelectionInput M J) s).card =
      ((candidateNeighbors M v.val) ∩ candidateSlot M s).card := by
  rw [candidateSelection_neighbors_eq, candidateSelection_slot_eq, subtype_inter]
  apply subtype_card_of_subset
  exact Finset.Subset.trans Finset.inter_subset_left (Finset.filter_subset _ _)

theorem candidateSelection_common_neighbors_card (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (v w : AvailableCandidate M) :
    ((Selection.neighbors (candidateSelectionInput M J) v) ∩
      Selection.neighbors (candidateSelectionInput M J) w).card =
      ((candidateNeighbors M v.val) ∩ candidateNeighbors M w.val).card := by
  rw [candidateSelection_neighbors_eq, candidateSelection_neighbors_eq, subtype_inter]
  apply subtype_card_of_subset
  exact Finset.Subset.trans Finset.inter_subset_left (Finset.filter_subset _ _)

theorem candidateGraphGood_selection {M : MergedPairs F} {c C : ℝ}
    (hgood : CandidateGraphGood M c C) :
    ∃ J : AvailableCandidate M → Finset (CandidateVertex F),
      Selection.GraphBounds (candidateSelectionInput M J) (Fintype.card F) c C := by
  rcases hgood with ⟨hslots, hvertices, hexceptions, _hmult, _hoccup⟩
  choose J hJ using (fun v : AvailableCandidate M => hexceptions v.val v.property)
  refine ⟨J, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Slot, Direction, Fintype.card_prod, Nat.mul_comm]
  · intro v w hslot hadj
    exact hadj.2.2.1 hslot
  · intro i
    rw [candidateSelection_slot_card]
    exact hslots i
  · intro v
    rw [candidateSelection_neighbors_card]
    exact (hvertices v.val v.property).1
  · intro v i
    have hc := candidateSelection_neighbor_slot_card M J v i
    have h := (hvertices v.val v.property).2 i
    convert h using 1
    congr 1
    convert hc using 1
    congr 1
    ext x
    simp
  · intro v
    change (((J v).subtype (fun w => w ∈ candidateVertices M)).card : ℝ) ≤ _
    rw [subtype_card_of_subset _ _ (hJ v).1]
    exact (hJ v).2.1
  · intro v w hw
    have hw' : w.val ∉ J v := by
      simpa [candidateSelectionInput] using hw
    have h := (hJ v).2.2.2 w.val w.property hw'
    have hc := candidateSelection_common_neighbors_card M J v w
    convert h using 1
    congr 1
    convert hc using 1
    congr 1
    ext x
    simp
  · intro v w hw
    have hw' : w.val ∈ J v := by
      simpa [candidateSelectionInput] using hw
    rcases (hJ v).2.2.1 w.val hw' with h | h
    · exact Or.inl h
    · exact Or.inr h.symm

theorem candidateSelection_lineAssignment (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) :
    Selection.LineAssignment (candidateSelectionInput M J) (coordinatePlane F)
      (Equiv.refl (Slot F)) (fun v : AvailableCandidate M => candidateLine v.val) := by
  constructor
  · intro v
    rfl
  · intro v w hslot hline
    apply Subtype.ext
    apply Prod.ext
    · exact hslot
    · exact congrArg (fun l : Line F => l.2) hline

theorem candidateSelection_selector_of_transversal (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a) :
    CandidateSelector M (fun s => (a s).val.2) ∧
      IndependentSelector M (fun s => (a s).val.2) := by
  have heq (s : Slot F) : (a s).val = (s, (a s).val.2) :=
    Prod.ext (ha.1 s) rfl
  constructor
  · intro s
    have h := mem_candidateVertices.mp (a s).property
    rw [heq s] at h
    exact h
  · intro s t hst
    have h := ha.2 s t hst
    change ¬ CandidateAdjacent M (a s).val (a t).val at h
    rw [heq s, heq t] at h
    exact h

theorem candidateSelection_configuration_of_transversal (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M) (hd : DistinctConstituents M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a) :
    (selectedConfiguration M (fun s => (a s).val.2)).Valid ∧
      (selectedConfiguration M (fun s => (a s).val.2)).Compatible := by
  obtain ⟨hs, hi⟩ := candidateSelection_selector_of_transversal M J a ha
  exact ⟨selectedConfiguration_valid hd hs,
    (selectedConfiguration_compatible_iff hs).mpr hi⟩

end
end Balanced

end OAI
