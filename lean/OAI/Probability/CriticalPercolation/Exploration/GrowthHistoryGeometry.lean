import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.LatticeGrowth
import OAI.Probability.CriticalPercolation.Gluing.CorridorGraph

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph Boundary

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def revealed (S : GrowthState) : Set E :=
  boxEdges G ξ j h (0,0)∪⋃ e∈S.seen, corridorEdges G ξ j h e

lemma revealed_mono {S T : GrowthState} (hST : S.seen⊆T.seen) :
    revealed G ξ j h S⊆revealed G ξ j h T := by
  apply Set.union_subset_union_right
  intro b hb
  obtain ⟨e,he,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.mem_iUnion₂.mpr ⟨e,hST he,hb⟩

lemma boxEdges_subset_corridor_source (e : Edge) :
    boxEdges G ξ j h (source e)⊆corridorEdges G ξ j h e := by
  intro b hb v hv
  exact Or.inl (Or.inl (hb v hv))

lemma boxEdges_subset_corridor_target (e : Edge) :
    boxEdges G ξ j h (target e)⊆corridorEdges G ξ j h e := by
  intro b hb v hv
  exact Or.inl (Or.inr (hb v hv))

lemma good_box_revealed {S : GrowthState} (hs : S.Covered) {v : Site} (hv : v∈S.good) :
    boxEdges G ξ j h v⊆revealed G ξ j h S := by
  rcases hs v hv with rfl|⟨e,he,rfl⟩
  · exact Set.subset_union_left
  · intro b hb
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,boxEdges_subset_corridor_target G ξ j h e hb⟩)

lemma revealed_initial : revealed G ξ j h GrowthState.initial=boxEdges G ξ j h (0,0) := by
  simp [revealed,GrowthState.initial]

lemma revealed_advance (n : ℕ) (S : GrowthState) (b : Bool) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪
      ⋃ e∈(incoming n S.good).toFinset, corridorEdges G ξ j h e := by
  ext e
  constructor
  · rintro (he|he)
    · exact Or.inl (Or.inl he)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      rcases Finset.mem_union.mp hf with hf|hf
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩))
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩)
  · rintro ((he|he)|he)
    · exact Or.inl he
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inl hf),he⟩)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inr hf),he⟩)

lemma revealed_incoming (n : ℕ) (S : GrowthState) (b : Bool) {e : Edge}
    (he : incoming n S.good=some e) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪corridorEdges G ξ j h e := by
  rw [revealed_advance,he]
  simp

lemma later_revealed_intersection (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S T : GrowthState) (hc : S.Covered) (hv : T.Valid n)
    {e : Edge} (hp : source e∈S.good) (ht : n ≤ gridSlot (target e)) :
    revealed G ξ j h T∩corridorEdges G ξ j h e⊆revealed G ξ j h S := by
  intro b hb
  rcases hb.1 with hb0|hbT
  · exact Or.inl hb0
  · have hh' := T.seen_intersection n hv ht
    have hh'' := history_intersection_subset G ξ j h hh hhj hsep (↑T.seen) hh'.1 hh'.2
    exact good_box_revealed G ξ j h hc hp (hh'' ⟨hbT,hb.2⟩)

lemma outgoing_unrevealed (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (hn : 0<n)
    {e : Edge} (he : source e=slotSite n) :
    Disjoint (revealed G ξ j h S) (corridorEdges G ξ j h e) := by
  apply Disjoint.sup_left
  · apply edge_box_disjoint G ξ j h hh hhj hsep
    intro hroot
    have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
    have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
    rcases hroot with hh|hh
    · have he0 : gridSlot (source e)=0 := by rw [← hh]; rfl
      omega
    · have he0 : gridSlot (target e)=0 := by rw [← hh]; rfl
      omega
  · exact history_disjoint G ξ j h hh hhj hsep (↑S.seen)
      (fun f hf => S.outgoing_nonincident n hv he hf)

end CriticalPercolation.Corridor
end
end
end

end OAI
