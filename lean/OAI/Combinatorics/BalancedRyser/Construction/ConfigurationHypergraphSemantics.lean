import OAI.Combinatorics.BalancedRyser.Construction.ConstructionRepresentationLemmas
import OAI.Combinatorics.BalancedRyser.Construction.HypergraphSemantics

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

noncomputable def toHypergraphEdgeEquiv (H : PartiteHypergraph r n) :
    {e // e ∈ H.edges} ≃ H.toHypergraph.edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨↑(edgeVertices e.val), ⟨e.val, e.property, rfl⟩⟩)
    (by
      constructor
      · intro e f h
        apply Subtype.ext
        exact coe_edgeVertices_injective (congrArg Subtype.val h)
      · rintro ⟨E, e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩)

theorem no_standard_cover_at_most_rank_sub_one (H : PartiteHypergraph r r)
    (hr : 0 < r) (hcover : H.HasCoverNumber r)
    (C : Set (Vertex r r)) (hC : C.ncard ≤ r - 1) :
    ¬ ∀ E ∈ H.toHypergraph.edgeSet, (C ∩ E).Nonempty := by
  intro hc
  have hlower := ((toHypergraph_hasCoverNumber_iff H r).mp hcover).2 C hc
  omega

end Balanced.PartiteHypergraph

namespace Balanced.ConfigurationRealization

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}
variable {H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)}

noncomputable def standardEdgeEquiv (h : ConfigurationRealization C H) :
    {p : Point F // p ∈ C.points} ≃ H.toHypergraph.edgeSet :=
  h.edgeEquiv.trans H.toHypergraphEdgeEquiv

theorem standardEdgeEquiv_incidence (h : ConfigurationRealization C H)
    (p : {p : Point F // p ∈ C.points})
    (b : {b : Configuration.BlockLabel F // b ∈ C.blockLabels}) :
    h.labelEquiv b ∈ (h.standardEdgeEquiv p).val ↔ p.val ∈ C.blockPoints b.val := by
  change h.labelEquiv b ∈ PartiteHypergraph.edgeVertices (h.edgeEquiv p).val ↔ _
  rw [PartiteHypergraph.mem_edgeVertices]
  exact (h.incidence p b).symm

theorem standard_edgeSet_ncard (h : ConfigurationRealization C H) :
    H.toHypergraph.edgeSet.ncard = C.points.card := by
  rw [H.toHypergraph_edgeSet_ncard]
  simpa only [Fintype.card_coe] using (Fintype.card_congr h.edgeEquiv).symm

end Balanced.ConfigurationRealization

end OAI
