import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def inducedEdges (S : Set V) : Set E := {e | ∀ v ∈ G.ends e, v∈S}

def induce (S : Set V) : BondGraph S (G.inducedEdges S) where
  ends e := (G.ends e.val).attachWith e.property

lemma induce_ends_map (S : Set V) (e : G.inducedEdges S) :
    Sym2.map Subtype.val ((G.induce S).ends e) = G.ends e.val :=
  Sym2.attachWith_map_subtypeVal _

lemma induce_ends_eq (S : Set V) (e : G.inducedEdges S) (u v : S) :
    (G.induce S).ends e = s(u,v) ↔ G.ends e.val = s(u.val,v.val) := by
  rw [← G.induce_ends_map S e,← Sym2.map_mk]
  exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  ext e
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma finite_inducedEdges (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.inducedEdges S).Finite := by
  apply (G.finite_incident hG hS).subset
  intro e he
  obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective (G.ends e)
  have hu : u ∈ G.ends e := by rw [← huv]; simp
  exact ⟨u,he u hu,hu⟩

lemma induce_adj (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Adj u v ↔
      (G.openGraph (Subtype.val '' ω)).Adj u.val v.val := by
  simp only [openGraph,SimpleGraph.fromEdgeSet_adj,Set.mem_image]
  constructor
  · rintro ⟨⟨e,he,hend⟩,hne⟩
    exact ⟨⟨e.val,⟨e,he,rfl⟩,(G.induce_ends_eq S e u v).mp hend⟩,
      fun h => hne (Subtype.ext h)⟩
  · rintro ⟨⟨e,⟨a,ha,rfl⟩,hend⟩,hne⟩
    exact ⟨⟨a,ha,(G.induce_ends_eq S a u v).mpr hend⟩,
      fun h => hne (congrArg Subtype.val h)⟩

lemma induced_adj_mem (S : Set V) (ω : Set (G.inducedEdges S)) {u v : V}
    (h : (G.openGraph (Subtype.val '' ω)).Adj u v) : u∈S ∧ v∈S := by
  obtain ⟨⟨e,⟨a,ha,rfl⟩,he⟩,_⟩ := h
  constructor
  · exact a.property u (by rw [he]; simp)
  · exact a.property v (by rw [he]; simp)

lemma induce_reachable (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Reachable u v ↔
      (G.openGraph (Subtype.val '' ω)).Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map ⟨Subtype.val, fun {a b} hab => (G.induce_adj S ω a b).mp hab⟩
  · intro h
    have H : ∀ w, (G.openGraph (Subtype.val '' ω)).Reachable u.val w →
        ∀ hw : w∈S, ((G.induce S).openGraph ω).Reachable u ⟨w,hw⟩ := by
      intro w hh
      rw [SimpleGraph.reachable_iff_reflTransGen] at hh
      induction hh with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail w z _ hz ih =>
        intro hmem
        have hw := (G.induced_adj_mem S ω hz).1
        exact (ih hw).trans ((G.induce_adj S ω ⟨w,hw⟩ ⟨z,hmem⟩).mpr hz).reachable
    exact H v.val h v.property

lemma induced_cluster_subset (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    G.cluster (Subtype.val '' ω) u.val ⊆ S := by
  intro v hv
  rw [cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact u.property
  | tail _ hadj _ => exact (G.induced_adj_mem S ω hadj).2

lemma induce_cluster_image (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    Subtype.val '' ((G.induce S).cluster ω u) = G.cluster (Subtype.val '' ω) u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.induce_reachable S ω u a).mp ha
  · intro hv
    have hmem := G.induced_cluster_subset S ω u hv
    exact ⟨⟨v,hmem⟩,(G.induce_reachable S ω u ⟨v,hmem⟩).mpr hv,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
