import OAI.Combinatorics.Crossing.GraphWalkTrace

namespace OAI

noncomputable section
namespace Zarankiewicz

def exteriorSegmentGraph (G : SimpleGraph Plane) (U : Set Plane) : SimpleGraph Plane where
  Adj := fun a b => G.Adj a b ∧ Disjoint (segment ℝ a b) U
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa only [segment_symm] using h.2⟩⟩
  loopless := ⟨by intro a h; exact G.loopless.irrefl a h.1⟩

theorem exteriorSegmentGraph_le (G : SimpleGraph Plane) (U : Set Plane) :
    exteriorSegmentGraph G U ≤ G := fun _ _ h => h.1

theorem graphWalkPath_edge_subset_range {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (u v : Plane) (huv : s(u,v) ∈ p.edges) :
    segment ℝ u v ⊆ Set.range (graphWalkPath id p) := by
  obtain ⟨i,hi,he⟩ := (p.mk_mem_edges_iff_exists).mp huv
  have hpiece := polygonalArcPath_piece_subset_range (fun i => p.getVert i) p.length i hi
  change segment ℝ u v ⊆ Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  rcases Sym2.eq_iff.mp he with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using hpiece
  · simpa only [h0,h1,segment_symm] using hpiece

def exteriorGraphWalk {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorSegmentGraph G U).Walk a b :=
  p.transfer (exteriorSegmentGraph G U) (by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro huv
      exact ⟨p.adj_of_mem_edges huv,h.mono_left (graphWalkPath_edge_subset_range p u v huv)⟩)

theorem exteriorGraphWalk_getVert {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) (i : ℕ) :
    (exteriorGraphWalk p U h).getVert i=p.getVert i := by
  have hlen : (exteriorGraphWalk p U h).length=p.length := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]
  have hsupport : (exteriorGraphWalk p U h).support=p.support := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.support_transfer]
  by_cases hi : i ≤ p.length
  · have hi' : i ≤ (exteriorGraphWalk p U h).length := by rw [hlen]; exact hi
    rw [SimpleGraph.Walk.getVert_eq_support_getElem _ hi',p.getVert_eq_support_getElem hi]
    simp only [hsupport]
  · rw [SimpleGraph.Walk.getVert_of_length_le _ (by
      rw [hlen]
      omega),p.getVert_of_length_le (by omega)]

theorem exteriorGraphWalk_length {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorGraphWalk p U h).length=p.length := by
  simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]

theorem exteriorGraphWalk_trace {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    Set.range (graphWalkPath id (exteriorGraphWalk p U h))=Set.range (graphWalkPath id p) := by
  change Set.range (polygonalArcPath (fun i => (exteriorGraphWalk p U h).getVert i)
    (exteriorGraphWalk p U h).length)=Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  have hf : (fun i => (exteriorGraphWalk p U h).getVert i)=(fun i => p.getVert i) :=
    funext (exteriorGraphWalk_getVert p U h)
  exact congrArg₂ (fun (seq : ℕ → Plane) (k : ℕ) =>
    Set.range (fun t : unitInterval => polygonalArcPath seq k t)) hf (exteriorGraphWalk_length p U h)

end Zarankiewicz

end

end OAI
