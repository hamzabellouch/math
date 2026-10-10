import OAI.Combinatorics.Crossing.DrawingWalkCutTraces
import OAI.Combinatorics.Crossing.ExteriorSegmentGraph

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem graphWalkPath_range_iff {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (x : Plane) :
    x ∈ Set.range (graphWalkPath id p) ↔
      x=a ∨ ∃ u v, s(u,v) ∈ p.edges ∧ x ∈ segment ℝ u v := by
  constructor
  · intro hx
    rcases graphWalkPath_range_cases id p x hx with h | ⟨i,hi,hx⟩
    · exact Or.inl h
    · refine Or.inr ⟨p.getVert i,p.getVert (i+1),?_,hx⟩
      exact (p.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
  · rintro (rfl | ⟨u,v,h,hx⟩)
    · exact ⟨0,(graphWalkPath id p).source⟩
    · exact graphWalkPath_edge_subset_range p u v h hx

theorem graphWalkPath_copy_range {G : SimpleGraph Plane} {a b a' b' : Plane}
    (p : G.Walk a b) (ha : a=a') (hb : b=b') :
    Set.range (graphWalkPath id (p.copy ha hb))=Set.range (graphWalkPath id p) := by
  subst a'
  subst b'
  rfl

theorem graphWalkPath_mapLe_range {G H : SimpleGraph Plane} (hle : G ≤ H)
    {a b : Plane} (p : G.Walk a b) :
    Set.range (graphWalkPath id (p.mapLe hle))=Set.range (graphWalkPath id p) := by
  ext x
  simp only [graphWalkPath_range_iff,SimpleGraph.Walk.edges_mapLe_eq_edges]

theorem graphWalkPath_append_range {G : SimpleGraph Plane} {a b c : Plane}
    (p : G.Walk a b) (q : G.Walk b c) :
    Set.range (graphWalkPath id (p.append q))=
      Set.range (graphWalkPath id p) ∪ Set.range (graphWalkPath id q) := by
  ext x
  simp only [Set.mem_union,graphWalkPath_range_iff,SimpleGraph.Walk.edges_append,List.mem_append]
  constructor
  · rintro (hx | ⟨u,v,h,hx⟩)
    · exact Or.inl (Or.inl hx)
    · rcases h with h | h
      · exact Or.inl (Or.inr ⟨u,v,h,hx⟩)
      · exact Or.inr (Or.inr ⟨u,v,h,hx⟩)
  · rintro ((hx | ⟨u,v,h,hx⟩) | (hx | ⟨u,v,h,hx⟩))
    · exact Or.inl hx
    · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · have hb : x ∈ Set.range (graphWalkPath id p) := ⟨1,(graphWalkPath id p).target.trans hx.symm⟩
      rcases (graphWalkPath_range_iff p x).mp hb with h | ⟨u,v,h,hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · exact Or.inr ⟨u,v,Or.inr h,hx⟩

theorem graphWalkPath_toWalk_range {G : SimpleGraph Plane} {a b : Plane} (h : G.Adj a b) :
    Set.range (graphWalkPath id h.toWalk)=segment ℝ a b := by
  change Set.range (Path.segment a b)=segment ℝ a b
  exact Path.range_segment a b

end Zarankiewicz

end

end OAI
