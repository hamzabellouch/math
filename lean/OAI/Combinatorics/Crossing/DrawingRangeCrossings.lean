import OAI.Combinatorics.Crossing.DrawingDefinition

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem edgeInterior_subset_range (D : ContinuousDrawing m n) (e : BipartiteEdge m n) :
    edgeInterior D e ⊆ Set.range (D.edge e) := by
  rintro x ⟨t,_,he⟩
  exact ⟨t,he⟩

theorem edgeInterior_of_range_not_vertices (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hvertex : ∀ j, x ≠ D.vertex j) :
    x ∈ edgeInterior D e := by
  obtain ⟨t,he⟩ := hx
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).source)
  have ht1 : t ≠ 1 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).target)
  exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

theorem edgeInterior_not_vertex (D : ContinuousDrawing m n) (e : BipartiteEdge m n)
    (x : Plane) (hx : x ∈ edgeInterior D e) (j : BipartiteVertex m n) : x ≠ D.vertex j := by
  obtain ⟨t,ht,he⟩ := hx
  exact fun hj => D.interior_avoids_vertices e t ht j (he.trans hj)

theorem crossing_of_ranges_not_vertices (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (he : x ∈ Set.range (D.edge e)) (hf : x ∈ Set.range (D.edge f))
    (hv : ∀ j, x ≠ D.vertex j) : x ∈ crossingPoints D :=
  ⟨e,f,hef,edgeInterior_of_range_not_vertices D e x he hv,edgeInterior_of_range_not_vertices D f x hf hv⟩

end Zarankiewicz

end

end OAI
