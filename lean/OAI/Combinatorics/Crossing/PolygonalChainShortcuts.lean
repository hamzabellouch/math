import OAI.Combinatorics.Crossing.PolygonalChainOperations

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def withEndpoints (P : PolygonalChain O a b) {a' b' : Plane}
    (ha : a'=a) (hb : b'=b) : PolygonalChain O a' b' where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first.trans ha.symm
  last := P.last.trans hb.symm
  start_mem := ha.symm ▸ P.start_mem
  inside := P.inside

theorem minimum_shortcut_bound (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.pieces)
    (Q : PolygonalChain O (P.vertices i) (P.vertices j)) : j-i ≤ Q.pieces := by
  have hh := hmin (((P.take i (by omega)).join Q).join (P.drop j hj))
  simp only [pieces_join,pieces_take,pieces_drop] at hh
  omega

theorem minimum_vertices_ne (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i < j) (hj : j ≤ P.pieces) : P.vertices i ≠ P.vertices j := by
  intro he
  let Q := (point O (P.vertices i) (P.vertex_mem i (by omega))).withEndpoints rfl he.symm
  have hh := P.minimum_shortcut_bound hmin i j (by omega) hj Q
  change j-i ≤ 0 at hh
  omega

theorem minimum_nonadjacent_disjoint (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i+1 < j) (hj : j < P.pieces) :
    Disjoint (segment ℝ (P.vertices i) (P.vertices (i+1)))
      (segment ℝ (P.vertices j) (P.vertices (j+1))) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hleft : segment ℝ (P.vertices i) x ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hxi).trans
      (P.inside i (by omega))
  have hright : segment ℝ x (P.vertices (j+1)) ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset hxj (right_mem_segment ℝ _ _)).trans
      (P.inside j hj)
  let Q := (single O (P.vertices i) x (P.vertex_mem i (by omega)) hleft).join
    (single O x (P.vertices (j+1)) (P.inside i (by omega) hxi) hright)
  have hh := P.minimum_shortcut_bound hmin i (j+1) (by omega) (by omega) Q
  change j+1-i ≤ 1+1 at hh
  omega

theorem minimum_two_step_not_subset (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    ¬ segment ℝ (P.vertices i) (P.vertices (i+2)) ⊆ O := by
  intro h
  have hh := P.minimum_shortcut_bound hmin i (i+2) (by omega) hi
    (single O (P.vertices i) (P.vertices (i+2)) (P.vertex_mem i (by omega)) h)
  change i+2-i ≤ 1 at hh
  omega

end Zarankiewicz.PolygonalChain

end

end OAI
