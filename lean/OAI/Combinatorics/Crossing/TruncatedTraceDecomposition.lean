import OAI.Combinatorics.Crossing.TruncatedChainPath

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem center_segment_in_disk (o p : Plane) (r : ℝ) (hp : squaredLength (p-o)=r^2) :
    segment ℝ o p ⊆ closedRoundDisk o r := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  have he : squaredLength (segmentPoint o p t.val-o)=t.val^2*squaredLength (p-o) := by
    dsimp [segmentPoint,squaredLength]
    ring
  have ht2 : t.val^2 ≤ 1 := by nlinarith [t.property.1,t.property.2]
  have hh := mul_le_mul_of_nonneg_right ht2 (sq_nonneg r)
  change squaredLength (x-o) ≤ r^2
  have ht' : segmentPoint o p t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  rw [← ht',he,hp]
  simpa only [one_mul] using hh

theorem drawing_edge_trace_decomposition {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    Set.range (D.edge e)=
      segment ℝ (D.vertex (.inl e.1)) (P.startPort r) ∪
        Set.range (polygonalArcPath (P.truncatedVertices r) P.pieces) ∪
        segment ℝ (P.endPort r) (D.vertex (.inr e.2)) := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : segment ℝ (D.vertex (.inl e.1)) (P.startPort r) ⊆ Set.range (D.edge e) := by
    have hx := openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment (P.vertices 0) (P.vertices 1) r hr hfirst)
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside 0 hp)
    simpa only [PolygonalChain.startPort,P.first] using hh
  have ht : segment ℝ (P.endPort r) (D.vertex (.inr e.2)) ⊆ Set.range (D.edge e) := by
    have hlen : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
      rwa [squaredLength_sub_comm]
    have hx := openSegmentTrace_subset_segment _ _
      (openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hlen))
    have hinside := P.inside (P.pieces-1) (by omega)
    rw [show P.pieces-1+1=P.pieces by omega] at hinside
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans hinside
    simpa only [PolygonalChain.endPort,P.last] using hh
  let T := P.truncated hp r hr hfirst hlast
  let G := ((Path.segment (D.vertex (.inl e.1)) (P.startPort r)).trans T.path).trans
    (Path.segment (P.endPort r) (D.vertex (.inr e.2)))
  have hG : Set.range G ⊆ Set.range (D.edge e) := by
    dsimp [G]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset (Set.union_subset hs T.path_range_subset) ht
  have he := path_range_eq_of_subset (D.edge e) G (D.edge_injective e) hG
  calc
    Set.range (D.edge e) = Set.range G := he.symm
    _ = _ := by
      dsimp [G]
      rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
      rfl

end Zarankiewicz

end

end OAI
