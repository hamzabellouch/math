import OAI.Combinatorics.Crossing.CycleBlockIntersections

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_closed_cycle_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → (completeBipartite m n).Dart)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
        (N K : ℕ), d N=d 0 → f K=f 0 →
        (∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i)) →
        (∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) →
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        (bipartiteDartSign (d i)*bipartiteDartSign (f j)*
          V.signedIntersection (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))+
            C.passageIntersection d f hd hf i j ε)=0 := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cycle_block_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro ε hε hs d f hd hf N K hN hK hdi hfj
  let P := V.dartCycleChain d hd N hN
  let Q := C.shiftedCycleChain f hf K hK ε
  have hblocks (i j : ℕ) (hi : i < N) (hj : j < K) :=
    hh ε hε hs d f hd hf i j (hdi i hi) (hfj j hj)
  have hT : P.Transverse Q := by
    change (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).Transverse
      (finitePolygonalChain Set.univ (C.shiftedCycleVertex f ε) (Set.mem_univ _) (C.shiftedCycleBlock f hf ε) K)
    apply finitePolygonalChain_transverse_left
    intro i hi
    apply finitePolygonalChain_transverse_right
    intro j hj
    exact (hblocks i j hi hj).1
  have hzero := P.closed_intersection_zero Q hT
  have hsplit : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces :=
    finitePolygonalChain_intersection_double _ _ _ _ _ _ _ _
  rw [hsplit] at hzero
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hblocks i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)).2.symm
    _ = 0 := hzero

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
