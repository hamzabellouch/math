import OAI.Combinatorics.Crossing.CycleMatrixBlocks
import OAI.Combinatorics.Crossing.HalfOrderInvertibility

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def leftNode (i : Fin m) (p : Fin n) : ℝ := C.node (Sum.inl i) (V.leftIncident (i,p))

theorem leftNode_injective (i : Fin m) : Function.Injective (C.leftNode i) := by
  intro p q hpq
  have he := C.node_injective (Sum.inl i) hpq
  exact congrArg (fun e : IncidentEdges (Sum.inl i) => e.val.2) he

@[instance_reducible] def leftOrder (i : Fin m) : LinearOrder (Fin n) := LinearOrder.lift' (C.leftNode i) (C.leftNode_injective i)

theorem leftHalfOrder_eq_halfOrder (i : Fin m) :
    C.leftHalfOrder i=@halfOrderMatrix (Fin n) (C.leftOrder i) := by
  ext p q
  change orderSign (C.leftNode i p) (C.leftNode i q)/2=
    if C.leftNode i p<C.leftNode i q then (1/2 : ℝ) else if C.leftNode i q<C.leftNode i p then -1/2 else 0
  unfold orderSign
  split_ifs <;> norm_num

theorem diagonal_detector_isUnit (hnorm : NoAdjacentCrossings D)
    (s : ℕ) (hs : 0 < s) (node : Fin n → ℝ) (hn : Function.Injective node)
    (hcard : n=2*s+1) (i : Fin m) :
    IsUnit (rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i)) := by
  rw [C.cycleIntersectionMatrix_diagonal_block hnorm,C.leftHalfOrder_eq_halfOrder]
  exact (lemma4_2 s hs node hn (by simpa only [Fintype.card_fin] using hcard)).2.2.2 (C.leftOrder i)

theorem offDiagonal_detector (s : ℕ) (node : Fin n → ℝ) (i k : Fin m) (hik : i ≠ k) :
    rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)=
      rankDetector s node (V.intersectionBlock i k) := by
  rw [C.cycleIntersectionMatrix_offDiagonal_block i k hik,map_add,rankDetector_diagonal,add_zero]

theorem additive_detector_relation (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (s : ℕ) (node : Fin n → ℝ) (hn : Function.Injective node) (hcard : n=2*s+1)
    (i k i₀ : Fin m) :
    rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i i₀)-
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ k)+
      rankDetector s node (edgeBlock C.cycleIntersectionMatrix i₀ i₀)=0 := by
  obtain ⟨r,c,hrc⟩ := C.lemma3_2 hnorm hstraight htrans i k i₀
  have he : blockRectangle C.cycleIntersectionMatrix i k i₀=(fun p q => r p+c q) := funext (fun p => funext (hrc p))
  have hz : rankDetector s node (blockRectangle C.cycleIntersectionMatrix i k i₀)=0 := by
    rw [he]
    exact rankDetector_additive s node hn (by simpa only [Fintype.card_fin] using hcard) r c
  simpa only [blockRectangle,map_add,map_sub] using hz

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
