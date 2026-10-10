import OAI.Combinatorics.Crossing.TruncatedSignedIntersections
import OAI.Combinatorics.Crossing.DetectorRank

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)

def intersectionBlock (i k : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => V.signedIntersection (i,p) (k,q)

theorem detector_rank_le_rowCrossingCount (s : ℕ) (node : Fin n → ℝ) (i k : Fin m) :
    (rankDetector s node (V.intersectionBlock i k)).rank ≤ rowCrossingCount D i k := by
  classical
  apply (rankDetector_support_bound s node (V.intersectionBlock i k)).trans
  rw [Finset.card_filter,Fintype.sum_prod_type]
  unfold rowCrossingCount
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  by_cases hh : p ≠ q ∧ V.intersectionBlock i k p q ≠ 0
  · rw [ite_eq_left hh]
    exact V.pairCrossings_pos_of_signedIntersection_ne_zero (i,p) (k,q) hh.2
  · rw [ite_eq_right hh]
    exact Nat.zero_le _

theorem ordered_detector_rank_le_twice_crossings (hnorm : NoAdjacentCrossings D)
    (s : ℕ) (node : Fin n → ℝ) :
    (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (rankDetector s node (V.intersectionBlock i k)).rank) ≤
      2*crossingCount D := by
  rw [← sum_offDiagonal_rowCrossingCount D hnorm]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro k hk
  exact V.detector_rank_le_rowCrossingCount s node i k

end Zarankiewicz.VertexTruncation

end

end OAI
