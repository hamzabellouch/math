import OAI.Combinatorics.Crossing.VertexOrderDetector
import OAI.Combinatorics.Crossing.IndexedMatrixRankSum

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem odd_normalized_crossing_lower_bound (C : TruncatedSpokeCoordinates V) (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (s : ℕ) (hs : 0 < s) (hcard : n=2*s+1) (hm : 0 < m) :
    axisPairs m*(s*s) ≤ crossingCount D := by
  let node : Fin n → ℝ := fun p => p.val
  have hnode : Function.Injective node := by
    intro p q hpq
    apply Fin.ext
    change (p.val : ℝ)=(q.val : ℝ) at hpq
    exact_mod_cast hpq
  let i₀ : Fin m := ⟨0,hm⟩
  let H := fun i k : Fin m => rankDetector s node (edgeBlock C.cycleIntersectionMatrix i k)
  let X := fun i : Fin m => H i i₀
  let Y := fun k : Fin m => H i₀ i₀-H i₀ k
  have hH (i k : Fin m) : H i k=X i-Y k := by
    have hh := C.additive_detector_relation hnorm hstraight htrans s node hnode hcard i k i₀
    change H i k-H i i₀-H i₀ k+H i₀ i₀=0 at hh
    dsimp only [X,Y]
    calc
      H i k=(H i k-H i i₀-H i₀ k+H i₀ i₀)+(H i i₀-(H i₀ i₀-H i₀ k)) := by abel
      _ = _ := by rw [hh,zero_add]
  have hdiag : ∀ i, IsUnit (X i-Y i) := by
    intro i
    rw [← hH]
    exact C.diagonal_detector_isUnit hnorm s hs node hnode hcard i
  have hlower := matrix_rank_sum_bound_product m s X Y hdiag
  have hsum : (∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (X i-Y k).rank)=
      ∑ i : Fin m, ∑ k ∈ Finset.univ.erase i, (rankDetector s node (V.intersectionBlock i k)).rank := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hH]
    exact congrArg Matrix.rank (C.offDiagonal_detector s node i k (Ne.symm (Finset.mem_erase.mp hk).1))
  rw [hsum] at hlower
  have hupper := V.ordered_detector_rank_le_twice_crossings hnorm s node
  have hh := hlower.trans hupper
  nlinarith

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
