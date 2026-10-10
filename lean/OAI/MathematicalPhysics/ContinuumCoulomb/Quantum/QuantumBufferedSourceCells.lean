import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortChain
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPassages

namespace OAI

/-! Original spin cells contain no internal route passage. Their local connections
are precisely the vertex fanout rays, separated from crossing cells. -/

noncomputable section
namespace ContinuumCoulomb
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem coarseRoute_avoids (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) (v : Fin M.n) (hi0 : 0 < i) (hi : i < M.coarseLength hd e) :
    M.coarseRoute hd e i ≠ M.placedVertex v := by
  intro h
  have hm := (M.bufferedPath hd e).val.getVert_mem_support i
  change M.coarseRoute hd e i ∈ _ at hm
  rw [h] at hm
  rcases M.bufferedPath_vertex hd e v hm with hv | hv
  · rw [hv] at h
    have he := M.coarseRoute_simple hd e i 0 hi.le (Nat.zero_le _)
      (h.trans (M.coarseRoute_zero hd e).symm)
    omega
  · rw [hv] at h
    have he := M.coarseRoute_simple hd e i (M.coarseLength hd e) hi.le le_rfl
      (h.trans (M.coarseRoute_last hd e).symm)
    omega

theorem sourceCell_no_passage (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (i : (M.portRouteData hA hd).Interior) (v : Fin M.n) :
    (M.portRouteData hA hd).cell i ≠ M.placedVertex v := by
  apply M.coarseRoute_avoids hd i.1 (i.2.val+1) v (by omega)
  exact (M.portRouteData hA hd).cell_index_lt i

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
