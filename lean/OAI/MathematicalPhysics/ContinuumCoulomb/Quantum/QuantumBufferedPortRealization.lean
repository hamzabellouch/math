import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortChain
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainBounds

namespace OAI

/-! A fixed number of rational mediator layers realizes every bounded spatial
route on its explicit port graph, with full-space energy comparison. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def routeLengthBound (A B : ℕ) : ℕ := 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)

theorem portEmbedding_bounded (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    (M.portEmbedding hA hd).Bounded (32*M.bufferedWidth) (32*M.bufferedHeight) := by
  constructor
  · intro v
    exact qmaExpandedPoint_bounds (M.placedVertex_bounds v).1 (M.placedVertex_bounds v).2
  · intro e k hk
    exact qmaPortChain_bounds (M.coarseRoute hd e)
      (fun i _ => M.bufferedPath_bounds hd e ((M.bufferedPath hd e).val.getVert_mem_support i)) k hk

theorem port_realize (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {N : ℚ} (hN : 0 < N) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < 32*M.bufferedWidth ∧ (position v).2 < 32*M.bufferedHeight) ∧
      (∀ e, (M.portGraph hd).Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ 3) ∧
      H.n+Fintype.card H.Edge ≤ 5^(routeLengthBound A B)*(M.n+Fintype.card M.Term) ∧
      |H.energy-M.energy| ≤ (routeLengthBound A B:ℝ)/(N:ℝ) := by
  have hD : ∀ e, (M.portRouteData hA hd).schedule.work e ≤ routeLengthBound A B := M.bufferedPath_length hd
  obtain ⟨H,pos,hinj,hbox,hadj,hdeg,hsize,herror⟩ :=
    (M.portEmbedding hA hd).realize hN (by decide : 3 ≤ 3) hD (M.portEmbedding_bounded hA hd) hd
  rw [M.portRouteData_graph hA hd] at hadj
  refine ⟨H,pos,hinj,hbox,hadj,hdeg,hsize,?_⟩
  exact herror

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
