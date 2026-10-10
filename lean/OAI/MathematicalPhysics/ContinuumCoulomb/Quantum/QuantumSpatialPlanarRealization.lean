import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortPlanarRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSize
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedPortRealization
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedSourceCells

namespace OAI

/-! Every actual degree-three spatial exchange model has a nearest-neighbor
square-lattice realization. The number of layers and the size factor depend
only on its fixed spatial-density constants. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem placedVertex_positive (v : Fin M.n) :
    0 < (M.placedVertex v).1 ∧ 0 < (M.placedVertex v).2 := by
  change 0 < 8*(9*B+3+6)*(M.routeVertex v).1+17 ∧
    0 < 8*(9*B+3+6)*(M.routeVertex v).2+17
  omega

theorem planar_realize (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {N : ℚ} (hN : 0 < N) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < 256*M.bufferedWidth ∧ (position v).2 < 256*M.bufferedHeight) ∧
      (∀ e, qmaSquareGrid.Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ 4) ∧
      H.n+Fintype.card H.Edge ≤
        (5^81*(5^(routeLengthBound A B)+11*routeLengthBound A B))*(M.n+Fintype.card M.Term) ∧
      |H.energy-M.energy| ≤ ((routeLengthBound A B+82:ℕ):ℝ)/(N:ℝ) := by
  let P := M.portRouteData hA hd
  have hD : ∀ e, P.length e ≤ routeLengthBound A B := M.bufferedPath_length hd
  have hpath : ∀ e k, k ≤ P.length e →
      (P.point e k).1 < M.bufferedWidth ∧ (P.point e k).2 < M.bufferedHeight := by
    intro e k _
    exact M.bufferedPath_bounds hd e ((M.bufferedPath hd e).val.getVert_mem_support k)
  obtain ⟨H,pos,hinj,hbox,hgrid,hdegree,hsize,herr⟩ :=
    P.planar_realize hN hD (M.sourceCell_no_passage hA hd)
      M.placedVertex_positive M.placedVertex_bounds hpath
  refine ⟨H,pos,hinj,hbox,hgrid,hdegree,?_,herr⟩
  have hs := Nat.mul_le_mul_left (5^81) (P.mergedOutput_size N hD)
  exact hsize.trans (by simpa only [Nat.mul_assoc] using hs)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
