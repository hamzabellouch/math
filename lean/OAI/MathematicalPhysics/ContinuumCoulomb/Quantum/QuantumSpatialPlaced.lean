import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialDegreeReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitialLocality

namespace OAI

/-! The actual degree-three output retains constant density in the original rectangular grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def placedDegreeReduction : QMAPlacedForkNetwork (QMAGridCell M.rows M.width) M.n :=
  (qmaSubdivisionPlaced M.indexedLeft M.indexedRight M.cell).iterate (9*B)

theorem placedDegreeReduction_graph (N : ℝ) :
    M.placedDegreeReduction.graph = (M.degreeReduction N).graph := by
  unfold placedDegreeReduction degreeReduction
  rw [QMAPlacedForkNetwork.iterate_graph,qmaDegreeReduction_graph]
  rfl

theorem placedDegreeReduction_density (p : QMAGridCell M.rows M.width) :
    qmaCellMass M.placedDegreeReduction.cell p ≤ (1+9*B+2*(9*B)^2)*A := by
  have h := qmaSubdivisionPlaced_density M.indexedLeft M.indexedRight M.indexed_distinct
    M.cell (9*B) M.indexed_degree_bound p
  have hc : qmaCellMass M.cell p ≤ A := by
    simpa [qmaCellMass] using M.qubitDensity p
  exact h.trans (Nat.mul_le_mul_left _ hc)

theorem placedDegreeReduction_local :
    let G := M.placedDegreeReduction
    ∀ e, ∃ a : QMAGridCell M.rows M.width,
      QMAGridCellsNear (G.cell (G.graph.state.fullLeft e)) a ∧
        QMAGridCellsNear (G.cell (G.graph.state.fullRight e)) a := by
  let R := fun p q : QMAGridCell M.rows M.width =>
    ∃ a, QMAGridCellsNear p a ∧ QMAGridCellsNear q a
  have hr : ∀ p, R p p := by
    intro p
    refine ⟨p,?_,?_⟩ <;> simp [QMAGridCellsNear]
  have he : ∀ e, R (M.cell (M.indexedLeft e)) (M.cell (M.indexedRight e)) := by
    intro e
    exact ⟨M.anchor (M.termIndex.symm e),M.geometry (M.termIndex.symm e)⟩
  exact qmaSubdivisionPlaced_full_local M.indexedLeft M.indexedRight M.cell R hr he (9*B)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
