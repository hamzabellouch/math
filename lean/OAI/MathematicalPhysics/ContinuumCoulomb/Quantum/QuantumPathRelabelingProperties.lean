import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabeling

namespace OAI

/-! Degree and inverse transport for finite relabelings of scheduled graphs. -/

noncomputable section
namespace ContinuumCoulomb.QMAPathRelabeling
open scoped BigOperators Classical

variable {S T : QMAPathSchedule} (E : QMAPathRelabeling S T)

def symm : QMAPathRelabeling T S where
  vertex := E.vertex.symm
  edge := E.edge.symm
  left := E.inverse_left
  right := E.inverse_right
  work f := (E.inverse_work f).symm

theorem degree (v : Fin S.graph.n) :
    qmaGraphDegree T.graph.left T.graph.right (E.vertex v) =
      qmaGraphDegree S.graph.left S.graph.right v := by
  unfold qmaGraphDegree
  have h := E.edge.sum_comp (fun f =>
    if T.graph.left f=E.vertex v ∨ T.graph.right f=E.vertex v then (1 : ℕ) else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro e _
  rw [← E.left,← E.right]
  simp only [Equiv.apply_eq_iff_eq]

end ContinuumCoulomb.QMAPathRelabeling

end

end OAI
