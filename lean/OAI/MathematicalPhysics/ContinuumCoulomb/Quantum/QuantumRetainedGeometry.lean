import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRaySupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlacement
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortCellPositive

namespace OAI

/-! The actual retained interactions are source rays, noncrossing cell pairs,
or external corridors. All endpoint positions incorporate the inward move. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaMovedPort (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) : ℕ × ℕ :=
  if cross p then qmaInnerPort p a else qmaGridPort p a

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

def RetainedGeometry (x y : ℕ × ℕ) : Prop :=
  (∃ p a, (∃ v, P.position v = p) ∧ ¬P.IsCrossing p ∧
    ((x = qmaExpandedPoint p ∧ y = qmaGridPort p a) ∨
     (x = qmaGridPort p a ∧ y = qmaExpandedPoint p))) ∨
  (∃ p a b, ¬P.IsCrossing p ∧ x = qmaGridPort p a ∧ y = qmaGridPort p b ∧
    ∃ i : P.Interior, P.cell i = p ∧
      ((P.port i 0 = a ∧ P.port i 1 = b) ∨ (P.port i 0 = b ∧ P.port i 1 = a))) ∨
  (∃ p q, qmaSquareGrid.Adj p q ∧ (0 < p.1 ∧ 0 < p.2) ∧ (0 < q.1 ∧ 0 < q.2) ∧
    x = qmaMovedPort P.IsCrossing p (qmaGridNeighborIndex p q) ∧
    y = qmaMovedPort P.IsCrossing q (qmaGridNeighborIndex q p))

theorem retained_geometry (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
    (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
    (e : (P.portCrossingSelection N hD).retained.Edge) :
    P.RetainedGeometry
      (P.movedPosition N D ((P.finishedGraph N D).left e.val))
      (P.movedPosition N D ((P.finishedGraph N D).right e.val)) := by
  have hadj := P.finished_edge_adjacent N hD e.val
  rcases P.finished_edge_link N hD e.val with
    ⟨p,a,⟨hl,hr⟩ | ⟨hl,hr⟩⟩ | ⟨p,a,b,hl,hr⟩ | ⟨p,q,hpq,hl,hr⟩
  · have hn : ¬P.IsCrossing p := by
      apply P.graph_center_not_crossing havoid
      simpa only [hl] using hadj
    have hv := P.graph_center_source (by simpa only [hl] using hadj)
    refine Or.inl ⟨p,a,hv,hn,Or.inl ?_⟩
    simp only [movedPosition,hl,hr,qmaCrossingMove_center,qmaCrossingMove_port,hn,ite_false]
    constructor <;> trivial
  · have hn : ¬P.IsCrossing p := by
      apply P.graph_center_not_crossing havoid
      simpa only [hr] using hadj.symm
    have hv := P.graph_center_source (by simpa only [hr] using hadj.symm)
    refine Or.inl ⟨p,a,hv,hn,Or.inr ?_⟩
    simp only [movedPosition,hl,hr,qmaCrossingMove_center,qmaCrossingMove_port,hn,ite_false]
    constructor <;> trivial
  · have hn : ¬P.IsCrossing p := by
      intro hc
      exact P.retained_no_internal_crossing N hD e ⟨p,P.mem_crossingCells.mpr hc⟩ a b hl hr
    have hvis := P.graph_inner_pair (by simpa only [hl,hr] using hadj)
    refine Or.inr (Or.inl ⟨p,a,b,hn,?_,?_,hvis⟩)
    · simp only [movedPosition,hl,qmaCrossingMove_port,hn,ite_false]
    · simp only [movedPosition,hr,qmaCrossingMove_port,hn,ite_false]
  · have hpos := P.graph_cell_positive hadj
    simp only [hl,hr,qmaDirectedPort,qmaPointCell_port] at hpos
    refine Or.inr (Or.inr ⟨p,q,hpq,hpos.1,hpos.2,?_,?_⟩)
    · simp only [movedPosition,hl,qmaDirectedPort,qmaCrossingMove_port,qmaMovedPort]
    · simp only [movedPosition,hr,qmaDirectedPort,qmaCrossingMove_port,qmaMovedPort]

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
