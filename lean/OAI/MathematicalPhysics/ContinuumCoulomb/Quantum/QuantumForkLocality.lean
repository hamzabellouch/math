import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkPlaced

namespace OAI

/-! Fork corrections and new mediator edges are local to one original coarse cell. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

theorem qmaForkCellAligned_site {n c : ℕ} {d : Fin c → ℕ} {β : Type*}
    (P : QMAForkPorts n c d) (cell : Fin n → β) (h : QMAForkCellAligned P cell)
    (e : Fin P.pairCount) (a : Fin 3) :
    cell (P.site e a) = cell (P.center (P.pairEquiv.symm e).1) := by
  fin_cases a
  · rfl
  · exact h (qmaForkPairedPort d (P.pairEquiv.symm e,0))
  · exact h (qmaForkPairedPort d (P.pairEquiv.symm e,1))

namespace QMAPlacedForkNetwork
variable {β : Type*} {c : ℕ}

def BackgroundLocal (G : QMAPlacedForkNetwork β c) (R : β → β → Prop) : Prop :=
  ∀ e, R (G.cell (G.graph.state.left e)) (G.cell (G.graph.state.right e))

theorem next_backgroundLocal (G : QMAPlacedForkNetwork β c) (R : β → β → Prop)
    (hr : ∀ x, R x x) (h : G.BackgroundLocal R) : G.next.BackgroundLocal R := by
  intro e
  change R (qmaForkCellNext G.graph.state.ports G.cell
    (qmaForkBackgroundLeft G.graph.state.left G.graph.state.ports.site e))
    (qmaForkCellNext G.graph.state.ports G.cell
      (qmaForkBackgroundRight G.graph.state.right G.graph.state.ports.site e))
  rcases e with (e | e) | (e | ⟨e,b⟩)
  · simpa only [qmaForkBackgroundLeft,qmaForkBackgroundRight,qmaParallelGraphLeft,
      qmaParallelGraphRight,qmaForksBaseLeft,qmaForksBaseRight,Sum.elim_inl,
      qmaForkCellNext_old] using h e
  · simp only [qmaForkBackgroundLeft,qmaForkBackgroundRight,qmaParallelGraphLeft,
      qmaParallelGraphRight,qmaForksBaseLeft,qmaForksBaseRight,Sum.elim_inr,
      qmaForkCellNext_old,qmaForkCellAligned_site _ _ G.aligned]
    exact hr _
  · simp only [qmaForkBackgroundLeft,qmaForkBackgroundRight,qmaParallelGraphLeft,
      qmaParallelGraphRight,qmaForkCellNext_fresh]
    exact hr _
  · simp only [qmaForkBackgroundLeft,qmaForkBackgroundRight,qmaParallelGraphLeft,
      qmaParallelGraphRight,qmaForkCellNext_old,qmaForkCellNext_fresh,qmaForkOuter,
      qmaForkCellAligned_site _ _ G.aligned]
    exact hr _

theorem iterate_backgroundLocal (G : QMAPlacedForkNetwork β c) (R : β → β → Prop)
    (hr : ∀ x, R x x) (h : G.BackgroundLocal R) (k : ℕ) : (G.iterate k).BackgroundLocal R := by
  induction k with
  | zero => exact h
  | succ k ih => exact (G.iterate k).next_backgroundLocal R hr ih

theorem full_local (G : QMAPlacedForkNetwork β c) (R : β → β → Prop)
    (hr : ∀ x, R x x) (h : G.BackgroundLocal R)
    (e : G.graph.Edge ⊕ (Σ i, Fin (G.graph.degree i))) :
    R (G.cell (G.graph.state.fullLeft e)) (G.cell (G.graph.state.fullRight e)) := by
  rcases e with e | p
  · exact h e
  · change R (G.cell (G.graph.state.ports.center p.1)) (G.cell (G.graph.state.ports.port p))
    rw [G.aligned p]
    exact hr _

end QMAPlacedForkNetwork
end ContinuumCoulomb

end

end OAI
