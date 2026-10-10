import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRounds

namespace OAI

/-! Repeated degree reduction retains the coarse cells of all active centers. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMAPlacedForkNetwork (β : Type*) (c : ℕ) where
  graph : QMAForkNetwork c
  cell : Fin graph.n → β
  aligned : QMAForkCellAligned graph.state.ports cell

namespace QMAPlacedForkNetwork
variable {β : Type*} {c : ℕ}

def centerCell (G : QMAPlacedForkNetwork β c) : Fin c → β := G.cell ∘ G.graph.state.ports.center

def next (G : QMAPlacedForkNetwork β c) : QMAPlacedForkNetwork β c where
  graph := G.graph.next
  cell := qmaForkCellNext G.graph.state.ports G.cell
  aligned := qmaForkCellNext_aligned G.graph.state.ports G.cell G.aligned

theorem next_centerCell (G : QMAPlacedForkNetwork β c) : G.next.centerCell = G.centerCell := by
  funext i
  exact qmaForkCellNext_old G.graph.state.ports G.cell (G.graph.state.ports.center i)

def iterate (G : QMAPlacedForkNetwork β c) : ℕ → QMAPlacedForkNetwork β c
  | 0 => G
  | k+1 => (G.iterate k).next

theorem iterate_graph (G : QMAPlacedForkNetwork β c) (k : ℕ) :
    (G.iterate k).graph = G.graph.iterate k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (G.iterate k).graph.next = (G.graph.iterate k).next
    rw [ih]

theorem iterate_centerCell (G : QMAPlacedForkNetwork β c) (k : ℕ) :
    (G.iterate k).centerCell = G.centerCell := by
  induction k with
  | zero => rfl
  | succ k ih => exact (G.iterate k).next_centerCell.trans ih

theorem next_cell_mass [DecidableEq β] (G : QMAPlacedForkNetwork β c) (D : ℕ)
    (hd : ∀ i, G.graph.degree i ≤ D) (x : β) :
    qmaCellMass G.next.cell x ≤ qmaCellMass G.cell x+2*D*qmaCellMass G.centerCell x :=
  qmaForkCellNext_mass_le G.graph.state.ports G.cell D hd x

theorem iterate_cell_mass [DecidableEq β] (G : QMAPlacedForkNetwork β c) (D : ℕ)
    (hd : ∀ i, G.graph.degree i ≤ D) (k : ℕ) (x : β) :
    qmaCellMass (G.iterate k).cell x ≤ qmaCellMass G.cell x+2*k*D*qmaCellMass G.centerCell x := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hd' : ∀ i, (G.iterate k).graph.degree i ≤ D := by
      rw [G.iterate_graph]
      intro i
      exact ((G.graph).iterate_degree_le k i).trans (hd i)
    have hs := (G.iterate k).next_cell_mass D hd' x
    rw [G.iterate_centerCell] at hs
    change qmaCellMass (G.iterate k).next.cell x ≤ _
    calc
      _ ≤ qmaCellMass (G.iterate k).cell x+2*D*qmaCellMass G.centerCell x := hs
      _ ≤ (qmaCellMass G.cell x+2*k*D*qmaCellMass G.centerCell x)+
          2*D*qmaCellMass G.centerCell x := Nat.add_le_add_right ih _
      _ = _ := by ring

end QMAPlacedForkNetwork
end ContinuumCoulomb

end

end OAI
