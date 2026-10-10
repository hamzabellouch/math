import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkLocality
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkInitialCells

namespace OAI

/-! The initial subdivision preserves the original edge locality relation. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

theorem qmaSubdivisionPlaced_backgroundLocal {n m : ℕ} {β : Type*}
    (left right : Fin m → Fin n) (cell : Fin n → β) (R : β → β → Prop)
    (h : ∀ e, R (cell (left e)) (cell (right e))) :
    (qmaSubdivisionPlaced left right cell).BackgroundLocal R := by
  intro e
  change Fin m at e
  change R (qmaSubdivisionCell left right cell (fresh n m e 0))
    (qmaSubdivisionCell left right cell (fresh n m e 1))
  rw [qmaSubdivisionCell_fresh,qmaSubdivisionCell_fresh]
  simpa [qmaOriginalEndpoint] using h e

theorem qmaSubdivisionPlaced_full_local {n m : ℕ} {β : Type*}
    (left right : Fin m → Fin n) (cell : Fin n → β) (R : β → β → Prop)
    (hr : ∀ x, R x x) (h : ∀ e, R (cell (left e)) (cell (right e))) (k : ℕ) :
    let G := (qmaSubdivisionPlaced left right cell).iterate k
    ∀ e, R (G.cell (G.graph.state.fullLeft e)) (G.cell (G.graph.state.fullRight e)) := by
  intro G
  exact G.full_local R hr ((qmaSubdivisionPlaced left right cell).iterate_backgroundLocal R hr
    (qmaSubdivisionPlaced_backgroundLocal left right cell R h) k)

end ContinuumCoulomb

end

end OAI
