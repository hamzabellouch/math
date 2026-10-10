import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialModel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalSupported

namespace OAI

/-! Placing a mediator at its source term's anchor preserves the spatial support bound. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
def qmaMediatorCell {rows width : ℕ} (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) : ι ⊕ κ → QMAGridCell rows width :=
  Sum.elim cell anchor

theorem qmaMediatorSupport_geometry {rows width : ℕ} (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) (S : Finset ι) (e : κ)
    (hS : ∀ i ∈ S, QMAGridCellsNear (cell i) (anchor e))
    (q : ι ⊕ κ) (hq : q ∈ qmaMediatorSupport S e) :
    QMAGridCellsNear (qmaMediatorCell cell anchor q) (anchor e) := by
  cases q with
  | inl i =>
    apply hS
    simpa [qmaMediatorSupport] using hq
  | inr j =>
    have he : j = e := by simpa [qmaMediatorSupport] using hq
    subst j
    exact qmaGridCellsNear_refl _

end ContinuumCoulomb

end

end OAI
