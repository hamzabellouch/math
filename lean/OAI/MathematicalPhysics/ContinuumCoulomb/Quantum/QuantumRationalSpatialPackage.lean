import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalFork
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPlaced
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAnchorDensity

namespace OAI

/-! Package the rational degree-three graph with its proved coarse-grid placement. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaDegreeThreeSpatialModel {ν : Type} [Fintype ν] {n rows width A : ℕ}
    (left right : ν → Fin n) (distinct : ∀ e, left e ≠ right e)
    (weight : ν → ℚ) (constant : ℚ)
    (cell : Fin n → QMAGridCell rows width) (anchor : ν → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A)
    (hd : ∀ v, qmaGraphDegree left right v ≤ 3)
    (hl : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e) ∧
      QMAGridCellsNear (cell (right e)) (anchor e)) : QMASpatialExchangeModel A (27*A) where
  n := n
  Term := ν
  left := left
  right := right
  distinct := distinct
  weight := weight
  constant := constant
  rows := rows
  width := width
  cell := cell
  anchor := anchor
  geometry := hl
  qubitDensity := hc
  termDensity := by
    intro p
    have h := qmaAnchor_density left right cell anchor (fun e => (hl e).1) hc hd p
    simpa only [show 9*A*3 = 27*A by omega] using h

theorem qmaRationalSpatialPackage {c rows width A : ℕ} (G : QMARationalForkNetwork c)
    (cell : Fin G.graph.n → QMAGridCell rows width)
    (hc : ∀ p, qmaCellMass cell p ≤ A)
    (hd : ∀ v, qmaGraphDegree G.graph.state.fullLeft G.graph.state.fullRight v ≤ 3)
    (hl : ∀ e, ∃ a : QMAGridCell rows width,
      QMAGridCellsNear (cell (G.graph.state.fullLeft e)) a ∧
        QMAGridCellsNear (cell (G.graph.state.fullRight e)) a) :
    ∃ M : QMASpatialExchangeModel A (27*A),
      M.rows = rows ∧ M.width = width ∧ M.n = G.graph.n ∧ M.energy = G.real.energy ∧
        ∀ v, qmaGraphDegree M.left M.right v ≤ 3 := by
  let anchor := fun e => Classical.choose (hl e)
  have hg (e) := Classical.choose_spec (hl e)
  have hc' : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A := by
    intro p
    simpa [qmaCellMass] using hc p
  let M := qmaDegreeThreeSpatialModel G.graph.state.fullLeft G.graph.state.fullRight
    G.graph.state.full_distinct (Sum.elim G.weight G.active) G.constant cell anchor hc' hd hg
  refine ⟨M,rfl,rfl,rfl,?_,hd⟩
  change MediatorGraph.normalizedBottom
    (qmaExchangeMatrix G.graph.state.fullLeft G.graph.state.fullRight
      (fun e => ((Sum.elim G.weight G.active e : ℚ):ℝ)) (G.constant:ℝ)) = _
  congr 2
  funext e
  cases e <;> rfl

theorem qmaRationalPlacedPackage {c rows width A : ℕ} (G : QMARationalForkNetwork c)
    (P : QMAPlacedForkNetwork (QMAGridCell rows width) c) (heq : G.graph = P.graph)
    (hc : ∀ p, qmaCellMass P.cell p ≤ A)
    (hd : ∀ v, qmaGraphDegree P.graph.state.fullLeft P.graph.state.fullRight v ≤ 3)
    (hl : ∀ e, ∃ a : QMAGridCell rows width,
      QMAGridCellsNear (P.cell (P.graph.state.fullLeft e)) a ∧
        QMAGridCellsNear (P.cell (P.graph.state.fullRight e)) a) :
    ∃ M : QMASpatialExchangeModel A (27*A),
      M.rows = rows ∧ M.width = width ∧ M.n = G.graph.n ∧ M.energy = G.real.energy ∧
        ∀ v, qmaGraphDegree M.left M.right v ≤ 3 := by
  rcases G with ⟨gg,w,J,t⟩
  rcases P with ⟨pg,cell,aligned⟩
  dsimp only at heq hc hd hl ⊢
  subst pg
  exact qmaRationalSpatialPackage ⟨gg,w,J,t⟩ cell hc hd hl

end ContinuumCoulomb

end

end OAI
