import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialOccupancy

namespace OAI

/-! Spatial data for the actual finite real Hamiltonian, including bounded density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

structure QMASpatialModel (d A B : ℕ) extends QMARealLocalModel d where
  rows : ℕ
  width : ℕ
  cell : Q → QMAGridCell rows width
  anchor : Term → QMAGridCell rows width
  geometry : ∀ a, ∀ q ∈ sites a, QMAGridCellsNear (cell q) (anchor a)
  qubitDensity : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A
  termDensity : ∀ p, (Finset.univ.filter (fun a => anchor a = p)).card ≤ B

def qmaSpatialHistoryModel (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) : QMASpatialModel 6 45 64 where
  toQMARealLocalModel := qmaOrderedHistoryModel (qmaSparseCircuit c) hT
  rows := (qmaNearestCircuit c).gates.length
  width := c.work
  cell := qmaOrderedQubitCell c hT
  anchor := qmaOrderedTermCell c hT
  geometry := qmaOrderedHistoryModel_spatial c hc hT hne
  qubitDensity := qmaOrderedQubitCell_fiber_card c hT hne
  termDensity := qmaOrderedTermCell_fiber_card c hT hne

end ContinuumCoulomb

end

end OAI
