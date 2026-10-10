import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedModel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialTerms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceCongestion

namespace OAI

/-! All terms of the real reference model are localized in the actual clock grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridCellsNear_refl {rows width : ℕ} (p : QMAGridCell rows width) :
    QMAGridCellsNear p p := by
  unfold QMAGridCellsNear
  omega

theorem qmaGridCellsNear_symm {rows width : ℕ} {p q : QMAGridCell rows width}
    (h : QMAGridCellsNear p q) : QMAGridCellsNear q p :=
  ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

def qmaOrderedQubitCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕ QMACircuitQubit (qmaSparseCircuit c) →
      QMAGridCell (qmaNearestCircuit c).gates.length c.work :=
  Sum.elim (qmaOrderedSparseReferenceCell c hT) (qmaSparseQubitCell c hT)

def qmaOrderedTermCell (c : QMACircuit) (hT : 0 < (qmaSparseCircuit c).gates.length) :
    QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)) →
      QMAGridCell (qmaNearestCircuit c).gates.length c.work
  | .inl i => qmaOrderedSparseReferenceCell c hT i
  | .inr i => qmaOrderedSparseReferenceCell c hT i.castSucc

theorem qmaOrderedHistoryModel_spatial (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c)))
    (k : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1) ⊕ QMACircuitQubit (qmaSparseCircuit c))
    (hk : k ∈ (qmaOrderedHistoryModel (qmaSparseCircuit c) hT).sites a) :
    QMAGridCellsNear (qmaOrderedQubitCell c hT k) (qmaOrderedTermCell c hT a) := by
  change k ∈ qmaReferenceTermSites _ (qmaOrderedHistorySites (qmaSparseCircuit c) hT) a at hk
  cases a with
  | inl i =>
    cases k with
    | inl j =>
      have he : j = i := by
        simpa [qmaReferenceTermSites,qmaDistributedRebitSites] using hk
      subst j
      exact qmaGridCellsNear_refl _
    | inr k =>
      have hk' : k ∈ qmaOrderedHistorySites (qmaSparseCircuit c) hT i := by
        simpa [qmaReferenceTermSites,qmaDistributedRebitSites] using hk
      exact qmaSparseHistoryTerm_cell c hc hT hne _ k hk'
  | inr i =>
    have hk' : k = .inl i.castSucc ∨ k = .inl i.succ := by
      simpa [qmaReferenceTermSites,qmaReferenceEdgeSites] using hk
    rcases hk' with rfl | rfl
    · exact qmaGridCellsNear_refl _
    · exact qmaGridCellsNear_symm (qmaOrderedSparseReferenceCell_near c hT i)

end ContinuumCoulomb

end

end OAI
