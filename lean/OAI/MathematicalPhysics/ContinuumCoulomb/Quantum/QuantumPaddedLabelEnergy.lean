import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelEnergy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelTable

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

def historyInput (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    QuantumOrderedLabelFamily.Input :=
  (N,qubitCount c,sourceEntries (QuantumAlgebraicHistory.samplePrecision c N) c hT)

def historyOutput (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :=
  QuantumOrderedLabelCompile.output (historyInput c hT N)

def historyQubits (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : ℕ :=
  QuantumOrderedLabelCompile.qubitCount (historyInput c hT N)

theorem historyQubits_eq (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    historyQubits c hT N=4*(qubitCount c+3717*termCount c) := by
  unfold historyQubits historyInput QuantumOrderedLabelCompile.qubitCount
  rw [QuantumOrderedLabelPipeline.output_qubits,sourceEntries_length]

theorem history_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom
        (QuantumRawExchange.rawMatrix (historyQubits c hT N) (historyOutput c hT N))-
      (qmaOrderedHistoryModel c hT).energy| ≤ 9/(N:ℝ) := by
  let k := QuantumAlgebraicHistory.samplePrecision c N
  have hc (p : Term c) : qmaPauliSupport (sourceWord c hT p) ⊆
      (QuantumOrderedSupport.sites c hT p.1).toFinset := by
    rw [QuantumOrderedSupport.sites_finset]
    exact support c hT p
  have h₁ := QuantumOrderedLabelCompile.output_accuracy (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
    (sourceWord c hT) (sampledWeight k c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1) hc (even c hT) N hN
  have hi : historyInput c hT N =
      (N,qubitCount c,QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (qubits c))
        (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT)) := by
    unfold historyInput
    rw [sourceEntries_table]
  rw [← hi] at h₁
  have h₂ := sampled_accuracy c hT N hN
  exact (abs_sub_le _ _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
