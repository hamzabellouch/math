import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawIncidence
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryFork
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListFinalDegree

namespace OAI

/-! A fixed degree bound for the literal raw history output. Consequently a
constant number of literal fork rounds suffices. -/

noncomputable section
namespace ContinuumCoulomb
open QuantumOrderedIncidence QuantumRawIncidence QuantumOrderedLabelTable
open scoped Classical

namespace QuantumOrderedLabelCompile

theorem output_degree {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {n m D : ℕ}
    (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    (hD : 1 ≤ D) (hinc : Bounded xs D) (N v : ℕ)
    (hv : v<qubitCount (N,n,table e (index q) xs w J)) :
    QuantumForkList.degree (output (N,n,table e (index q) xs w J)).1 v ≤
      6+22*(12544*D) := by
  rw [output_table q e xs w J hlen hdup N]
  have hb := numbered_bound (qubits6 q e) (terms6 e) (finalSites xs w)
    (complete_bound xs w hlen hD hinc)
  apply raw_degree N _ _ _ hb v
  rw [qubitCount_table] at hv
  change v<finalCount n m*4
  rw [finalCount_eq]
  omega

end QuantumOrderedLabelCompile

namespace QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumForkList

def historyDegree : ℕ := 6+22*29595009024

theorem sparse_history_degree (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ)
    (v : Fin (historyQubits (qmaSparseCircuit c) hT N)) :
    degree (historyOutput (qmaSparseCircuit c) hT N).1 v.val ≤ historyDegree := by
  let b := qmaSparseCircuit c
  let k := QuantumAlgebraicHistory.samplePrecision b N
  have hi : historyInput b hT N =
      (N,qubitCount b,table (sourceTerms b hT) (index (qubits b))
        (fun p : Term b => QuantumOrderedSupport.sites b hT p.1)
        (sourceWord b hT) (sampledWeight k b hT)) := by
    unfold historyInput
    rw [sourceEntries_table]
  have h := QuantumOrderedLabelCompile.output_degree (qubits b) (sourceTerms b hT)
    (fun p : Term b => QuantumOrderedSupport.sites b hT p.1)
    (sourceWord b hT) (sampledWeight k b hT)
    (fun p => QuantumOrderedSupport.sites_length b hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup b hT p.1)
    (by decide : 1 ≤ 2359296) (QuantumHistoryIncidence.sparse_padded_bound c hc hT hne)
    N v.val (by simpa only [historyQubits,← hi] using v.isLt)
  have hd : 6+22*(12544*2359296)=historyDegree := by norm_num [historyDegree]
  rw [hd] at h
  change degree (QuantumOrderedLabelCompile.output (historyInput b hT N)).1 v.val ≤
    historyDegree
  rw [hi]
  exact h

theorem sparse_fork_degree_three (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ)
    (v : Fin (forkState (qmaSparseCircuit c) hT N historyDegree).1) :
    degree ((forkState (qmaSparseCircuit c) hT N historyDegree).2.1 ++
      activeBonds (forkState (qmaSparseCircuit c) hT N historyDegree).2.2.2) v.val ≤ 3 := by
  exact initial_iterate_full_degree_of_bound _ _
    (fun b hb => (history_valid (qmaSparseCircuit c) hT N b hb).2.2) _ _ _
    (sparse_history_degree c hc hT hne N) v

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
