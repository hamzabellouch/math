import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialAccuracy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelEnergy

namespace OAI

/-! The actual history compiler produces a bounded loop-free exchange list.
Its initial subdivision and ordered fork rounds preserve the full-space
ground energy with the accumulated explicit error. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph QuantumRawExchange
open scoped BigOperators Classical

namespace QuantumOrderedLabelCompile
open QuantumOrderedLabelTable

theorem output_valid {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (output (N,n,table e (index q) xs w J)).1) :
    b.1 < qubitCount (N,n,table e (index q) xs w J) ∧
      b.2.1 < qubitCount (N,n,table e (index q) xs w J) ∧ b.1 ≠ b.2.1 := by
  rw [output_table q e xs w J hlen hx N] at hb
  have hv := QuantumOrderedRawBlock.output_valid N
    (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
    (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
    (fun i => finalCoefficient J N (terms6 e i)) b hb
  have hn : qubitCount (N,n,table e (index q) xs w J)=finalCount n m*4 := by
    rw [qubitCount_table,finalCount_eq]
    omega
  simpa only [hn,finalCount] using hv

end QuantumOrderedLabelCompile

namespace QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumForkList

theorem history_valid (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (historyOutput c hT N).1) :
    b.1 < historyQubits c hT N ∧ b.2.1 < historyQubits c hT N ∧ b.1 ≠ b.2.1 := by
  let k := QuantumAlgebraicHistory.samplePrecision c N
  have hi : historyInput c hT N =
      (N,qubitCount c,QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (qubits c))
        (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT)) := by
    unfold historyInput
    rw [sourceEntries_table]
  unfold historyOutput at hb
  rw [hi] at hb
  have hv := QuantumOrderedLabelCompile.output_valid (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
    (sourceWord c hT) (sampledWeight k c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1) N b hb
  simpa only [historyQubits,hi] using hv

def forkState (c : QMACircuit) (hT : 0 < c.gates.length) (N D : ℕ) : State :=
  iterate (N:ℚ) D (initial (historyQubits c hT N) (historyOutput c hT N).1
    (historyOutput c hT N).2 (N:ℚ))

theorem fork_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) (D : ℕ) :
    |normalizedBottom (matrix (forkState c hT N D))-(qmaOrderedHistoryModel c hT).energy| ≤
      ((D:ℝ)+10)/(N:ℝ) := by
  have hb : SourceBondLists.bounded (historyQubits c hT N) (historyOutput c hT N).1 :=
    fun b hb => ⟨(history_valid c hT N b hb).1,(history_valid c hT N b hb).2.1⟩
  have hn : ∀ b ∈ (historyOutput c hT N).1, b.1 ≠ b.2.1 :=
    fun b hb => (history_valid c hT N b hb).2.2
  have he := initial_iterated_accuracy (historyQubits c hT N) (historyOutput c hT N).1
    hb hn (historyOutput c hT N).2 (N:ℚ) (by exact_mod_cast hN) D
  have hh := history_accuracy c hT N hN
  have he' : |normalizedBottom (matrix (forkState c hT N D))-
      normalizedBottom (rawMatrix (historyQubits c hT N) (historyOutput c hT N))| ≤
        ((D:ℝ)+1)/(N:ℝ) := by
    have hcast : ((N:ℚ):ℝ)=(N:ℝ) := by norm_cast
    rw [hcast] at he
    exact he
  exact (abs_sub_le _ _ _).trans ((add_le_add he' hh).trans_eq (by ring))

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
