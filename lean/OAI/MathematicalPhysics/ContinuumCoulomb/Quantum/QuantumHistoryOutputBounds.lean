import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedOutputBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialInputBounds

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

def historyCoefficientBudget (c : QMACircuit) (N : ℕ) : ℕ :=
  QuantumOrderedLabelCompile.coefficientEnvelope (qubitCount c) (termCount c)
    (QuantumAlgebraicHistory.coefficientBudget c) N

theorem history_output_bound (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    |((historyOutput c hT N).2:ℝ)| ≤ historyCoefficientBudget c N ∧
      ∀ b ∈ (historyOutput c hT N).1, |(b.2.2:ℝ)| ≤ historyCoefficientBudget c N := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  exact QuantumOrderedLabelCompile.output_coefficients (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT)
    (sampledWeight (QuantumAlgebraicHistory.samplePrecision c N) c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1)
    (fun p => sampledWeight_bound _ c hT p) N

theorem input_bonds (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).bonds=(historyOutput (qmaSparseCircuit c) hT N).1 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_constant (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).constant=(historyOutput (qmaSparseCircuit c) hT N).2 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_n (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).n=historyQubits (qmaSparseCircuit c) hT N := by
  unfold historyQubits historyInput
  rw [sourceEntries_table]
  rfl

private theorem outputNat_one (n m B N : ℕ) : 1 ≤ QuantumRawExchange.outputNat n m B N := by
  dsimp only [QuantumRawExchange.outputNat]
  omega

theorem historyCoefficientBudget_one (c : QMACircuit) (N : ℕ) :
    1 ≤ historyCoefficientBudget c N := outputNat_one _ _ _ _

theorem model_coefficientBound (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (model c hc hT hne N).exchangeGraph.CoefficientBound
      (outputCoefficientNat (input c hc hT hne N).bonds.length historyDegree
        (historyCoefficientBudget (qmaSparseCircuit c) N) N) := by
  have hb := history_output_bound (qmaSparseCircuit c) hT N
  have hp : (input c hc hT hne N).precision=(N:ℚ) := rfl
  apply (input c hc hT hne N).model_nat_coefficientBound
    (by rw [hp]; exact_mod_cast Nat.zero_le N)
    (historyCoefficientBudget_one _ N)
    (by rw [hp,Rat.cast_natCast,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  · rw [input_constant]
    exact hb.1
  · rw [input_bonds]
    exact hb.2

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
