import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryCellProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedOutputSpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryOutputBounds

namespace OAI

/-! The computed cell array has the exact physical-spin order of the raw
history compiler, including all six mediator layers and the four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumOrderedSourceIndex
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete

theorem map_cell6 {ι κ C D : Type} (f : C → D) (cell : ι → C) (anchor : κ → C) :
    cell6 (f ∘ cell) (f ∘ anchor)=f ∘ cell6 cell anchor := by
  funext q
  rcases q with q | q
  · rcases q with q | q
    · rcases q with q | q
      · rcases q with q | q
        · rcases q with q | q
          · rcases q with q | q <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

def rawCells (c : QMACircuit) : List (ℕ × ℕ) := QuantumOrderedRawCells.value (value c)

noncomputable opaque rawCellsProgram : Procedure circuitCode
    (listCode QuantumRouteCode.pairCode) rawCells :=
  QuantumOrderedRawCells.program.comp valueProgram

theorem rawCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    rawCells c=List.ofFn (fun i : Fin
      (finalCount (qubitCount (qmaSparseCircuit c))
        (referenceCount (qmaSparseCircuit c)*patternCount)*4) =>
      encodeCell (QuantumOrderedOutputSpatial.physicalCell
        (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) i.val)) := by
  rw [rawCells,value_actual c hT,QuantumOrderedRawCells.value_table]
  apply congrArg List.ofFn
  funext i
  rw [QuantumOrderedOutputSpatial.physicalCell,
    QuantumRawCellLocality.blockCell_fin]
  change cell6 (encodeCell ∘ qmaOrderedQubitCell c hT)
      (encodeCell ∘ (fun p => qmaOrderedTermCell c hT p.1))
      (qubits6 (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (finProdFinEquiv.symm i).1)=_
  rw [map_cell6]
  simp only [Function.comp_apply,QuantumOrderedOutputSpatial.logicalCell,qmaFourBlockCell]

theorem rawCells_length (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (N : ℕ) :
    (rawCells c).length=QuantumPaddedLabelProgram.historyQubits
      (qmaSparseCircuit c) hT N := by
  rw [rawCells_actual c hT,List.length_ofFn,
    QuantumPaddedLabelProgram.historyQubits_eq,finalCount_eq]
  simp only [termCount]
  omega

theorem rawCells_get (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell (QuantumOrderedOutputSpatial.physicalCell
      (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j) := by
  simp only [rawCells_actual c hT,List.getElem_ofFn]

theorem input_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ) :
    (QuantumHistorySpatial.input c hc hT hne N).cell j=
      QuantumOrderedOutputSpatial.physicalCell (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j := by
  simp only [QuantumHistorySpatial.input,QuantumOrderedOutputSpatial.input,id]

theorem rawCells_input_length (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    (rawCells c).length=(QuantumHistorySpatial.input c hc hT hne N).n := by
  rw [QuantumHistorySpatial.input_n]
  exact rawCells_length c hT N

theorem rawCells_input_get (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell ((QuantumHistorySpatial.input c hc hT hne N).cell j) := by
  rw [input_cell]
  exact rawCells_get c hT j hj

noncomputable def rawCertificate : Turing.TM2ComputableInPolyTime circuitCode
    (listCode QuantumRouteCode.pairCode) rawCells := rawCellsProgram.toTM2

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
