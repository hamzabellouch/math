import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryRawCells
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialInputTape

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

abbrev Input := QuantumHistoryPrecisionProgram.Input
abbrev inputCode := QuantumHistoryPrecisionProgram.inputCode

def sparseInput (x : Input) : Input := (x.1,qmaSparseCircuit x.2)

noncomputable opaque sparseInputProgram : Procedure inputCode inputCode sparseInput :=
  inverseErrorProgram.pair (sparseCircuitProgram.comp circuitProgram)

def initialInput (x : Input) : QuantumForkList.InitialInput :=
  ((x.1:ℚ),physicalQubits (sparseInput x),output (sparseInput x))

noncomputable opaque initialInputProgram : Procedure inputCode
    QuantumForkList.initialInputCode initialInput :=
  (Procedure.natToRat.comp (Procedure.unaryToBits.comp inverseErrorProgram)).pair
    ((physicalQubitsProgram.comp sparseInputProgram).pair
      (outputProgram.comp sparseInputProgram))

def prepared (x : Input) : QuantumForkGridProgram.PreparedInput :=
  (initialInput x,QuantumHistoryCells.rawCells x.2)

noncomputable opaque cellsProgram : Procedure inputCode
    (listCode QuantumRouteCode.pairCode) (QuantumHistoryCells.rawCells ∘ Prod.snd) :=
  @Procedure.comp Input QMACircuit (List QuantumRouteCode.Pair)
    inputCode circuitCode (listCode QuantumRouteCode.pairCode)
    Prod.snd QuantumHistoryCells.rawCells QuantumHistoryCells.rawCellsProgram circuitProgram

noncomputable opaque preparedProgram : Procedure inputCode
    QuantumForkGridProgram.preparedCode prepared := by
  refine (@Procedure.pair Input QuantumForkList.InitialInput (List QuantumRouteCode.Pair)
    inputCode QuantumForkList.initialInputCode (listCode QuantumRouteCode.pairCode)
    initialInput (QuantumHistoryCells.rawCells ∘ Prod.snd)
    initialInputProgram cellsProgram).congrFun ?_
  intro x
  simp only [prepared,Function.comp_apply]

theorem rawCells_input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    QuantumHistoryCells.rawCells c=List.ofFn
      (fun i : Fin (QuantumHistorySpatial.input c hc hT hne N).n =>
        QuantumSpatialInputTape.coordinates
          ((QuantumHistorySpatial.input c hc hT hne N).cell i.val)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact QuantumHistoryCells.rawCells_input_length c hc hT hne N
  · intro j hj _
    rw [List.getElem_ofFn]
    simpa only [QuantumSpatialInputTape.coordinates,QuantumHistoryCells.encodeCell] using
      QuantumHistoryCells.rawCells_input_get c hc hT hne N j hj

theorem initialInput_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    initialInput (N,c)=
      ((QuantumHistorySpatial.input c hc hT hne N).precision,
        (QuantumHistorySpatial.input c hc hT hne N).n,
        (QuantumHistorySpatial.input c hc hT hne N).bonds,
        (QuantumHistorySpatial.input c hc hT hne N).constant) := by
  rw [initialInput,sparseInput,physicalQubits_actual N (qmaSparseCircuit c) hT,
    output_actual N (qmaSparseCircuit c) hT,QuantumHistorySpatial.input_n,
    QuantumHistorySpatial.input_bonds,QuantumHistorySpatial.input_constant]
  rfl

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    prepared (N,c)=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input c hc hT hne N) := by
  unfold prepared QuantumSpatialInputTape.input
  rw [initialInput_actual c hc hT hne N,rawCells_input c hc hT hne N]

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    QuantumForkGridProgram.preparedCode prepared := preparedProgram.toTM2

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
