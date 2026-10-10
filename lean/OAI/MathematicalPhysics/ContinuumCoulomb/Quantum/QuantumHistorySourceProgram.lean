import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryPreparedProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFinalRoutingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPreparedVerifier

namespace OAI

/-! The complete literal circuit-to-source map, including nonempty padding,
sampling precision, fork and route programs, and rational thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode BinaryEncoding

def value : QMACircuit → BinaryHeisenberg :=
  QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
    QuantumPaddedLabelProgram.historyDegree ∘ QuantumHistoryPreparedProgram.finalInput

theorem inputCode_eq : QuantumHistoryPreparedProgram.finalInputCode=
    QuantumFinalRoutingProgram.inputCode := rfl

private noncomputable opaque inputProgram : Procedure circuitCode
    QuantumFinalRoutingProgram.inputCode QuantumHistoryPreparedProgram.finalInput := by
  rw [← inputCode_eq]
  exact QuantumHistoryPreparedProgram.finalInputProgram

noncomputable opaque program : Procedure circuitCode binaryHeisenbergCodec.encode value :=
  @Procedure.comp QMACircuit QuantumFinalRoutingProgram.Input BinaryHeisenberg
    circuitCode QuantumFinalRoutingProgram.inputCode binaryHeisenbergCodec.encode
    QuantumHistoryPreparedProgram.finalInput
    (QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree)
    (QuantumFinalRoutingProgram.program QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree) inputProgram

theorem value_actual (c : QMACircuit) (hc : c.WellFormed) :
    value c=QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree
      (((QuantumHistoryPreparedProgram.precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c)
          (QuantumHistoryPreparedProgram.precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) :=
  congrArg (QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
    QuantumPaddedLabelProgram.historyDegree) (QuantumHistoryPreparedProgram.finalInput_actual c hc)

noncomputable def certificate : Turing.TM2ComputableInPolyTime circuitCode
    binaryHeisenbergCodec.encode value := program.toTM2

def fromVerifier (V : QuantumVerifier) : BitString → BinaryHeisenberg := value ∘ V.generate

noncomputable def fromVerifier_uniform (V : QuantumVerifier) :
    Turing.TM2ComputableInPolyTime (id : BitString → List Bool)
      binaryHeisenbergCodec.encode (fromVerifier V) :=
  TM2Composition.computable V.generateUnary certificate

theorem fromVerifier_actual (V : QuantumVerifier) (x : BitString) :
    fromVerifier V x=value (V.generate x) := rfl

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
