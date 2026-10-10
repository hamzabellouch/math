import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySpatialProgram

namespace OAI

/-! The completed history input is fed to the fixed number of fork rounds,
then to the literal endpoint/anchor array constructor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram

def gridOutput (x : Input) : QuantumForkGridProgram.Cells :=
  QuantumForkGridProgram.output QuantumPaddedLabelProgram.historyDegree (prepared x)

noncomputable opaque gridProgram : Procedure inputCode
    QuantumForkGridProgram.cellsCode gridOutput :=
  (QuantumForkGridProgram.outputProgram QuantumPaddedLabelProgram.historyDegree).comp preparedProgram

def routing (x : Input) : QuantumRoutingInputProgram.Data :=
  QuantumForkRoutingData.value (gridOutput x)

noncomputable opaque routingProgram : Procedure inputCode
    QuantumRoutingInputProgram.dataCode routing :=
  QuantumForkRoutingData.program.comp gridProgram

theorem gridOutput_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    gridOutput (N,c)=
      ((QuantumHistorySpatial.input c hc hT hne N).state,
        List.ofFn (fun i : Fin (QuantumHistorySpatial.input c hc hT hne N).state.1 =>
          QuantumSpatialInputTape.coordinates
            ((QuantumHistorySpatial.input c hc hT hne N).cells i.val))) := by
  rw [gridOutput,prepared_actual c hc hT hne N]
  exact QuantumSpatialInputTape.output_eq (QuantumHistorySpatial.input c hc hT hne N)

theorem gridOutput_state (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    (gridOutput (N,c)).1=QuantumPaddedLabelProgram.forkState
      (qmaSparseCircuit c) hT N QuantumPaddedLabelProgram.historyDegree := by
  rw [gridOutput_actual c hc hT hne N,QuantumHistorySpatial.input_state]

theorem routing_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    routing (N,c)=QuantumRoutingInputProgram.actualData
      (QuantumHistorySpatial.model c hc hT hne N) (Equiv.refl _) := by
  rw [routing,gridOutput,prepared_actual c hc hT hne N]
  exact QuantumSpatialInputTape.routing_eq (QuantumHistorySpatial.input c hc hT hne N)

noncomputable def routingCertificate : Turing.TM2ComputableInPolyTime inputCode
    QuantumRoutingInputProgram.dataCode routing := routingProgram.toTM2

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
