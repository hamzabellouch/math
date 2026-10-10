import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryRoutingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPreparedLattice

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def precision (c : QMACircuit) : ℕ :=
  QuantumHistorySpatial.latticePrecision (qmaNonemptyCircuit c)

def time (c : QMACircuit) : ℕ := (qmaPreparedCircuit c).gates.length

noncomputable opaque timeProgram : Procedure circuitCode unaryCode time :=
  QuantumHistoryDescriptors.timeProgram.comp preparedCircuitProgram

noncomputable opaque precisionProgram : Procedure circuitCode unaryCode precision :=
  ((QuantumAlgebraicHistory.finalPrecisionProgram QuantumHistorySpatial.totalRounds).comp
    timeProgram).congrFun (by
      intro c
      simp only [precision,QuantumHistorySpatial.latticePrecision,
        QuantumAlgebraicHistory.finalPrecision,time,qmaPreparedCircuit,Function.comp_apply])

def scheduled (c : QMACircuit) : QuantumHistorySpatialProgram.Input :=
  (precision c,qmaNonemptyCircuit c)

noncomputable opaque scheduledProgram : Procedure circuitCode
    QuantumHistorySpatialProgram.inputCode scheduled :=
  precisionProgram.pair nonemptyProgram

def prepared (c : QMACircuit) : QuantumForkGridProgram.PreparedInput :=
  QuantumHistorySpatialProgram.prepared (scheduled c)

noncomputable opaque preparedProgram : Procedure circuitCode
    QuantumForkGridProgram.preparedCode prepared :=
  QuantumHistorySpatialProgram.preparedProgram.comp scheduledProgram

def grid (c : QMACircuit) : QuantumForkGridProgram.Cells :=
  QuantumHistorySpatialProgram.gridOutput (scheduled c)

noncomputable opaque gridProgram : Procedure circuitCode
    QuantumForkGridProgram.cellsCode grid :=
  QuantumHistorySpatialProgram.gridProgram.comp scheduledProgram

def routing (c : QMACircuit) : QuantumRoutingInputProgram.Data :=
  QuantumHistorySpatialProgram.routing (scheduled c)

noncomputable opaque routingProgram : Procedure circuitCode
    QuantumRoutingInputProgram.dataCode routing :=
  QuantumHistorySpatialProgram.routingProgram.comp scheduledProgram

def thresholds (c : QMACircuit) : ℚ × ℚ :=
  (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
    QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))

noncomputable opaque thresholdTimeProgram : Procedure circuitCode ratCode
    (fun c => ((time c+1:ℕ):ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp timeProgram))

noncomputable opaque lowerProgram : Procedure circuitCode ratCode
    (fun c => (thresholds c).1) := by
  let denominator := Procedure.ratMul.comp
    ((Procedure.constant circuitCode ratCode 20).pair thresholdTimeProgram)
  exact (Procedure.ratDiv.comp
    ((Procedure.constant circuitCode ratCode 7).pair denominator)).congrFun (by
      intro c
      simp only [thresholds,QuantumAlgebraicHistory.xzYesThreshold,time,
        Function.comp_apply,Nat.cast_add,Nat.cast_one])

noncomputable opaque upperProgram : Procedure circuitCode ratCode
    (fun c => (thresholds c).2) := by
  let denominator := Procedure.ratMul.comp
    ((Procedure.constant circuitCode ratCode 60).pair thresholdTimeProgram)
  exact (Procedure.ratDiv.comp
    ((Procedure.constant circuitCode ratCode 23).pair denominator)).congrFun (by
      intro c
      simp only [thresholds,QuantumAlgebraicHistory.xzNoThreshold,time,
        Function.comp_apply,Nat.cast_add,Nat.cast_one])

noncomputable opaque thresholdsProgram : Procedure circuitCode
    (prodCode ratCode ratCode) thresholds :=
  (lowerProgram.pair upperProgram).congrFun (by intro c; rfl)

abbrev FinalInput := (ℚ × QuantumForkGridProgram.PreparedInput) × (ℚ × ℚ)
def finalInputCode : FinalInput → List Bool :=
  prodCode (prodCode ratCode QuantumForkGridProgram.preparedCode) (prodCode ratCode ratCode)

def finalInput (c : QMACircuit) : FinalInput :=
  (((precision c:ℚ),prepared c),thresholds c)

noncomputable opaque rationalPrecisionProgram : Procedure circuitCode ratCode
    (fun c => (precision c:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp precisionProgram)

noncomputable opaque finalInputProgram : Procedure circuitCode finalInputCode finalInput :=
  (rationalPrecisionProgram.pair preparedProgram).pair thresholdsProgram

theorem precision_pos (c : QMACircuit) : 0<precision c :=
  QuantumAlgebraicHistory.finalPrecision_pos _ _

theorem thresholds_lt (c : QMACircuit) : (thresholds c).1<(thresholds c).2 :=
  QuantumAlgebraicHistory.xz_threshold_lt _

theorem thresholds_gap (c : QMACircuit) :
    (thresholds c).2-(thresholds c).1=1/(30*(time c+1:ℚ)) :=
  QuantumAlgebraicHistory.xz_threshold_gap _

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed) :
    prepared c=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)) :=
  QuantumHistorySpatialProgram.prepared_actual _ (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)

theorem routing_actual (c : QMACircuit) (hc : c.WellFormed) :
    routing c=QuantumRoutingInputProgram.actualData
      (QuantumHistorySpatial.model (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))
      (Equiv.refl _) :=
  QuantumHistorySpatialProgram.routing_actual _ (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)

theorem finalInput_actual (c : QMACircuit) (hc : c.WellFormed) :
    finalInput c=
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) := by
  rw [finalInput,prepared_actual c hc]
  rfl

noncomputable def certificate : Turing.TM2ComputableInPolyTime circuitCode
    finalInputCode finalInput := finalInputProgram.toTM2

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
