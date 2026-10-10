import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumNearestProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridLocality
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary

namespace OAI

/-! The complete sweep is a finite table of the literal row stages, followed
by concatenation. It agrees with the recursive physical circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def readGate (gs : List QMAGate) (i : ℕ) : QMAGate :=
  (gs.drop i).headD (.hadamard 0)

def sweepList (rows width start : ℕ) (gs : List QMAGate) : List QMAGate :=
  (List.range gs.length).flatMap (fun i => rowStage rows width (start+i) (readGate gs i))

theorem sweepList_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepList rows width start (g::gs)=
      rowStage rows width start g++sweepList rows width (start+1) gs := by
  simp only [sweepList,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,
    Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowStage rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowStage rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

theorem sweepList_eq (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    qmaSweepCircuitFrom rows width start gs h=sweepList rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepList_cons]
    simp only [qmaSweepCircuitFrom]
    rw [rowStage_eq rows width start hs,ih]

noncomputable def gateLengthProgram : Procedure (listCode gateCode) unaryCode List.length :=
  Procedure.boundedUnary (Procedure.listLength gateCode (.hadamard 0))
    (Procedure.length.precompose (listCode gateCode)) (list_length_le_code gateCode)

abbrev SweepInput := ℕ × (ℕ × (ℕ × List QMAGate))
def sweepInputCode : SweepInput → List Bool :=
  prodCode Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))

noncomputable def sweepListProgram : Procedure sweepInputCode (listCode gateCode)
    (fun x => sweepList x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let rest := Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))
  let tail := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp rest
  let gates := (Procedure.second Nat.bits (listCode gateCode)).comp tail
  let context := Procedure.second unaryCode sweepInputCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode sweepInputCode)
  let rows := (Procedure.first Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))).comp context
  let cr := (Procedure.second Nat.bits (prodCode unaryCode (prodCode Nat.bits (listCode gateCode)))).comp context
  let width := (Procedure.first unaryCode (prodCode Nat.bits (listCode gateCode))).comp cr
  let ct := (Procedure.second unaryCode (prodCode Nat.bits (listCode gateCode))).comp cr
  let start := (Procedure.first Nat.bits (listCode gateCode)).comp ct
  let gs := (Procedure.second Nat.bits (listCode gateCode)).comp ct
  let gate := (Procedure.listGet gateCode (.hadamard 0)).comp (index.pair gs)
  let stage := rowStageProgram.comp
    (rows.pair (width.pair ((Procedure.binaryAdd.comp (start.pair index)).pair gate)))
  let table := Procedure.tabulate (f := fun (x : SweepInput) i =>
    rowStage x.1 x.2.1 (x.2.2.1+i) (readGate x.2.2.2 i)) [] stage
  exact ((QuantumRawExchange.flattenProgram gateCode (.hadamard 0)).comp
    (table.comp ((gateLengthProgram.comp gates).pair
      (Procedure.identity sweepInputCode)))).congrFun (by
        intro x
        simp only [Function.comp_apply,id_eq,sweepList,List.flatMap_def])

noncomputable def sweepCircuitProgram : Procedure circuitCode circuitCode qmaSweepCircuit := by
  let rows := gateLengthProgram.comp gatesProgram
  let count := Procedure.unaryAdd.comp
    (workProgram.pair (Procedure.unaryMul.comp
      (rows.pair (Procedure.unarySuccessor.comp workProgram))))
  let gates := sweepListProgram.comp ((Procedure.unaryToBits.comp rows).pair
    (workProgram.pair ((Procedure.constant circuitCode Nat.bits 0).pair gatesProgram)))
  exact (count.pair (witnessProgram.pair gates)).result (by
    intro c
    change prodCode unaryCode (prodCode unaryCode (listCode gateCode))
      (qmaGridWork c.gates.length c.work,c.witness,
        sweepList c.gates.length c.work 0 c.gates)=
      prodCode unaryCode (prodCode unaryCode (listCode gateCode))
        (qmaGridWork c.gates.length c.work,c.witness,
          qmaSweepCircuitFrom c.gates.length c.work 0 c.gates _)
    rw [sweepList_eq])

noncomputable def sparseCircuitProgram : Procedure circuitCode circuitCode qmaSparseCircuit :=
  sweepCircuitProgram.comp nearestCircuitProgram

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
