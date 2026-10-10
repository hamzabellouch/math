import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateCode
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSupport
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListMapWith
import OAI.Computability.QuantumFactoring.BitStackListLength

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev GateInput := ℕ × QMAGate
def gateInputCode : GateInput → List Bool := prodCode Nat.bits gateCode

def gateLabels (x : GateInput) : List ℕ :=
  let left := gateLeft x.2 % (x.1+1)
  let right := gateRight x.2 % (x.1+1)
  if gateTag x.2=2 then [left,right] else [left]

noncomputable def gateLabelsProgram :
    Procedure gateInputCode (listCode Nat.bits) gateLabels := by
  let work := Procedure.first Nat.bits gateCode
  let gate := Procedure.second Nat.bits gateCode
  let modulus := Procedure.successor.comp work
  let left := Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair modulus)
  let right := Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair modulus)
  let nil := Procedure.constant gateInputCode (listCode Nat.bits) []
  let single := (Procedure.listCons Nat.bits).comp (left.pair nil)
  let pair := (Procedure.listCons Nat.bits).comp
    (left.pair ((Procedure.listCons Nat.bits).comp (right.pair nil)))
  let isCnot := Procedure.binaryEq.comp ((gateTagProgram.comp gate).pair
    (Procedure.constant gateInputCode Nat.bits 2))
  exact (Procedure.conditional isCnot pair single).congrFun (by
    intro x
    simp only [Function.comp_apply,gateLabels,decide_eq_true_eq])

theorem gateLabels_actual (work : ℕ) (g : QMAGate) :
    gateLabels (work,g)=(QuantumOrderedSupport.gateSites work g).map Fin.val := by
  cases g <;> rfl

def distributedNumber (c : QMACircuit) : QMACircuitQubit c → ℕ :=
  Sum.elim Fin.val (fun i => c.gates.length+2+i.val)

abbrev Input := QMACircuit × ℕ
def inputCode : Input → List Bool := prodCode circuitCode Nat.bits

def gateAt (x : Input) : QMAGate := x.1.gates.getD x.2 (.hadamard 0)

def propagationLabels (x : Input) : List ℕ :=
  [x.2,x.2+1,x.2+2] ++
    (gateLabels (x.1.work,gateAt x)).map (fun i => x.1.gates.length+2+i)

noncomputable def gateAtProgram : Procedure inputCode gateCode gateAt := by
  let circuit := Procedure.first circuitCode Nat.bits
  let index := Procedure.second circuitCode Nat.bits
  exact ((Procedure.listGet gateCode (.hadamard 0)).comp
    (index.pair (gatesProgram.comp circuit))).congrFun (by
      intro x
      simp only [Function.comp_apply,gateAt,List.headD_eq_head?_getD,
        List.head?_drop,List.getD_eq_getElem?_getD])

noncomputable def propagationLabelsProgram :
    Procedure inputCode (listCode Nat.bits) propagationLabels := by
  let circuit := Procedure.first circuitCode Nat.bits
  let index := Procedure.second circuitCode Nat.bits
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let gates := gatesProgram.comp circuit
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength gateCode (.hadamard 0)).comp gates)
  let offset := Procedure.binaryAdd.comp (count.pair (Procedure.constant inputCode Nat.bits 2))
  let nil := Procedure.constant inputCode (listCode Nat.bits) []
  let one := Procedure.successor.comp index
  let two := Procedure.successor.comp one
  let clock := (Procedure.listCons Nat.bits).comp
    (index.pair ((Procedure.listCons Nat.bits).comp
      (one.pair ((Procedure.listCons Nat.bits).comp (two.pair nil)))))
  let gateSites := gateLabelsProgram.comp (work.pair gateAtProgram)
  let translated := (Procedure.listMapWith (f := fun a b : ℕ => a+b) 0 0
    Procedure.binaryAdd).comp (offset.pair gateSites)
  exact (Procedure.listAppend Nat.bits 0).comp (clock.pair translated)

theorem propagationLabels_actual (c : QMACircuit) (t : Fin c.gates.length) :
    propagationLabels (c,t.val)=
      (QuantumOrderedSupport.propagationSites c t).map (distributedNumber c) := by
  simp only [propagationLabels,gateAt,gateLabels_actual,
    QuantumOrderedSupport.propagationSites,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,distributedNumber,qmaClockLeft,qmaClockMiddle,qmaClockRight]
  rfl

end ContinuumCoulomb.QuantumHistorySiteProgram

end

end OAI
