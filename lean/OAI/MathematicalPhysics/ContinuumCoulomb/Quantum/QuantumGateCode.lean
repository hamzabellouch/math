import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitCode

namespace OAI

/-! Literal constructors and coordinate selectors for the fixed H/T/CNOT
alphabet used by the nearest-neighbor circuit preprocessor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCircuitCode
open ExactQuantumFactoring.BitStackProgram

def gateTag : QMAGate → ℕ
  | .hadamard _ => 0
  | .phaseT _ => 1
  | .controlledNot _ _ => 2

def gateLeft : QMAGate → ℕ
  | .hadamard i => i
  | .phaseT i => i
  | .controlledNot i _ => i

def gateRight : QMAGate → ℕ
  | .hadamard i => i
  | .phaseT i => i
  | .controlledNot _ j => j

noncomputable def hadamardProgram : Procedure Nat.bits gateCode QMAGate.hadamard :=
  ((Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp
    (Procedure.sumLeft Nat.bits Nat.bits)).result (by intro i; rfl)

noncomputable def phaseProgram : Procedure Nat.bits gateCode QMAGate.phaseT :=
  ((Procedure.sumLeft (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).comp
    (Procedure.sumRight Nat.bits Nat.bits)).result (by intro i; rfl)

noncomputable def cnotProgram : Procedure (prodCode Nat.bits Nat.bits) gateCode
    (fun p => QMAGate.controlledNot p.1 p.2) :=
  (Procedure.sumRight (sumCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)).result
    (by intro p; rfl)

noncomputable def gateTagProgram : Procedure gateCode Nat.bits gateTag := by
  let h := Procedure.constant Nat.bits Nat.bits 0
  let t := Procedure.constant Nat.bits Nat.bits 1
  let c := Procedure.constant (prodCode Nat.bits Nat.bits) Nat.bits 2
  exact ((Procedure.casesSum (Procedure.casesSum h t) c).precompose qmaGateEquiv).congrFun
    (by intro g; cases g <;> rfl)

noncomputable def gateLeftProgram : Procedure gateCode Nat.bits gateLeft :=
  ((Procedure.casesSum (Procedure.casesSum (Procedure.identity Nat.bits) (Procedure.identity Nat.bits))
    (Procedure.first Nat.bits Nat.bits)).precompose qmaGateEquiv).congrFun
      (by intro g; cases g <;> rfl)

noncomputable def gateRightProgram : Procedure gateCode Nat.bits gateRight :=
  ((Procedure.casesSum (Procedure.casesSum (Procedure.identity Nat.bits) (Procedure.identity Nat.bits))
    (Procedure.second Nat.bits Nat.bits)).precompose qmaGateEquiv).congrFun
      (by intro g; cases g <;> rfl)

def swapList (a : ℕ) : List QMAGate :=
  [.controlledNot a (a+1),.controlledNot (a+1) a,.controlledNot a (a+1)]

theorem swapList_reverse (a : ℕ) : (swapList a).reverse=swapList a := rfl

noncomputable def swapListProgram : Procedure Nat.bits (listCode gateCode) swapList := by
  let a := Procedure.identity Nat.bits
  let b := Procedure.successor
  let forward := cnotProgram.comp (a.pair b)
  let backward := cnotProgram.comp (b.pair a)
  let nil := Procedure.constant Nat.bits (listCode gateCode) []
  let one := (Procedure.listCons gateCode).comp (forward.pair nil)
  let two := (Procedure.listCons gateCode).comp (backward.pair one)
  exact (Procedure.listCons gateCode).comp (forward.pair two)

end ContinuumCoulomb.QuantumCircuitCode

end

end OAI
