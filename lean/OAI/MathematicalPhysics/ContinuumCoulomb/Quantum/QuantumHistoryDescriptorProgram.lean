import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDescriptors

namespace OAI

/-! Polynomial generation of the literal history-term descriptor list.  Only
the circuit's unary work count and gate-list length control enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev IndexInput := ℕ × (ℕ × ℕ)
def indexCode : IndexInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits Nat.bits)

noncomputable opaque atIndexProgram : Procedure indexCode descriptorCode
    (fun x => atIndex x.1 x.2.1 x.2.2) := by
  let work := Procedure.first Nat.bits (prodCode Nat.bits Nat.bits)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Nat.bits)
  let time := (Procedure.first Nat.bits Nat.bits).comp rest
  let index := (Procedure.second Nat.bits Nat.bits).comp rest
  let one := Procedure.successor.comp time
  let three := Procedure.binaryAdd.comp
    (one.pair (Procedure.constant indexCode Nat.bits 2))
  let inputs := Procedure.binaryAdd.comp (three.pair (Procedure.successor.comp work))
  let afterInput := Procedure.successor.comp inputs
  let tag (n : ℕ) := Procedure.constant indexCode Nat.bits n
  let sub {f : IndexInput → ℕ} (bound : Procedure indexCode Nat.bits f) :
      Procedure indexCode Nat.bits (fun x => x.2.2-f x) :=
    Procedure.binarySub.comp (index.pair bound)
  let lt {f : IndexInput → ℕ} (bound : Procedure indexCode Nat.bits f) :
      Procedure indexCode Procedure.boolCode (fun x => decide (x.2.2<f x)) :=
    Procedure.binaryLt.comp (index.pair bound)
  exact (Procedure.conditional (lt one) ((tag 0).pair index)
    (Procedure.conditional (lt three) ((tag 1).pair (sub one))
    (Procedure.conditional (lt inputs) ((tag 2).pair (sub three))
    (Procedure.conditional (lt afterInput) ((tag 3).pair (tag 0))
      ((tag 4).pair (sub afterInput)))))).congrFun (by
        intro x
        simp only [atIndex,Function.comp_apply,decide_eq_true_eq])

noncomputable opaque timeProgram : Procedure circuitCode unaryCode
    (fun c => c.gates.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength gateCode (.hadamard 0)).comp
    gatesProgram

noncomputable opaque countProgram : Procedure circuitCode unaryCode
    (fun c => 2*c.gates.length+c.work+5) := by
  let twice := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 2).pair timeProgram)
  exact Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (twice.pair workProgram)).pair
      (Procedure.constant circuitCode unaryCode 5))

noncomputable opaque sourceEntryProgram :
    Procedure (prodCode unaryCode circuitCode) descriptorCode
      (fun x => atIndex x.2.work x.2.gates.length x.1) := by
  let circuit := Procedure.second unaryCode circuitCode
  let index := Procedure.unaryToBits.comp (Procedure.first unaryCode circuitCode)
  let work := Procedure.unaryToBits.comp (workProgram.comp circuit)
  let time := Procedure.unaryToBits.comp (timeProgram.comp circuit)
  exact atIndexProgram.comp (work.pair (time.pair index))

noncomputable opaque sourceProgram : Procedure circuitCode (listCode descriptorCode) source :=
  ((Procedure.tabulate (f := fun c i => atIndex c.work c.gates.length i)
    (0,0) sourceEntryProgram).comp
      (countProgram.pair (Procedure.identity circuitCode))).congrFun (by intro c; rfl)

noncomputable def sourceCertificate : Turing.TM2ComputableInPolyTime circuitCode
    (listCode descriptorCode) source := sourceProgram.toTM2

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
