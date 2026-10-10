import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDescriptorSiteProgram

namespace OAI

/-! Exact scalar-register evaluation of the diagonal history descriptors. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar
open QuantumCircuitCode QuantumHistoryDescriptors QuantumHistoryBitProgram

abbrev Input := QMACircuit × (Descriptor × Data)
def inputCode : Input → List Bool := prodCode circuitCode (prodCode descriptorCode dataCode)

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.fst := Procedure.first _ _
noncomputable opaque descriptorProgram : Procedure inputCode descriptorCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)
noncomputable opaque tagProgram : Procedure inputCode Nat.bits (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp descriptorProgram
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1.2) :=
  (Procedure.second _ _).comp descriptorProgram
noncomputable opaque timeProgram : Procedure inputCode Nat.bits (fun x => x.1.gates.length) :=
  Procedure.unaryToBits.comp (QuantumHistoryDescriptors.timeProgram.comp circuitProgram)

noncomputable opaque clockBaseProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1) :=
  Procedure.successor.comp (referenceWorkProgram.comp circuitProgram)

noncomputable opaque workBaseProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1+(x.1.gates.length+2)) :=
  Procedure.binaryAdd.comp (clockBaseProgram.pair
    (Procedure.binaryAdd.comp (timeProgram.pair (Procedure.constant inputCode Nat.bits 2))))

noncomputable def clockValueProgram {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) :
    Procedure inputCode Nat.bits (fun x => (clockRow x.1 x.2.2 (f x)).val) :=
  rowProgram.comp ((Procedure.binaryAdd.comp (clockBaseProgram.pair p)).pair dataProgram)

noncomputable def workValueProgram {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) :
    Procedure inputCode Nat.bits (fun x => (workRow x.1 x.2.2 (f x)).val) :=
  rowProgram.comp ((Procedure.binaryAdd.comp (workBaseProgram.pair p)).pair dataProgram)

noncomputable opaque firstUseProgram : Procedure inputCode Nat.bits
    (fun x => QuantumFirstUseProgram.value (x.1,x.2.1.2)) :=
  Procedure.unaryToBits.comp
    (QuantumFirstUseProgram.program.comp (circuitProgram.pair indexProgram))

noncomputable opaque weightProgram : Procedure inputCode scalarCode
    (fun x => rat (weight x.1 x.2.1 x.2.2)) := by
  let const (n : ℕ) := Procedure.constant inputCode Nat.bits n
  let eq {f : Input → ℕ} (p : Procedure inputCode Nat.bits f) (n : ℕ) :=
    Procedure.binaryEq.comp (p.pair (const n))
  let both {f g : Input → Bool} (p : Procedure inputCode Procedure.boolCode f)
      (q : Procedure inputCode Procedure.boolCode g) := Procedure.boolAnd.comp (p.pair q)
  let not {f : Input → Bool} (p : Procedure inputCode Procedure.boolCode f) :=
    Procedure.boolNot.comp p
  let scalar (n : ℚ) := Procedure.constant inputCode scalarCode (rat n)
  let zero := scalar 0
  let one := scalar 1
  let fault := Procedure.conditional
    (both (eq (clockValueProgram indexProgram) 0)
      (eq (clockValueProgram (Procedure.successor.comp indexProgram)) 1)) one zero
  let left := Procedure.conditional (eq (clockValueProgram (const 0)) 1) zero one
  let right := Procedure.conditional
    (eq (clockValueProgram (Procedure.successor.comp timeProgram)) 0) zero one
  let boundary := Procedure.conditional (eq indexProgram 0) left right
  let witness := Procedure.unaryToBits.comp (witnessProgram.comp circuitProgram)
  let initial := both (eq (clockValueProgram firstUseProgram) 1)
    (both (eq (clockValueProgram (Procedure.successor.comp firstUseProgram)) 0)
      (both (Procedure.binaryLe.comp (witness.pair indexProgram))
        (not (eq (workValueProgram indexProgram) 0))))
  let input := Procedure.conditional initial (scalar 14) zero
  let work := Procedure.unaryToBits.comp (workProgram.comp circuitProgram)
  let output := Procedure.conditional
    (both (eq (clockValueProgram timeProgram) 1) (not (eq (workValueProgram work) 1))) one zero
  exact (Procedure.conditional (eq tagProgram 0) fault
    (Procedure.conditional (eq tagProgram 1) boundary
    (Procedure.conditional (eq tagProgram 2) input
    (Procedure.conditional (eq tagProgram 3) output zero)))).congrFun (by
      intro x
      simp only [weight,Function.comp_apply,id_eq,decide_eq_true_eq,Bool.and_eq_true,
        Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,ne_eq,Fin.ext_iff,Fin.val_zero,
        Fin.val_one,Nat.succ_eq_add_one]
      simp only [apply_ite rat])

noncomputable def weightCertificate : Turing.TM2ComputableInPolyTime inputCode scalarCode
    (fun x => rat (weight x.1 x.2.1 x.2.2)) := weightProgram.toTM2

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
