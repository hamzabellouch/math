import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedBranch
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip
import OAI.Analysis.MatrixSigning.Machines.SignedSerializePrimitives

namespace OAI

section

namespace KS.W01.SignedRationalSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers reverseProgram reverse_spec)
open SignedSerializePrimitives

abbrev Registers := Fin 13 → List Bool

def inputState (num den : List Bool) (sgn : Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[],[],num,den,[sgn]]
def selectedState (num den : List Bool) (sgn : Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[sgn],[],num,den,[]]
def oneState (num den : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[true],[true],num,den,[]]
def decrementedState (num den : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[true],WireMagnitude.decrement num,[],den,[]]
def reverseState (wire : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],wire.reverse,[],[],[],[]]
def outputState (wire : List Bool) : Registers :=
  ![[],[],[],[],[],[],[],[],[],[],wire,[],[]]

def signedWire (sgn : Bool) (num den : List Bool) : List Bool :=
  sgn :: (frame num ++ frame den)
def rawWire (sgn : Bool) (num den : List Bool) : List Bool :=
  signedWire sgn (if sgn then WireMagnitude.decrement num else num) den

theorem signedWire_length (sgn : Bool) (num den : List Bool) :
    (signedWire sgn num den).length = 2 * num.length + 2 * den.length + 3 := by
  simp only [signedWire, List.length_cons, List.length_append, length_frame]
  omega

def positivePorts : Fin 3 ↪ Fin 13 := ⟨![10,11,8], by decide⟩
def negativePorts : Fin 3 ↪ Fin 13 := ⟨![9,11,8], by decide⟩
def subtractPorts : Fin 3 ↪ Fin 13 := ⟨![10,9,7], by decide⟩
def reversePorts : Fin 3 ↪ Fin 13 := ⟨![0,10,8], by decide⟩

def pushDispatch (_ : Fin 1) (_ : Fin 13 → Fin 3) (_ : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 9 then .push true else .stay)⟩
def pushOne : Program 13 := ofMachine (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch)
def positiveBranch : Program 13 := compose (pairProgram positivePorts) (reverseProgram reversePorts)
def negativeBranch : Program 13 := compose pushOne
  (compose (subtractProgram subtractPorts)
    (compose (pairProgram negativePorts) (reverseProgram reversePorts)))

def selector (heads : Fin 13 → Fin 3) (_ : Bool) : KS.W29.FixedBranch.SelectInstruction 13 :=
  ⟨if (heads 12).val = 2 then .right else .left,
    Vector.ofFn (fun j => if j = 12 then .pop
      else if j = 8 then .push (decide ((heads 12).val = 2)) else .stay)⟩
def program : Program 13 := KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector

@[simp] theorem stackCount : program.toMachine.stackCount = 13 := rfl
@[simp] theorem inputPort : program.toMachine.inputStack = (10 : Fin 13) := rfl
@[simp] theorem outputPort : program.toMachine.outputStack = (10 : Fin 13) := rfl

private theorem branch_table_length {k : Nat} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k) :
    (KS.W29.FixedBranch.branch P Q output select).table.length =
      (P.states+Q.states+1)*(3^k*2) := by
  change (compile (KS.W29.FixedBranch.start P Q) P.input output
    (KS.W29.FixedBranch.dispatch P Q select)).table.length = _
  exact compile_table_length _ _ _ _

theorem table_length : program.table.length = program.states * (3 ^ 13 * 2) := by
  change program.table.length = (positiveBranch.states+negativeBranch.states+1)*(3^13*2)
  exact branch_table_length positiveBranch negativeBranch 10 selector

theorem selector_false (num den : List Bool) (coin : Bool) :
    program.toMachine.step ⟨some program.initial, inputState num den false⟩ coin =
      KS.W29.FixedBranch.liftLeft positiveBranch negativeBranch
        ⟨some positiveBranch.initial, selectedState num den false⟩ := by
  change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.step
    ⟨some (KS.W29.FixedBranch.start positiveBranch negativeBranch),inputState num den false⟩ coin = _
  erw [KS.W29.FixedBranch.step_start]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem selector_true (num den : List Bool) (coin : Bool) :
    program.toMachine.step ⟨some program.initial, inputState num den true⟩ coin =
      KS.W29.FixedBranch.liftRight positiveBranch negativeBranch
        ⟨some negativeBranch.initial, selectedState num den true⟩ := by
  change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.step
    ⟨some (KS.W29.FixedBranch.start positiveBranch negativeBranch),inputState num den true⟩ coin = _
  erw [KS.W29.FixedBranch.step_start]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem pushOne_spec (num den : List Bool) :
    RunSpec pushOne (selectedState num den true) (oneState num den) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch)
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin tail =>
    have ht : tail = [] := by simpa using hb
    subst tail
    change (compile (0 : Fin 1) (10 : Fin 13) 9 pushDispatch).step
      ⟨some (0 : Fin 1), selectedState num den true⟩ coin = _
    erw [step_compile]
    change Config.mk none _ = Config.mk none _
    congr 1
    funext j
    fin_cases j <;> rfl

theorem positive_emit_spec (num den : List Bool) :
    RunSpec (pairProgram positivePorts) (selectedState num den false)
      (reverseState (signedWire false num den)) (2 * num.length + 2 * den.length + 2) := by
  have h := pair_spec positivePorts (fun _ => []) num den [false]
  have hb : registers positivePorts (fun _ => []) num den [false] = selectedState num den false := by
    funext j
    fin_cases j <;> rfl
  have ha : registers positivePorts (fun _ => []) [] []
      ((frame num ++ frame den).reverse ++ [false]) = reverseState (signedWire false num den) := by
    funext j
    fin_cases j <;> simp [registers, positivePorts, reverseState, signedWire]
  rwa [hb, ha] at h

theorem subtract_spec (num den : List Bool) :
    RunSpec (subtractProgram subtractPorts) (oneState num den) (decrementedState num den)
      (2 * (max num.length 1 + 1)) := by
  have h := decrement_spec subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else []) num
  have hb : registers subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else [])
      num [true] [] = oneState num den := by
    funext j
    fin_cases j <;> rfl
  have ha : registers subtractPorts (fun j => if j = 8 then [true] else if j = 11 then den else [])
      [] (WireMagnitude.decrement num) [] = decrementedState num den := by
    funext j
    fin_cases j <;> rfl
  rwa [hb, ha] at h

theorem negative_emit_spec (num den : List Bool) :
    RunSpec (pairProgram negativePorts) (decrementedState num den)
      (reverseState (signedWire true (WireMagnitude.decrement num) den))
      (2 * (WireMagnitude.decrement num).length + 2 * den.length + 2) := by
  have h := pair_spec negativePorts (fun _ => []) (WireMagnitude.decrement num) den [true]
  have hb : registers negativePorts (fun _ => []) (WireMagnitude.decrement num) den [true] =
      decrementedState num den := by
    funext j
    fin_cases j <;> rfl
  have ha : registers negativePorts (fun _ => []) [] []
      ((frame (WireMagnitude.decrement num) ++ frame den).reverse ++ [true]) =
      reverseState (signedWire true (WireMagnitude.decrement num) den) := by
    funext j
    fin_cases j <;> simp [registers, negativePorts, reverseState, signedWire]
  rwa [hb, ha] at h

theorem finish_spec (wire : List Bool) :
    RunSpec (reverseProgram reversePorts) (reverseState wire) (outputState wire) (wire.length + 1) := by
  have h := reverse_spec reversePorts (fun _ => []) wire
  have hb : registers reversePorts (fun _ => []) [] [] wire.reverse = reverseState wire := by
    funext j
    fin_cases j <;> rfl
  have ha : registers reversePorts (fun _ => []) [] wire [] = outputState wire := by
    funext j
    fin_cases j <;> rfl
  rwa [hb, ha] at h

theorem positive_spec (num den : List Bool) :
    RunSpec positiveBranch (selectedState num den false)
      (outputState (signedWire false num den)) (4 * num.length + 4 * den.length + 6) := by
  have h := (positive_emit_spec num den).compose (finish_spec (signedWire false num den))
  have ht : (2 * num.length + 2 * den.length + 2) + ((signedWire false num den).length + 1) =
      4 * num.length + 4 * den.length + 6 := by rw [signedWire_length]; omega
  rwa [ht] at h

theorem negative_spec (num den : List Bool) :
    RunSpec negativeBranch (selectedState num den true)
      (outputState (signedWire true (WireMagnitude.decrement num) den))
      (2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length + 4 * den.length + 9) := by
  have h := (pushOne_spec num den).compose ((subtract_spec num den).compose
    ((negative_emit_spec num den).compose (finish_spec (signedWire true (WireMagnitude.decrement num) den))))
  have ht : 1 + (2 * (max num.length 1 + 1) +
      ((2 * (WireMagnitude.decrement num).length + 2 * den.length + 2) +
        ((signedWire true (WireMagnitude.decrement num) den).length + 1))) =
      2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length + 4 * den.length + 9 := by
    rw [signedWire_length]
    omega
  rwa [ht] at h

theorem program_spec (num den : List Bool) (sgn : Bool) :
    RunSpec program (inputState num den sgn) (outputState (rawWire sgn num den))
      (16 * (num.length + den.length + 1)) := by
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    simp only [List.length_cons] at hlen
    cases sgn
    · have ht : 4 * num.length + 4 * den.length + 6 ≤ tail.length := by omega
      rw [Machine.run, selector_false]
      change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftLeft positiveBranch negativeBranch
          ⟨some positiveBranch.initial, selectedState num den false⟩) tail = _
      rw [KS.W29.FixedBranch.run_left]
      erw [(positive_spec num den).run_of_le tail ht]
      rfl
    · have hn := WireMagnitude.decrement_length_le num
      have ht : 2 * max num.length 1 + 4 * (WireMagnitude.decrement num).length +
          4 * den.length + 9 ≤ tail.length := by omega
      rw [Machine.run, selector_true]
      change (KS.W29.FixedBranch.branch positiveBranch negativeBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftRight positiveBranch negativeBranch
          ⟨some negativeBranch.initial, selectedState num den true⟩) tail = _
      rw [KS.W29.FixedBranch.run_right]
      erw [(negative_spec num den).run_of_le tail ht]
      rfl

theorem rawWire_canonical (q : ℚ) :
    rawWire (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) = encodeRat q := by
  have h := WireMagnitude.wireRat_encode q
  simpa only [WireMagnitude.wireRat, WireMagnitude.wireInt, WireMagnitude.constructorPayload,
    KS.W19.trimBits_eq_encodeNat, KS.W19.bitsValue_encodeNat, rawWire, signedWire,
    List.cons_append] using h

theorem serializes_rational (q : ℚ) :
    RunSpec program
      (inputState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0))) (outputState (encodeRat q))
      (16 * ((Computability.encodeNat q.num.natAbs).length +
        (Computability.encodeNat q.den).length + 1)) := by
  have h := program_spec (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
    (decide (q.num < 0))
  rwa [rawWire_canonical] at h

end KS.W01.SignedRationalSerializer

end

end OAI
