import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawPacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram

namespace OAI

/-! A literal polynomial program for the final ordered X/Z classifier.
It reads two site-label pairs and never enumerates a spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawPacking
open ExactQuantumFactoring.BitStackProgram

def letterCode : Letter → List Bool := prodCode Nat.bits Nat.bits
def inputCode : Input → List Bool := prodCode (listCode letterCode) ratCode
def entry (k : ℕ) (x : Input) : Letter := (x.1.drop k).headD (0,0)

noncomputable opaque weightProgram : Procedure inputCode ratCode Prod.snd := Procedure.second _ _
noncomputable opaque entriesProgram : Procedure inputCode (listCode letterCode) Prod.fst :=
  Procedure.first _ _
noncomputable opaque entryProgram (k : ℕ) : Procedure inputCode letterCode (entry k) :=
  (Procedure.listGet letterCode (0,0)).comp
    ((Procedure.constant inputCode Nat.bits k).pair entriesProgram)
noncomputable opaque indexProgram (k : ℕ) : Procedure inputCode Nat.bits (fun x => (entry k x).1) :=
  (Procedure.first Nat.bits Nat.bits).comp (entryProgram k)
noncomputable opaque labelProgram (k : ℕ) : Procedure inputCode Nat.bits (fun x => (entry k x).2) :=
  (Procedure.second Nat.bits Nat.bits).comp (entryProgram k)
noncomputable opaque labelTest (k a : ℕ) : Procedure inputCode Procedure.boolCode
    (fun x => decide ((entry k x).2=a)) :=
  Procedure.binaryEq.comp ((labelProgram k).pair (Procedure.constant inputCode Nat.bits a))
noncomputable opaque lengthProgram : Procedure inputCode Nat.bits (fun x => x.1.length) :=
  Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength letterCode (0,0)).comp entriesProgram)
noncomputable opaque lengthTest (k : ℕ) : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.1.length=k)) :=
  Procedure.binaryEq.comp (lengthProgram.pair (Procedure.constant inputCode Nat.bits k))
noncomputable opaque sameIndexProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide ((entry 0 x).1=(entry 1 x).1)) :=
  Procedure.binaryEq.comp ((indexProgram 0).pair (indexProgram 1))

noncomputable opaque scalarProgram : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => scalar x.2) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (false,false)).pair
    ((Procedure.constant inputCode (prodCode Nat.bits Nat.bits) (0,0)).pair
      ((Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode)
        (false,false)).pair weightProgram))

noncomputable opaque nonzeroFieldProgram (k : ℕ) :
    Procedure inputCode QuantumRawExchange.rawCode (fun x =>
      ((false,true),(((entry k x).1,0),((decide ((entry k x).2=1),false),x.2)))) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (false,true)).pair
    (((indexProgram k).pair (Procedure.constant inputCode Nat.bits 0)).pair
      (((labelTest k 1).pair (Procedure.constant inputCode Procedure.boolCode false)).pair
        weightProgram))

noncomputable opaque fieldProgram (k : ℕ) : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => field (entry k x) x.2) :=
  (Procedure.conditional (labelTest k 0) scalarProgram (nonzeroFieldProgram k)).congrFun (by
    intro x
    simp only [field,decide_eq_true_eq])

noncomputable opaque pairProgram : Procedure inputCode QuantumRawExchange.rawCode
    (fun x => pair (entry 0 x) (entry 1 x) x.2) :=
  (Procedure.constant inputCode (prodCode Procedure.boolCode Procedure.boolCode) (true,false)).pair
    (((indexProgram 0).pair (indexProgram 1)).pair
      (((labelTest 0 1).pair (labelTest 1 1)).pair weightProgram))

def lookupValue (x : Input) : QuantumRawExchange.Raw :=
  if x.1.length=0 then scalar x.2 else
  if x.1.length=1 then field (entry 0 x) x.2 else
  if (entry 0 x).1=(entry 1 x).1 then field (entry 0 x) x.2 else
  if (entry 0 x).2=0 then field (entry 1 x) x.2 else
  if (entry 1 x).2=0 then field (entry 0 x) x.2 else
    pair (entry 0 x) (entry 1 x) x.2

theorem lookupValue_eq (x : Input) : lookupValue x = value x := by
  rcases x with ⟨xs,j⟩
  cases xs with
  | nil => rfl
  | cons u xs =>
    cases xs with
    | nil => simp [lookupValue,value,entry]
    | cons v xs => simp [lookupValue,value,entry]

noncomputable opaque program : Procedure inputCode QuantumRawExchange.rawCode value := by
  let p := Procedure.conditional (lengthTest 0) scalarProgram
    (Procedure.conditional (lengthTest 1) (fieldProgram 0)
      (Procedure.conditional sameIndexProgram (fieldProgram 0)
        (Procedure.conditional (labelTest 0 0) (fieldProgram 1)
          (Procedure.conditional (labelTest 1 0) (fieldProgram 0) pairProgram))))
  exact p.congrFun (by
    intro x
    simpa only [lookupValue,Function.comp_apply,decide_eq_true_eq] using lookupValue_eq x)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode QuantumRawExchange.rawCode value := program.toTM2

end ContinuumCoulomb.QuantumOrderedRawPacking

end

end OAI
