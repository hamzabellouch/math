import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineDrainMany
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularOriginalBody

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {Λ : Type}

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

def cleanupEntry (labels : Label → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

def instruction (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

theorem finalTapes_empty (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∈ cleanupTapes) : finalTapes base d o k = [] := by
  rw [finalTapes_apply, ite_eq_left hk]

theorem finalTapes_other (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∉ cleanupTapes) (hp : k ≠ prefixTape) :
    finalTapes base d o k = base k := by
  rw [finalTapes_apply, ite_eq_right hk, ite_eq_right hp]

@[simp] theorem finalTapes_scratch (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o scratch = base scratch := by
  apply finalTapes_other
  · simp [cleanupTapes, scratch, localRank, count, rotor, padding, level, dummyFuel, core]
  · decide

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

theorem additionTraceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

theorem traceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second

def executionAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels entry), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), finalTapes base d o⟩) (steps base d) where
  steps := steps base d
  evals_in_steps := traceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
