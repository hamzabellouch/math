import Mathlib.Data.List.FinRange
import OAI.Computability.PerfectCompleteness.Machines.UnaryRepresentationMachine
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas

namespace OAI


namespace PerfectCompleteness.FixedUnaryRepresentationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

inductive Mode
  | encodedToRaw | rawToEncoded
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.encodedToRaw, .rawToEncoded]

protected theorem Mode.enumList_getElem?_ctorIdx_eq (x : Mode) :
    Mode.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Tape (width : Nat)
  | source (position : Fin width)
  | destination (position : Fin width)
  | scratch
  deriving DecidableEq, Fintype

abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (A : Type) := A × Option Bool

def sourceWord : Mode → Nat → List Bool
  | .encodedToRaw, n => encodeWord n
  | .rawToEncoded, n => List.replicate n true

def targetWord : Mode → Nat → List Bool
  | .encodedToRaw, n => List.replicate n true
  | .rawToEncoded, n => encodeWord n

def cost : Mode → Nat → Nat
  | .encodedToRaw, n => 2 * n + 2
  | .rawToEncoded, n => 1 + 2 * (n + 1)

theorem cost_le (mode : Mode) (n : Nat) : cost mode n ≤ 2 * n + 3 := by
  cases mode <;> simp only [cost] <;> omega

def LocalLabel : Mode → Type
  | .encodedToRaw => UnaryRepresentationMachine.RawLabel
  | .rawToEncoded => UnaryRepresentationMachine.EncodedLabel

instance (mode : Mode) : Fintype (LocalLabel mode) := by
  cases mode with
  | encodedToRaw => exact inferInstanceAs (Fintype UnaryRepresentationMachine.RawLabel)
  | rawToEncoded => exact inferInstanceAs (Fintype UnaryRepresentationMachine.EncodedLabel)

instance (mode : Mode) : DecidableEq (LocalLabel mode) := by
  cases mode with
  | encodedToRaw => exact inferInstanceAs (DecidableEq UnaryRepresentationMachine.RawLabel)
  | rawToEncoded => exact inferInstanceAs (DecidableEq UnaryRepresentationMachine.EncodedLabel)

def localMain : (mode : Mode) → LocalLabel mode
  | .encodedToRaw => UnaryRepresentationMachine.encodedToRawMain
  | .rawToEncoded => UnaryRepresentationMachine.rawToEncodedMain

variable {width : Nat} {Λ A : Type}

def localTape (position : Fin width) : Fin 3 → Tape width
  | 0 => .source position
  | 1 => .scratch
  | 2 => .destination position

theorem localTape_injective (position : Fin width) :
    Function.Injective (localTape position) := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [localTape]

def «stacks» (mode : Mode) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) : Tape width → List Bool
  | .source position => sourceWord mode (values position)
  | .destination position => destinations position
  | .scratch => []

theorem update_destination (mode : Mode) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (position : Fin width) (word : List Bool) :
    Function.update («stacks» mode values destinations) (.destination position) word =
      «stacks» mode values (Function.update destinations position word) := by
  funext tape
  cases tape with
  | source next => simp [«stacks»]
  | scratch => simp [«stacks»]
  | destination next =>
      by_cases same : next = position
      · subst next
        simp [«stacks»]
      · simp [«stacks», same]

def update (mode : Mode) (values : Fin width → Nat) (position : Fin width)
    (destinations : Fin width → List Bool) : Fin width → List Bool :=
  Function.update destinations position (targetWord mode (values position) ++ destinations position)

def result (mode : Mode) (values : Fin width → Nat)
    (positions : List (Fin width)) (destinations : Fin width → List Bool) :=
  MachineFiniteSequence.resultOf (update mode values) positions destinations

def steps (mode : Mode) (values : Fin width → Nat) (positions : List (Fin width)) : Nat :=
  (positions.map (fun position => cost mode (values position))).sum

theorem sequence_steps (mode : Mode) (values : Fin width → Nat)
    (positions : List (Fin width)) (destinations : Fin width → List Bool) :
    MachineFiniteSequence.steps (update mode values)
      (fun position _ => cost mode (values position)) positions destinations =
      steps mode values positions := by
  induction positions generalizing destinations with
  | nil => rfl
  | cons position positions ih =>
      simp only [MachineFiniteSequence.steps, steps, List.map_cons, List.sum_cons, ih]

theorem result_apply (mode : Mode) (values : Fin width → Nat)
    (positions : List (Fin width)) (nodup : positions.Nodup)
    (destinations : Fin width → List Bool) (position : Fin width) :
    result mode values positions destinations position =
      if position ∈ positions then targetWord mode (values position) ++ destinations position
      else destinations position := by
  induction positions generalizing destinations with
  | nil => simp [result, MachineFiniteSequence.resultOf]
  | cons first positions ih =>
      have distinct := List.nodup_cons.mp nodup
      change result mode values positions (update mode values first destinations) position = _
      rw [ih distinct.2]
      by_cases same : position = first
      · subst position
        simp [update, distinct.1]
      · simp [update, same]

theorem result_finRange (mode : Mode) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) :
    result mode values (List.finRange width) destinations =
      fun position => targetWord mode (values position) ++ destinations position := by
  funext position
  simp [result_apply mode values _ (List.nodup_finRange width)]

theorem steps_le (mode : Mode) (values : Fin width → Nat) (positions : List (Fin width))
    (maximum : Nat) (bounded : ∀ position, values position ≤ maximum) :
    steps mode values positions ≤ positions.length * (2 * maximum + 3) := by
  induction positions with
  | nil => simp [steps]
  | cons position positions ih =>
      have head := cost_le mode (values position)
      have valueBound := bounded position
      have headBound : cost mode (values position) ≤ 2 * maximum + 3 := by omega
      simp only [steps, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      calc
        _ ≤ 2 * maximum + 3 + positions.length * (2 * maximum + 3) :=
          Nat.add_le_add headBound ih
        _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

def localInstruction : (mode : Mode) → (position : Fin width) →
    (LocalLabel mode → Λ) → Option Λ →
    LocalLabel mode → TM2.Stmt (Alphabet (width := width)) Λ (State A)
  | .encodedToRaw, position, labels, done =>
      UnaryRepresentationMachine.encodedToRawInstruction (localTape position) labels done
  | .rawToEncoded, position, labels, done =>
      UnaryRepresentationMachine.rawToEncodedInstruction (localTape position) labels done

theorem localTrace (mode : Mode) (values : Fin width → Nat) (position : Fin width)
    (labels : LocalLabel mode → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = localInstruction mode position labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[cost mode (values position)]
      (some ⟨some (labels (localMain mode)), (ambient, none), «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values (update mode values position destinations)⟩ := by
  cases mode with
  | encodedToRaw =>
      have run := UnaryRepresentationMachine.encodedToRawTrace (localTape position)
        (localTape_injective position) labels done program atLabels
        («stacks» .encodedToRaw values destinations) (values position) rfl rfl ambient none
      change (advance (TM2.step program))^[cost .encodedToRaw (values position)]
        (some ⟨some (labels (localMain .encodedToRaw)), (ambient, none),
          «stacks» .encodedToRaw values destinations⟩) =
        some ⟨done, (ambient, none), Function.update («stacks» .encodedToRaw values destinations)
          (.destination position) (targetWord .encodedToRaw (values position) ++ destinations position)⟩
        at run
      rw [update_destination] at run
      exact run
  | rawToEncoded =>
      have run := UnaryRepresentationMachine.rawToEncodedTrace (localTape position)
        (localTape_injective position) labels done program atLabels
        («stacks» .rawToEncoded values destinations) (values position) rfl rfl ambient none
      change (advance (TM2.step program))^[cost .rawToEncoded (values position)]
        (some ⟨some (labels (localMain .rawToEncoded)), (ambient, none),
          «stacks» .rawToEncoded values destinations⟩) =
        some ⟨done, (ambient, none), Function.update («stacks» .rawToEncoded values destinations)
          (.destination position) (targetWord .rawToEncoded (values position) ++ destinations position)⟩
        at run
      rw [update_destination] at run
      exact run

abbrev Label (mode : Mode) (positions : List (Fin width)) :=
  MachineFiniteSequence.Label (fun _ : Fin width => LocalLabel mode) positions

def entry (mode : Mode) (positions : List (Fin width)) (labels : Label mode positions → Λ)
    (done : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (fun _ : Fin width => LocalLabel mode)
    (fun _ => localMain mode) positions labels done

def instruction (mode : Mode) (positions : List (Fin width)) (labels : Label mode positions → Λ)
    (done : Option Λ) : Label mode positions → TM2.Stmt (Alphabet (width := width)) Λ (State A) :=
  MachineFiniteSequence.instruction (fun _ : Fin width => LocalLabel mode)
    (fun _ => localMain mode) (localInstruction mode) positions labels done

theorem sequenceTrace (mode : Mode) (values : Fin width → Nat) (positions : List (Fin width))
    (labels : Label mode positions → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode positions labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[steps mode values positions]
      (some ⟨entry mode positions labels done, (ambient, none), «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values (result mode values positions destinations)⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := fun _ : Fin width => LocalLabel mode) (main := fun _ => localMain mode)
    (localInstruction := localInstruction mode) (result := update mode values)
    (cost := fun position _ => cost mode (values position)) program
    (fun _ : Fin width → List Bool => True) (fun _ => (ambient, none)) («stacks» mode values)
    positions (by intros; trivial)
    (by
      intro position _ localLabels localExit atLocal destinationWords _
      exact localTrace mode values position localLabels localExit program atLocal destinationWords ambient)
    labels done atLabels destinations trivial
  simpa only [sequence_steps, entry, result] using run

theorem familyTrace (mode : Mode) (values : Fin width → Nat)
    (labels : Label mode (List.finRange width) → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) =
      instruction mode (List.finRange width) labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[steps mode values (List.finRange width)]
      (some ⟨entry mode (List.finRange width) labels done, (ambient, none),
        «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values
        (fun position => targetWord mode (values position) ++ destinations position)⟩ := by
  simpa only [result_finRange] using
    sequenceTrace mode values (List.finRange width) labels done program atLabels destinations ambient

def familyInTime (mode : Mode) (values : Fin width → Nat)
    (labels : Label mode (List.finRange width) → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) =
      instruction mode (List.finRange width) labels done label)
    (destinations : Fin width → List Bool) (ambient : A)
    (maximum : Nat) (bounded : ∀ position, values position ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry mode (List.finRange width) labels done, (ambient, none), «stacks» mode values destinations⟩
      (some ⟨done, (ambient, none), «stacks» mode values
        (fun position => targetWord mode (values position) ++ destinations position)⟩)
      (width * (2 * maximum + 3)) where
  steps := steps mode values (List.finRange width)
  evals_in_steps := familyTrace mode values labels done program atLabels destinations ambient
  steps_le_m := by
    simpa only [List.length_finRange] using
      steps_le mode values (List.finRange width) maximum bounded

def cleanupTapes (width : Nat) : List (Tape width) :=
  (List.finRange width).map Tape.destination

@[simp] theorem cleanupTapes_length : (cleanupTapes width).length = width := by
  simp [cleanupTapes]

abbrev CleanupLabel (width : Nat) := MachineDrainMany.Label (cleanupTapes width)

def cleanupEntry (labels : CleanupLabel width → Λ) (done : Option Λ) : Option Λ :=
  MachineDrainMany.entry (cleanupTapes width) labels done

def cleanupInstruction (labels : CleanupLabel width → Λ) (done : Option Λ) :
    CleanupLabel width → TM2.Stmt (Alphabet (width := width)) Λ (State A) :=
  MachineDrainMany.instruction (cleanupTapes width) labels done

theorem cleanup_finalTapes (mode : Mode) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) :
    MachineDrainMany.finalTapes (cleanupTapes width) («stacks» mode values destinations) =
      «stacks» mode values (fun _ => []) := by
  funext tape
  cases tape <;> simp [MachineDrainMany.finalTapes_apply, cleanupTapes, «stacks»]

theorem cleanup_lengthSum (mode : Mode) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) :
    MachineDrainMany.lengthSum (cleanupTapes width) («stacks» mode values destinations) =
      ((List.finRange width).map (fun position => (destinations position).length)).sum := by
  simp [MachineDrainMany.lengthSum, cleanupTapes, «stacks», Function.comp_def]

theorem cleanupTrace (mode : Mode) (values : Fin width → Nat)
    (labels : CleanupLabel width → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = cleanupInstruction labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[MachineDrainMany.steps (cleanupTapes width)
      («stacks» mode values destinations)]
      (some ⟨cleanupEntry labels done, (ambient, none), «stacks» mode values destinations⟩) =
      some ⟨done, (ambient, none), «stacks» mode values (fun _ => [])⟩ := by
  simpa only [MachineDrainMany.finalRegister_none, cleanup_finalTapes, cleanupEntry] using
    MachineDrainMany.trace (cleanupTapes width) labels done program atLabels
      («stacks» mode values destinations) ambient none

def cleanupInTime (mode : Mode) (values : Fin width → Nat)
    (labels : CleanupLabel width → Λ) (done : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = cleanupInstruction labels done label)
    (destinations : Fin width → List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry labels done, (ambient, none), «stacks» mode values destinations⟩
      (some ⟨done, (ambient, none), «stacks» mode values (fun _ => [])⟩)
      (((List.finRange width).map (fun position => (destinations position).length)).sum + width) := by
  simpa only [MachineDrainMany.finalRegister_none, cleanup_finalTapes, cleanupEntry,
    cleanup_lengthSum, cleanupTapes_length] using
    MachineDrainMany.execution (cleanupTapes width) labels done program atLabels
      («stacks» mode values destinations) ambient none

theorem finiteState [Finite A] : Finite (State A) := inferInstance

theorem finiteLabels (mode : Mode) : Finite (Label mode (List.finRange width)) := inferInstance

theorem finiteAlphabet (tape : Tape width) : Finite (Alphabet tape) := inferInstance

end PerfectCompleteness.FixedUnaryRepresentationMachine

end OAI
