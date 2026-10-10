import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution

namespace OAI


namespace PerfectCompleteness.KeyMetadataMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineSubstitution
open MachineComposition CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

def actualSlot (shape : Shape) (occurrence : Nat) (variableIDs : Fin 3 → Nat) : Slot :=
  match shape with
  | .clause signs => .clause occurrence variableIDs signs
  | .bit => .bit (variableIDs 0)

def fieldValue (occurrence : Nat) (variableIDs : Fin 3 → Nat) : Fin 4 → Nat :=
  Fin.cases occurrence variableIDs

def sourceField : Shape → SupportMode → Option (Fin 4)
  | .clause _, .full => some 0
  | .clause _, .clauseBit i => some i.succ
  | .bit, .bit => some 1
  | _, _ => none

def prefixWords (position : Fin n) (shape : Shape) (mode : SupportMode) : List Nat :=
  [position.val, match shape, mode with | .clause _, .full => 2 | _, _ => 1]

def suffixWords : Shape → SupportMode → List Nat
  | .clause signs, .full =>
      [KeyMetadataEncoding.bitWord signs.1, KeyMetadataEncoding.bitWord signs.2.1,
        KeyMetadataEncoding.bitWord signs.2.2]
  | _, _ => [0, 0, 0]

def retainedWords (position : Fin n) (slot : Slot) (mode : SupportMode) : List Nat :=
  if recover slot mode = .dropped then []
  else KeyMetadataEncoding.entryWords (position, recover slot mode)

def retainedBits (position : Fin n) (slot : Slot) (mode : SupportMode) : List Bool :=
  encodeWords (retainedWords position slot mode)

theorem retainedWords_eq (position : Fin n) (shape : Shape) (mode : SupportMode)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) :
    retainedWords position (actualSlot shape occurrence variableIDs) mode =
      match sourceField shape mode with
      | none => []
      | some field => prefixWords position shape mode ++
          [fieldValue occurrence variableIDs field] ++ suffixWords shape mode := by
  cases shape <;> cases mode <;>
    simp [retainedWords, actualSlot, sourceField, prefixWords, suffixWords,
      fieldValue, recover, KeyMetadataEncoding.entryWords]
  rfl

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def clean (ambient : σ) : State σ := (ambient, none)

inductive Label
  | suffix
  | copyOut
  | copyBack
  | «prefix»
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.suffix, .copyOut, .copyBack, .«prefix»]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def idIndex (field : Fin 4) : Fin 6 := ⟨field.val, lt_trans field.isLt (by decide)⟩

def idTape (tape : Fin 6 → K) (field : Fin 4) : K := tape (idIndex field)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun state => clean state.1)
    (match exit with | none => .halt | some label => .goto (fun _ => label))

theorem stepAux_finish (exit : Option Λ) (ambient : σ) (register : Option Bool)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) (ambient, register) base = ⟨exit, clean ambient, base⟩ := by
  cases exit <;> rfl

omit [DecidableEq K] in
@[simp] theorem finish_pushBound (exit : Option Λ) :
    Runtime.statementPushBound (finish (K := K) (σ := σ) exit) = 0 := by
  cases exit <;> rfl

def literal (destination : K) (bits : List Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  pushWord destination bits.reverse (finish exit)

omit [DecidableEq K] in
theorem literal_pushBound (destination : K) (bits : List Bool) (exit : Option Λ) :
    Runtime.statementPushBound (literal (σ := σ) destination bits exit) = bits.length := by
  simp only [literal, statementPushBound_pushWord, List.length_reverse,
    finish_pushBound, Nat.add_zero]

theorem literal_step (destination : K) (bits : List Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (label : Λ)
    (atLabel : program label = literal destination bits exit)
    (base : K → List Bool) (ambient : σ) :
    TM2.step program ⟨some label, clean ambient, base⟩ =
      some ⟨exit, clean ambient, Function.update base destination (bits ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) (ambient, none) base) = _
  rw [atLabel]
  unfold literal
  rw [stepAux_pushWord (Γ := Alphabet (K := K)) (Λ := Λ) (σ := State σ)
    destination bits.reverse (finish exit) (ambient, none) base,
    List.reverse_reverse, stepAux_finish]

def instruction (position : Fin n) (shape : Shape) (mode : SupportMode)
    (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .suffix => match sourceField shape mode with
      | none => finish exit
      | some _ => literal (tape 5) (encodeWords (suffixWords shape mode))
          (some (labels .copyOut))
  | .copyOut => UniqueGamesTheorem.Reduction.MachineTransfer.loopAt
      (idTape tape ((sourceField shape mode).getD 0)) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4)
      (idTape tape ((sourceField shape mode).getD 0)) (tape 5) false
      (labels .copyBack) (some (labels .prefix))
  | .prefix => literal (tape 5) (encodeWords (prefixWords position shape mode)) exit

omit [DecidableEq K] in
theorem instruction_pushBound (position : Fin n) (shape : Shape) (mode : SupportMode)
    (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) (label : Label) :
    Runtime.statementPushBound (instruction (σ := σ) position shape mode tape labels exit label) ≤
      (encodeWords (prefixWords position shape mode)).length +
        (encodeWords (suffixWords shape mode)).length + 2 := by
  cases label with
  | suffix =>
    cases hs : sourceField shape mode <;>
      simp only [instruction, hs, finish_pushBound, literal_pushBound] <;> omega
  | copyOut =>
    simp [instruction, UniqueGamesTheorem.Reduction.MachineTransfer.loopAt,
      UniqueGamesTheorem.Reduction.MachineTransfer.exitAt, Runtime.statementPushBound]
  | copyBack =>
    simp [instruction, MachineCopy.forkLoop, UniqueGamesTheorem.Reduction.MachineTransfer.exitAt,
      Runtime.statementPushBound]
  | «prefix» =>
    rw [instruction, literal_pushBound]
    omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem droppedTrace (position : Fin n) (shape : Shape) (mode : SupportMode)
    (hdrop : sourceField shape mode = none)
    (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction position shape mode tape labels exit label)
    (base : K → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨exit, clean ambient, base⟩ := by
  change some (TM2.stepAux (program (labels .suffix)) (ambient, none) base) = _
  rw [atLabels .suffix]
  simp only [instruction, hdrop, stepAux_finish]

theorem selectedTrace (position : Fin n) (shape : Shape) (mode : SupportMode)
    (field : Fin 4) (hfield : sourceField shape mode = some field)
    (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction position shape mode tape labels exit label)
    (base : K → List Bool) (scratchEmpty : base (tape 4) = []) (ambient : σ) :
    (advance (TM2.step program))^[2 * ((base (idTape tape field)).length + 1) + 2]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 5)
        ((encodeWords (prefixWords position shape mode) ++ base (idTape tape field) ++
          encodeWords (suffixWords shape mode)) ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (distinct heq)
  have hsourceOutput : idTape tape field ≠ tape 5 := by
    apply hd
    intro h
    have heq := congrArg Fin.val h
    have hlt := field.isLt
    change field.val = 5 at heq
    omega
  have hsourceScratch : idTape tape field ≠ tape 4 := by
    apply hd
    intro h
    have heq := congrArg Fin.val h
    have hlt := field.isLt
    change field.val = 4 at heq
    omega
  have houtputScratch : tape 5 ≠ tape 4 := hd 5 4 (by decide)
  let afterSuffix := Function.update base (tape 5)
    (encodeWords (suffixWords shape mode) ++ base (tape 5))
  let afterCopy := Function.update base (tape 5)
    (base (idTape tape field) ++ encodeWords (suffixWords shape mode) ++ base (tape 5))
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterSuffix⟩ := by
    rw [Function.iterate_one, advance_some]
    apply literal_step (tape 5) (encodeWords (suffixWords shape mode))
      (some (labels .copyOut)) program (labels .suffix)
    rw [atLabels .suffix]
    simp only [instruction, hfield]
  have hselected : (sourceField shape mode).getD 0 = field := by
    rw [hfield]
    rfl
  have atOut : program (labels .copyOut) =
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (idTape tape field) (tape 4) id false
        (labels .copyOut) (some (labels .copyBack)) := by
    rw [atLabels .copyOut]
    exact congrArg (fun selected : Fin 4 =>
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (Γ := Alphabet (K := K)) (σ := σ)
        (idTape tape selected) (tape 4) id false
        (labels .copyOut) (some (labels .copyBack))) hselected
  have atBack : program (labels .copyBack) =
      MachineCopy.forkLoop (tape 4) (idTape tape field) (tape 5) false
        (labels .copyBack) (some (labels .prefix)) := by
    rw [atLabels .copyBack]
    exact congrArg (fun selected : Fin 4 =>
      MachineCopy.forkLoop (tape 4) (idTape tape selected) (tape 5) false
        (labels .copyBack) (some (labels .prefix))) hselected
  have hscratch : afterSuffix (tape 4) = [] := by
    simpa only [afterSuffix, Function.update_of_ne (Ne.symm houtputScratch)] using scratchEmpty
  have hsource : afterSuffix (idTape tape field) = base (idTape tape field) := by
    simp [afterSuffix, hsourceOutput]
  have htapes : Function.update afterSuffix (tape 5)
      (afterSuffix (idTape tape field) ++ afterSuffix (tape 5)) = afterCopy := by
    simp [afterSuffix, afterCopy, hsourceOutput, Function.update_idem, List.append_assoc]
  let copied := MachineCopy.copyInTime (idTape tape field) (tape 5) (tape 4)
    hsourceOutput hsourceScratch houtputScratch false (labels .copyOut) (labels .copyBack)
    (some (labels .prefix)) program atOut atBack afterSuffix hscratch ambient none
  have middle := copied.evals_in_steps
  change (advance (TM2.step program))^[2 * ((afterSuffix (idTape tape field)).length + 1)]
    (some ⟨some (labels .copyOut), clean ambient, afterSuffix⟩) =
    some ⟨some (labels .prefix), clean ambient,
      Function.update afterSuffix (tape 5)
        (afterSuffix (idTape tape field) ++ afterSuffix (tape 5))⟩ at middle
  rw [htapes, hsource] at middle
  have last : (advance (TM2.step program))^[1]
      (some ⟨some (labels .prefix), clean ambient, afterCopy⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 5)
        ((encodeWords (prefixWords position shape mode) ++ base (idTape tape field) ++
          encodeWords (suffixWords shape mode)) ++ base (tape 5))⟩ := by
    rw [Function.iterate_one, advance_some]
    have h := literal_step (tape 5) (encodeWords (prefixWords position shape mode)) exit
      program (labels .prefix) (atLabels .prefix) afterCopy ambient
    simpa only [afterCopy, Function.update_self, Function.update_idem, List.append_assoc] using h
  have joined := joinTrace (joinTrace first middle) last
  rw [show (1 + 2 * ((base (idTape tape field)).length + 1)) + 1 =
    2 * ((base (idTape tape field)).length + 1) + 2 by omega] at joined
  exact joined

def sourceLength (tape : Fin 6 → K) (base : K → List Bool) : Nat :=
  ∑ field : Fin 4, (base (idTape tape field)).length

omit [DecidableEq K] in
theorem selected_length_le (tape : Fin 6 → K) (base : K → List Bool) (field : Fin 4) :
    (base (idTape tape field)).length ≤ sourceLength tape base := by
  unfold sourceLength
  exact Finset.single_le_sum
    (f := fun selected : Fin 4 => (base (idTape tape selected)).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ field)

def metadataInTime (position : Fin n) (shape : Shape) (mode : SupportMode)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat)
    (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, program (labels label) =
      instruction position shape mode tape labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ field, base (idTape tape field) = encodeWord (fieldValue occurrence variableIDs field))
    (scratchEmpty : base (tape 4) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .suffix), clean ambient, base⟩
      (some ⟨exit, clean ambient, Function.update base (tape 5)
        (retainedBits position (actualSlot shape occurrence variableIDs) mode ++ base (tape 5))⟩)
      (2 * sourceLength tape base + 4) := by
  cases hfield : sourceField shape mode with
  | none =>
    refine {
      steps := 1
      evals_in_steps := ?_
      steps_le_m := by omega
    }
    change (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update base (tape 5)
        (retainedBits position (actualSlot shape occurrence variableIDs) mode ++ base (tape 5))⟩
    have hbits : retainedBits position (actualSlot shape occurrence variableIDs) mode = [] := by
      simp only [retainedBits, retainedWords_eq, hfield, encodeWords]
    simpa only [hbits, List.nil_append, Function.update_eq_self] using
      droppedTrace position shape mode hfield tape labels exit program atLabels base ambient
  | some field =>
    refine {
      steps := 2 * ((base (idTape tape field)).length + 1) + 2
      evals_in_steps := ?_
      steps_le_m := ?_
    }
    · change (advance (TM2.step program))^[2 * ((base (idTape tape field)).length + 1) + 2]
        (some ⟨some (labels .suffix), clean ambient, base⟩) =
        some ⟨exit, clean ambient, Function.update base (tape 5)
          (retainedBits position (actualSlot shape occurrence variableIDs) mode ++ base (tape 5))⟩
      have hbits : retainedBits position (actualSlot shape occurrence variableIDs) mode =
          encodeWords (prefixWords position shape mode) ++ base (idTape tape field) ++
            encodeWords (suffixWords shape mode) := by
        rw [sourceWords field]
        simp [retainedBits, retainedWords_eq, hfield, encodeWords, List.append_assoc]
      rw [hbits]
      exact selectedTrace position shape mode field hfield tape distinct labels exit
        program atLabels base scratchEmpty ambient
    · have hlength := selected_length_le tape base field
      omega

theorem output_frame (tape : Fin 6 → K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hne : k ≠ tape 5) :
    Function.update base (tape 5) (bits ++ base (tape 5)) k = base k := by
  simp [hne]

theorem label_finite : Finite Label := inferInstance

theorem state_finite [Finite σ] : Finite (State σ) := inferInstance

end
end PerfectCompleteness.KeyMetadataMachine

end OAI
