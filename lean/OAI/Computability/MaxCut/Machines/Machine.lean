import Mathlib
import OAI.Computability.MaxCut.Machines.Runtime
import OAI.Computability.MaxCut.Encoding.Serialization

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceMachine

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Read one unary field, stopping at its zero delimiter. -/
def fieldLoop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt destination exit)))

/-- Seed the destination delimiter before scanning the unary payload. -/
def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

theorem fieldTapes_other (source destination p : K)
    (hpS : p ≠ source) (hpD : p ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output p = base p := by
  simp [fieldTapes, hpS, hpD]

private theorem update_field_source_inline_SourceMachine (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

private theorem update_field_destination_inline_SourceMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) destination replacement =
      fieldTapes source destination base input replacement := by
  simp [fieldTapes]

theorem fieldStep_delimiter (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (false :: suffix) output⟩ =
      some ⟨exit, (ambient, none), fieldTapes source destination base suffix output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (false :: suffix) output)) = _
  rw [atLoop]
  cases exit <;>
    simp [fieldLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, hne, update_field_source_inline_SourceMachine]

theorem fieldStep_true (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (true :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some true),
        fieldTapes source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (true :: input) output)) = _
  rw [atLoop]
  simp [fieldLoop, TM2.stepAux, hne, update_field_source_inline_SourceMachine, update_field_destination_inline_SourceMachine]

/-- Exactly one transition per unary bit, including its terminating delimiter. -/
theorem fieldLoopTrace (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (List.replicate n true ++ output)⟩ := by
  induction n generalizing output register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      fieldStep_delimiter source destination hne loopLabel exit program atLoop
        base suffix output ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (true :: (encodeWord n ++ suffix)) output⟩) = _
    rw [fieldStep_true source destination hne loopLabel exit program atLoop, ih]
    have hrotate : List.replicate n true ++ true :: output =
        true :: (List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n + 1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ, List.cons_append]
    rw [hrotate]

theorem fieldStartStep (source destination : K)
    (startLabel loopLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some startLabel, (ambient, register), fieldTapes source destination base input output⟩ =
      some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base input (false :: output)⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register)
    (fieldTapes source destination base input output)) = _
  rw [atStart]
  simp [fieldStart, TM2.stepAux, update_field_destination_inline_SourceMachine]

def fieldInTime (source destination : K) (hne : source ≠ destination)
    (startLabel loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some startLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (encodeWord n ++ base destination)⟩)
      (n + 2) where
  steps := n + 2
  evals_in_steps := by
    have hbase : fieldTapes source destination base (encodeWord n ++ suffix)
        (base destination) = base := by rw [← hinput, fieldTapes_self]
    conv_lhs => rw [← hbase]
    change (MachineComposition.advance (TM2.step program))^[(n + 1) + 1]
      (some ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [fieldStartStep source destination startLabel loopLabel program atStart,
      fieldLoopTrace source destination hne loopLabel exit program atLoop]
    simp [encodeWord, List.append_assoc]
  steps_le_m := Nat.le_refl _

/-- Stack state after one completed field, retaining an arbitrary old destination. -/
def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

def fieldNext (start : Fin 4 → Λ) (exit : Option Λ) (j : Fin 4) : Option Λ :=
  match j.val with
  | 0 => some (start 1)
  | 1 => some (start 2)
  | 2 => some (start 3)
  | _ => exit

def fourTapes (source : K) (destination : Fin 4 → K) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) : K → List Bool :=
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  afterField source (destination 3) t₂ d suffix

theorem fourTapes_source (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) :
    fourTapes source destination base a b c d suffix source = suffix := by
  simp [fourTapes, afterField, hsep]

theorem fourTapes_other (source : K) (destination : Fin 4 → K)
    (p : K) (hpS : p ≠ source) (hpD : ∀ j, p ≠ destination j)
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool) :
    fourTapes source destination base a b c d suffix p = base p := by
  simp [fourTapes, afterField, fieldTapes_other, hpS, hpD]

theorem fourField_time_eq_length (a b c d : Nat) :
    a + b + c + d + 8 = (encodeWords [a, b, c, d]).length + 4 := by
  simp [encodeWords, encodeWord]
  omega

/-- Four fields are separated by actual finite-stack transitions. The stated
bound is exactly their serialized length plus four delimiter-seeding steps. -/
def fourFieldsInTime (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j)
    (start loopLabel : Fin 4 → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : ∀ j, program (start j) = fieldStart (destination j) (loopLabel j))
    (atLoop : ∀ j, program (loopLabel j) =
      fieldLoop source (destination j) (loopLabel j) (fieldNext start exit j))
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base source = encodeWords [a, b, c, d] ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start 0), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), fourTapes source destination base a b c d suffix⟩)
      (a + b + c + d + 8) := by
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  have h₀ : base source = encodeWord a ++ (encodeWords [b, c, d] ++ suffix) := by
    simpa only [encodeWords, List.append_assoc] using hinput
  have h₁ : t₀ source = encodeWord b ++ (encodeWords [c, d] ++ suffix) := by
    simp [t₀, afterField, hsep, encodeWords, List.append_assoc]
  have h₂ : t₁ source = encodeWord c ++ (encodeWords [d] ++ suffix) := by
    simp [t₁, afterField, hsep, encodeWords, List.append_assoc]
  have h₃ : t₂ source = encodeWord d ++ suffix := by
    simp [t₂, afterField, hsep, encodeWords]
  have p₀ := fieldInTime source (destination 0) (hsep 0) (start 0) (loopLabel 0)
    (some (start 1)) program (atStart 0) (atLoop 0) base a
    (encodeWords [b, c, d] ++ suffix) h₀ ambient register
  have p₁ := fieldInTime source (destination 1) (hsep 1) (start 1) (loopLabel 1)
    (some (start 2)) program (atStart 1) (atLoop 1) t₀ b
    (encodeWords [c, d] ++ suffix) h₁ ambient none
  have p₂ := fieldInTime source (destination 2) (hsep 2) (start 2) (loopLabel 2)
    (some (start 3)) program (atStart 2) (atLoop 2) t₁ c
    (encodeWords [d] ++ suffix) h₂ ambient none
  have p₃ := fieldInTime source (destination 3) (hsep 3) (start 3) (loopLabel 3)
    exit program (atStart 3) (atLoop 3) t₂ d suffix h₃ ambient none
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by have h := p.steps_le_m; omega
  }

def fieldDestination (j : Fin 4) : Fin 5 := ⟨j.val + 1, by omega⟩

theorem fourTapes_concrete (base : Fin 5 → List Bool) (a b c d : Nat) (suffix : List Bool) :
    fourTapes 0 fieldDestination base a b c d suffix =
      fun p : Fin 5 => if p = 0 then suffix
        else if p = 1 then encodeWord a ++ base 1
        else if p = 2 then encodeWord b ++ base 2
        else if p = 3 then encodeWord c ++ base 3
        else encodeWord d ++ base 4 := by
  funext p
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [fourTapes, afterField, fieldTapes, fieldDestination]

def groupingProgram (label : Fin 4 × Bool) :
    TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 4 × Bool) (Unit × Option Bool) :=
  if label.2 then
    fieldLoop 0 (fieldDestination label.1) (label.1, true)
      (fieldNext (fun j => (j, false)) none label.1)
  else fieldStart (fieldDestination label.1) (label.1, true)

/-- One concrete finite machine: five Boolean stacks, eight labels, and three
internal states. Four destination stacks hold the four separated fields. -/
def groupingMachine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 4 × Bool
  main := (0, false)
  σ := Unit × Option Bool
  initialState := ((), none)
  m := groupingProgram

/-- The concrete machine's verified trace includes arbitrary unread input and
arbitrary prior destination contents. No assumed algorithm remains here. -/
def groupingMachineInTime (base : Fin 5 → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base 0 = encodeWords [a, b, c, d] ++ suffix) (register : Option Bool) :
    StateTransition.EvalsToInTime groupingMachine.step
      ⟨some (0, false), ((), register), base⟩
      (some ⟨none, ((), none), fourTapes (0 : Fin 5) fieldDestination base a b c d suffix⟩)
      (a + b + c + d + 8) :=
  fourFieldsInTime (0 : Fin 5) fieldDestination (by
    intro j h
    have hh := congrArg Fin.val h
    change 0 = j.val + 1 at hh
    omega)
    (fun j => (j, false)) (fun j => (j, true)) none groupingProgram
    (by intro j; simp [groupingProgram]) (by intro j; simp [groupingProgram])
    base a b c d suffix hinput () register

end MaxCutGames.Foundations.Hastad.SourceMachine

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

namespace MaxCutGames.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def drain (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)))

theorem drainTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[word.length + 1]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source []⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) (ambient, register)
        (Function.update base source [])) = _
      rw [atDrain]
      cases exit <;> simp [drain, TM2.stepAux, Reduction.MachineTransfer.exitAt]
  | cons symbol word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[word.length + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (Function.update base source (symbol :: word)))) = _
      rw [atDrain]
      simpa [drain, TM2.stepAux] using ih (some symbol)

def drainInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source []⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, (ambient, register), base⟩) = _
    simpa only [Function.update_eq_self] using
      drainTrace source again exit program atDrain base (base source) ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineDrain

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace MaxCutGames.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

variable [DecidableEq K]

/-- This generic composition lemma retains the local execution obligations.
Concrete callers discharge them with the rotor, comparison and row programs. -/
theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end MaxCutGames.Foundations.Complexity.MachineFiniteSequence

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

/-- Selected tapes are empty; every other tape word is preserved. -/
theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

theorem finalTapes_not_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∉ chosen) :
    finalTapes chosen base k = base k := by rw [finalTapes_apply, ite_eq_right h]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

/-- This upper bound remains valid when the cleanup list repeats tapes. -/
theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Exact execution of all concrete drains in the supplied ambient program. -/
theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

def execution (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry chosen labels exit, (ambient, register), base⟩
      (some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩)
      (lengthSum chosen base + chosen.length) where
  steps := steps chosen base
  evals_in_steps := trace chosen labels exit program atLabels base ambient register
  steps_le_m := steps_le chosen base

/-- An executable complete cleanup list from an explicit finite enumeration. -/
def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

/-- The tape component of the actual halted configuration: only output remains. -/
def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

/-- With a clean register, complete work-tape cleanup reaches the standard
halted shape, preserving the output word and the ambient state exactly. -/
theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end MaxCutGames.Foundations.Complexity.MachineDrainMany

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

/-- All instructions act on physical stacks. The final load only resets the
finite internal register; no input-dependent integer is stored in it. -/
def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

theorem cleared_frame (clearKeys : List K) (base : Tapes K) (tape : K)
    (h : tape ∉ clearKeys) : MachineDrainMany.finalTapes clearKeys base tape = base tape :=
  MachineDrainMany.finalTapes_not_mem clearKeys base tape h

theorem reversed_tapes (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) :
    Reduction.MachineTransfer.tapesAt accumulator output
      (MachineDrainMany.finalTapes clearKeys base) [] (base accumulator).reverse =
      canonicalTapes output (base accumulator).reverse := by
  funext k
  by_cases hout : k = output
  · subst k
    simp [Reduction.MachineTransfer.tapesAt, canonicalTapes]
  · by_cases hacc : k = accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, distinct]
    · have hclear := MachineDrainMany.finalTapes_mem clearKeys base k (covers k hacc hout)
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, hout, hacc, hclear]

/-- Exact execution, including the real drain loops, reversal, and reset. The
only program hypotheses identify the caller's actual placed statements. -/
def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

theorem finishCost_le_list (clearKeys : List K) (accumulator : K) (base : Tapes K) :
    finishCost clearKeys accumulator base ≤ MachineDrainMany.lengthSum clearKeys base +
      clearKeys.length + (base accumulator).length + 2 := by
  have h := MachineDrainMany.steps_le clearKeys base
  unfold finishCost
  omega

variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

/-- Each physical pop removes one stored symbol; repeated clear keys add only
the extra empty-tape loop test after their first occurrence. -/
theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

theorem cleared_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    totalLength (MachineDrainMany.finalTapes clearKeys base) = (base accumulator).length := by
  have point (k : K) : (MachineDrainMany.finalTapes clearKeys base k).length =
      if k = accumulator then (base accumulator).length else 0 := by
    by_cases ha : k = accumulator
    · subst k
      simp [cleared_frame clearKeys base accumulator keepAccumulator]
    · by_cases ho : k = output
      · subst k
        simp [ha, cleared_frame clearKeys base output keepOutput, outputEmpty]
      · rw [MachineDrainMany.finalTapes_mem clearKeys base k (covers k ha ho)]
        simp [ha]
  simp only [totalLength, point]
  simp

/-- Exact finalization cost from the complete initial stack contents. -/
theorem finishCost_eq_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    finishCost clearKeys accumulator base = totalLength base + clearKeys.length + 2 := by
  have h := drain_conservation clearKeys base
  rw [cleared_totalLength clearKeys accumulator output keepAccumulator keepOutput covers
    base outputEmpty] at h
  unfold finishCost
  omega

end MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
