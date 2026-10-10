import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI


namespace PerfectCompleteness.NormalizationReadMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Signs := Fin 3 → Bool
abbrev Counters := Fin 3 → List Bool
abbrev State (A : Type) := (A × Signs) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

def clean {A : Type} (ambient : A) (signs : Signs) : State A := ((ambient, signs), none)

def clauseSigns {n : Nat} (clause : Target.Clause n) : Signs := fun i => clause[i].positive

def clauseCounters {n : Nat} (clause : Target.Clause n) : Counters :=
  fun i => List.replicate clause[i].variableIndex.val true

inductive Label where
  | field (slot : Fin 3)
  | sign (slot : Fin 3)
  deriving DecidableEq, Fintype

section Placement

variable {K Λ A : Type} [DecidableEq K]

def afterSign (labels : Label → Λ) (exit : Option Λ) (slot : Fin 3) : Option Λ :=
  if slot = 0 then some (labels (.field 1))
  else if slot = 1 then some (labels (.field 2)) else exit

@[simp] theorem afterSign_zero (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 0 = some (labels (.field 1)) := rfl

@[simp] theorem afterSign_one (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 1 = some (labels (.field 2)) := rfl

@[simp] theorem afterSign_two (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 2 = exit := rfl

def saveSign (source : K) (slot : Fin 3) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1 (Function.update state.1.2 slot bit))
    (exitAt source exit)

def rejectSign (source : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1 state.1.2) (exitAt source exit)

def signInstruction (source : K) (slot : Fin 3) (exit rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (rejectSign source rejected)
      (.branch (fun state => state.2.getD false)
        (.pop source (fun state head => (state.1, head))
          (.branch (fun state => state.2 == some false)
            (saveSign source slot true exit) (rejectSign source rejected)))
        (saveSign source slot false exit)))

def instruction (tape : Fin 4 → K) (labels : Label → Λ) (exit rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .field slot => Hastad.SourceMachine.fieldLoop (tape 0) (tape slot.succ)
      (labels (.field slot)) (some (labels (.sign slot)))
  | .sign slot => signInstruction (tape 0) slot (afterSign labels exit slot) rejected

def tapes (tape : Fin 4 → K) (base : K → List Bool) (input : List Bool)
    (counter : Counters) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) input) (tape 1) (counter 0)) (tape 2) (counter 1)) (tape 3) (counter 2)

theorem tapes_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (counter : Counters) :
    tapes tape base input counter (tape 0) = input := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [tapes, hd]

theorem tapes_counter (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (counter : Counters) (slot : Fin 3) :
    tapes tape base input counter (tape slot.succ) = counter slot := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  fin_cases slot <;> simp [tapes, hd]

theorem tapes_other (tape : Fin 4 → K) (base : K → List Bool)
    (input : List Bool) (counter : Counters) (k : K) (other : ∀ i, k ≠ tape i) :
    tapes tape base input counter k = base k := by
  simp [tapes, other]

theorem update_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (counter : Counters) :
    Function.update (tapes tape base input counter) (tape 0) replacement =
      tapes tape base replacement counter := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases hk : k = tape 0
  · subst k
    simp [tapes, hd]
  · simp [tapes, hk, Function.update_apply]

theorem update_counter (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (counter : Counters) (slot : Fin 3) :
    Function.update (tapes tape base input counter) (tape slot.succ) replacement =
      tapes tape base input (Function.update counter slot replacement) := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases hk : k = tape slot.succ
  · subst k
    fin_cases slot <;> simp [tapes, hd]
  · fin_cases slot
    · change k ≠ tape 1 at hk
      simp [tapes, hk, Function.update_apply]
    · change k ≠ tape 2 at hk
      simp [tapes, hk, Function.update_apply]
    · change k ≠ tape 3 at hk
      simp [tapes, hk, Function.update_apply]

theorem fieldTapes_eq (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement output : List Bool)
    (counter : Counters) (slot : Fin 3) :
    Hastad.SourceMachine.fieldTapes (tape 0) (tape slot.succ)
      (tapes tape base input counter) replacement output =
      tapes tape base replacement (Function.update counter slot output) := by
  unfold Hastad.SourceMachine.fieldTapes
  rw [update_input tape distinct, update_counter tape distinct]

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, program (labels label) = instruction tape labels exit rejected label)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem fieldTrace (slot : Fin 3) (value : Nat) (suffix : List Bool)
    (counter : Counters) (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[value + 1]
      (some ⟨some (labels (.field slot)), ((ambient, signs), register),
        tapes tape base (encodeWord value ++ suffix) counter⟩) =
      some ⟨some (labels (.sign slot)), clean ambient signs,
        tapes tape base suffix
          (Function.update counter slot (List.replicate value true ++ counter slot))⟩ := by
  have distinctSlot : tape 0 ≠ tape slot.succ := by
    intro h
    have same := congrArg Fin.val (distinct h)
    simp only [Fin.val_zero, Fin.val_succ] at same
    omega
  have h := Hastad.SourceMachine.fieldLoopTrace (tape 0) (tape slot.succ) distinctSlot
    (labels (.field slot)) (some (labels (.sign slot))) program (atLabels (.field slot))
    (tapes tape base (encodeWord value ++ suffix) counter) value suffix (counter slot)
    (ambient, signs) register
  simpa only [fieldTapes_eq tape distinct, Function.update_eq_self, clean] using h

theorem signStep (slot : Fin 3) (sign : Bool) (suffix : List Bool)
    (counter : Counters) (signs : Signs) (register : Option Bool) :
    TM2.step program
      ⟨some (labels (.sign slot)), ((ambient, signs), register),
        tapes tape base (encodeWord (if sign then 1 else 0) ++ suffix) counter⟩ =
      some ⟨afterSign labels exit slot, clean ambient (Function.update signs slot sign),
        tapes tape base suffix counter⟩ := by
  change some (TM2.stepAux (program (labels (.sign slot))) _ _) = _
  rw [atLabels (.sign slot)]
  cases sign <;> cases h : afterSign labels exit slot <;>
    simp [instruction, signInstruction, saveSign, rejectSign, encodeWord,
      TM2.stepAux, exitAt, h, clean, tapes_input tape distinct, update_input tape distinct]

omit [DecidableEq K] distinct atLabels in
private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem literalTrace {n : Nat} (slot : Fin 3) (literal : Target.Literal n)
    (suffix : List Bool) (counter : Counters) (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[literal.variableIndex.val + 2]
      (some ⟨some (labels (.field slot)), ((ambient, signs), register),
        tapes tape base (encodeWords (literalWords literal) ++ suffix) counter⟩) =
      some ⟨afterSign labels exit slot, clean ambient (Function.update signs slot literal.positive),
        tapes tape base suffix (Function.update counter slot
          (List.replicate literal.variableIndex.val true ++ counter slot))⟩ := by
  have first := fieldTrace tape distinct labels exit rejected program atLabels base ambient
    slot literal.variableIndex.val (encodeWord (if literal.positive then 1 else 0) ++ suffix)
    counter signs register
  have second := signStep tape distinct labels exit rejected program atLabels base ambient
    slot literal.positive suffix
    (Function.update counter slot (List.replicate literal.variableIndex.val true ++ counter slot))
    signs none
  change (advance (TM2.step program))^[1]
    (some ⟨some (labels (.sign slot)), clean ambient signs,
      tapes tape base (encodeWord (if literal.positive then 1 else 0) ++ suffix)
        (Function.update counter slot (List.replicate literal.variableIndex.val true ++ counter slot))⟩) = _
    at second
  have full := joinTrace first second
  simpa only [literalWords, encodeWords, List.append_nil, List.append_assoc,
    Nat.add_assoc] using full

theorem clauseTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[clause[0].variableIndex.val +
        clause[1].variableIndex.val + clause[2].variableIndex.val + 6]
      (some ⟨some (labels (.field 0)), ((ambient, signs), register),
        tapes tape base (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩) =
      some ⟨exit, clean ambient (clauseSigns clause),
        tapes tape base suffix (clauseCounters clause)⟩ := by
  let counter₀ : Counters := Function.update (fun _ => []) 0
    (List.replicate clause[0].variableIndex.val true)
  let counter₁ : Counters := Function.update counter₀ 1
    (List.replicate clause[1].variableIndex.val true)
  let counter₂ : Counters := Function.update counter₁ 2
    (List.replicate clause[2].variableIndex.val true)
  let signs₀ := Function.update signs 0 clause[0].positive
  let signs₁ := Function.update signs₀ 1 clause[1].positive
  let signs₂ := Function.update signs₁ 2 clause[2].positive
  have counter₀_one : counter₀ 1 = [] := rfl
  have counter₁_two : counter₁ 2 = [] := rfl
  have first := literalTrace tape distinct labels exit rejected program atLabels base ambient
    0 clause[0] (encodeWords (literalWords clause[1]) ++
      (encodeWords (literalWords clause[2]) ++ suffix)) (fun _ => []) signs register
  have second := literalTrace tape distinct labels exit rejected program atLabels base ambient
    1 clause[1] (encodeWords (literalWords clause[2]) ++ suffix) counter₀ signs₀ none
  have third := literalTrace tape distinct labels exit rejected program atLabels base ambient
    2 clause[2] suffix counter₁ signs₁ none
  simp only [counter₀_one, counter₁_two, List.append_nil,
    afterSign_zero, afterSign_one, afterSign_two] at first second third
  have full := joinTrace (joinTrace first second) third
  have counters_eq : counter₂ = clauseCounters clause := by
    funext i
    fin_cases i <;> simp [counter₂, counter₁, counter₀, clauseCounters]
  have signs_eq : signs₂ = clauseSigns clause := by
    funext i
    fin_cases i <;> simp [signs₂, signs₁, signs₀, clauseSigns]
  have htime : (clause[0].variableIndex.val + 2 + (clause[1].variableIndex.val + 2)) +
      (clause[2].variableIndex.val + 2) =
      clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6 := by omega
  rw [htime] at full
  change (advance (TM2.step program))^[_]
    (some ⟨some (labels (.field 0)), ((ambient, signs), register),
      tapes tape base (encodeWords (literalWords clause[0]) ++
        (encodeWords (literalWords clause[1]) ++ (encodeWords (literalWords clause[2]) ++ suffix)))
        (fun _ => [])⟩) =
    some ⟨exit, clean ambient signs₂, tapes tape base suffix counter₂⟩ at full
  rw [signs_eq, counters_eq] at full
  simpa only [clauseWords, encodeWords_append, List.append_assoc] using full

def clauseInTime {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.field 0)), ((ambient, signs), register),
        tapes tape base (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩
      (some ⟨exit, clean ambient (clauseSigns clause),
        tapes tape base suffix (clauseCounters clause)⟩)
      (clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6) where
  steps := clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6
  evals_in_steps := clauseTrace tape distinct labels exit rejected program atLabels base ambient
    clause suffix signs register
  steps_le_m := Nat.le_refl _

end Placement

theorem steps_le_encoded_length {n : Nat} (clause : Target.Clause n) :
    clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6 ≤
      (encodeWords (clauseWords clause)).length := by
  simp only [clauseWords, encodeWords_append, List.length_append,
    literalWords, encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

abbrev ConcreteLabel := Label ⊕ Bool

def concreteProgram : ConcreteLabel → TM2.Stmt (Alphabet (K := Fin 4)) ConcreteLabel (State Unit)
  | .inl label => instruction id Sum.inl (some (.inr true)) (some (.inr false)) label
  | .inr _ => .halt

abbrev machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := ConcreteLabel
  main := .inl (.field 0)
  σ := State Unit
  initialState := clean () (fun _ => false)
  m := concreteProgram

def machineInTime {n : Nat} (clause : Target.Clause n) (suffix : List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (.inl (.field 0)), clean () (fun _ => false),
        tapes id (fun _ : Fin 4 => []) (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩
      (some ⟨some (.inr true), clean () (clauseSigns clause),
        tapes id (fun _ : Fin 4 => []) suffix (clauseCounters clause)⟩)
      (clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6) :=
  clauseInTime id (fun _ _ h => h) Sum.inl (some (.inr true)) (some (.inr false))
    concreteProgram (fun _ => rfl) (fun _ => []) () clause suffix (fun _ => false) none

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.NormalizationReadMachine

end OAI
