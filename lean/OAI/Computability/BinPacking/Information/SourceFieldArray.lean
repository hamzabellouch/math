import OAI.Computability.BinPacking.Computation.MachineUnaryLessAt

namespace OAI

namespace BinPackingGames.Foundations.Hastad.SourceMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def fieldLoop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt destination exit)))

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

private theorem update_field_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

private theorem update_field_destination (source destination : K)
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
    simp [fieldLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, hne, update_field_source]

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
  simp [fieldLoop, TM2.stepAux, hne, update_field_source, update_field_destination]

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
  simp [fieldStart, TM2.stepAux, update_field_destination]

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

end BinPackingGames.Foundations.Hastad.SourceMachine

namespace BinPackingGames.Foundations.Hastad.SourceFieldArray

open Turing
open BinPackingGames.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

def finish (source : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)

theorem finishStep (source : K) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFinish : program label = finish source exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some label, (ambient, register), base⟩ =
      some ⟨exit, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program label) (ambient, register) base) = _
  rw [atFinish]
  cases exit <;> simp [finish, Reduction.MachineTransfer.exitAt, TM2.stepAux]

def sequenceTapes (source : K) (destination : Nat → K) (base : K → List Bool)
    (offset : Nat) (values : List Nat) (suffix : List Bool) : K → List Bool :=
  match values with
  | [] => base
  | n :: rest => sequenceTapes source destination
      (afterField source (destination offset) base n (encodeWords rest ++ suffix))
      (offset + 1) rest suffix

theorem sequenceTrace (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[values.sum + 2 * values.length + 1]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩ := by
  induction values generalizing offset base register with
  | nil =>
    simpa only [List.sum_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, Function.iterate_one, MachineComposition.advance_some, sequenceTapes]
      using finishStep source (start offset) exit program atDone base ambient register
  | cons n rest ih =>
    have hr0 : 0 < (n :: rest).length := by simp
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 hr0
    have hs0 : program (start offset) = fieldStart (destination offset) (loopLabel offset) := by
      simpa using atStart 0 hr0
    have hl0 : program (loopLabel offset) = fieldLoop source (destination offset)
        (loopLabel offset) (some (start (offset + 1))) := by simpa using atLoop 0 hr0
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    have hfirst := (fieldInTime source (destination offset) hsep0 (start offset)
      (loopLabel offset) (some (start (offset + 1))) program hs0 hl0 base n
      (encodeWords rest ++ suffix) hin ambient register).evals_in_steps
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨some (start (offset + 1)), (ambient, none), nextBase⟩ at hfirst
    have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    have hs' : ∀ r, r < rest.length → program (start (offset + 1 + r)) =
        fieldStart (destination (offset + 1 + r)) (loopLabel (offset + 1 + r)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atStart (r + 1) (by simp; omega)
    have hl' : ∀ r, r < rest.length → program (loopLabel (offset + 1 + r)) =
        fieldLoop source (destination (offset + 1 + r)) (loopLabel (offset + 1 + r))
          (some (start (offset + 1 + r + 1))) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atLoop (r + 1) (by simp; omega)
    have hd' : program (start (offset + 1 + rest.length)) = finish source exit := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atDone
    have hin' : nextBase source = encodeWords rest ++ suffix := by
      simp [nextBase, afterField, hsep0]
    rw [show (n :: rest).sum + 2 * (n :: rest).length + 1 =
      (rest.sum + 2 * rest.length + 1) + (n + 2) by simp; omega]
    rw [Function.iterate_add_apply, hfirst,
      ih nextBase (offset + 1) hsep' hs' hl' hd' hin' none]
    rfl

def sequenceInTime (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start offset), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩)
      (values.sum + 2 * values.length + 1) where
  steps := values.sum + 2 * values.length + 1
  evals_in_steps := sequenceTrace source destination start loopLabel exit program base offset
    values suffix hsep atStart atLoop atDone hinput ambient register
  steps_le_m := Nat.le_refl _

theorem sequence_time_eq_length (values : List Nat) :
    values.sum + 2 * values.length + 1 = (encodeWords values).length + values.length + 1 := by
  rw [encodeWords_length]
  omega

theorem sequenceTapes_other (source : K) (destination : Nat → K)
    (p : K) (hpS : p ≠ source) (base : K → List Bool) (offset : Nat)
    (values : List Nat) (suffix : List Bool)
    (hpD : ∀ r, r < values.length → p ≠ destination (offset + r)) :
    sequenceTapes source destination base offset values suffix p = base p := by
  induction values generalizing base offset with
  | nil => rfl
  | cons n rest ih =>
    have hp0 : p ≠ destination offset := by simpa using hpD 0 (by simp)
    have htail : ∀ r, r < rest.length → p ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpD (r + 1) (by simp; omega)
    rw [sequenceTapes, ih _ (offset + 1) htail]
    exact fieldTapes_other source (destination offset) p hpS hp0 _ _ _

theorem sequenceTapes_source (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hinput : base source = encodeWords values ++ suffix) :
    sequenceTapes source destination base offset values suffix source = suffix := by
  induction values generalizing base offset with
  | nil => simpa [sequenceTapes, encodeWords] using hinput
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    have htail : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    apply ih _ (offset + 1) htail
    simp [afterField, hsep0]

theorem sequenceTapes_selected (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (j : Nat) (hj : j < values.length)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hdist : ∀ r s, r < values.length → s < values.length →
      destination (offset + r) = destination (offset + s) → r = s) :
    sequenceTapes source destination base offset values suffix (destination (offset + j)) =
      encodeWord (values[j]'hj) ++ base (destination (offset + j)) := by
  induction values generalizing base offset j with
  | nil => simp at hj
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    cases j with
    | zero =>
      have hframe : ∀ r, r < rest.length → destination offset ≠ destination (offset + 1 + r) := by
        intro r hr heq
        have hh := hdist 0 (r + 1) (by simp) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      simp only [sequenceTapes, Nat.add_zero, List.getElem_cons_zero]
      rw [sequenceTapes_other source destination (destination offset) hsep0.symm _
        (offset + 1) rest suffix hframe]
      simp [afterField]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
        intro r hr
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
      have hdist' : ∀ r s, r < rest.length → s < rest.length →
          destination (offset + 1 + r) = destination (offset + 1 + s) → r = s := by
        intro r s hr hs heq
        have hh := hdist (r + 1) (s + 1) (by simp; omega) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hsrc : destination (offset + 1 + j) ≠ source := (hsep' j hj').symm
      have hdst : destination (offset + 1 + j) ≠ destination offset := by
        intro heq
        have hh := hdist (j + 1) 0 hj (by simp)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hkeep : nextBase (destination (offset + 1 + j)) = base (destination (offset + 1 + j)) :=
        fieldTapes_other source (destination offset) _ hsrc hdst _ _ _
      simp only [sequenceTapes, List.getElem_cons_succ]
      rw [show offset + (j + 1) = offset + 1 + j by omega]
      rw [ih _ (offset + 1) j hj' hsep' hdist']
      exact congrArg (encodeWord rest[j] ++ ·) hkeep

def boundedIndex (q j : Nat) : Fin (q + 1) := ⟨min j q, by omega⟩

@[simp] theorem boundedIndex_val {q j : Nat} (hj : j ≤ q) :
    (boundedIndex q j).val = j := Nat.min_eq_left hj

def destination (q j : Nat) : Fin (q + 1) := boundedIndex q (j + 1)
def startLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, false)
def loopLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, true)

theorem destination_ne_source (q r : Nat) (hr : r < q) :
    (0 : Fin (q + 1)) ≠ destination q r := by
  intro heq
  have hh := congrArg Fin.val heq
  simp only [destination, boundedIndex_val (Nat.succ_le_iff.mpr hr)] at hh
  change 0 = r + 1 at hh
  omega

theorem destination_injective_below (q r s : Nat) (hr : r < q) (hs : s < q)
    (heq : destination q r = destination q s) : r = s := by
  have hh := congrArg Fin.val heq
  simp only [destination, boundedIndex_val (Nat.succ_le_iff.mpr hr),
    boundedIndex_val (Nat.succ_le_iff.mpr hs)] at hh
  omega

@[simp] theorem destination_eq_succ {q : Nat} (j : Fin q) : destination q j.val = j.succ := by
  apply Fin.ext
  exact boundedIndex_val (Nat.succ_le_iff.mpr j.isLt)

theorem output_source (q : Nat) (values : List Nat) (hlen : values.length = q)
    (base : Fin (q + 1) → List Bool) (suffix : List Bool)
    (hinput : base 0 = encodeWords values ++ suffix) :
    sequenceTapes (0 : Fin (q + 1)) (destination q) base 0 values suffix 0 = suffix := by
  apply sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simpa using destination_ne_source q r (by omega)

theorem output_field (q : Nat) (values : List Nat) (hlen : values.length = q)
    (base : Fin (q + 1) → List Bool) (suffix : List Bool) (j : Fin q) :
    sequenceTapes (0 : Fin (q + 1)) (destination q) base 0 values suffix j.succ =
      encodeWord (values[j.val]'(by omega)) ++ base j.succ := by
  have h := sequenceTapes_selected (0 : Fin (q + 1)) (destination q) base 0 values suffix
    j.val (by omega)
    (by intro r hr; simpa using destination_ne_source q r (by omega))
    (by
      intro r s hr hs heq
      exact destination_injective_below q r s (by omega) (by omega)
        (by simpa only [Nat.zero_add] using heq))
  simpa only [Nat.zero_add, destination_eq_succ] using h

def program (q : Nat) (label : Fin (q + 1) × Bool) :
    TM2.Stmt (fun _ : Fin (q + 1) => Bool) (Fin (q + 1) × Bool) (Unit × Option Bool) :=
  if label.1.val < q then
    if label.2 then
      fieldLoop 0 (destination q label.1.val) (label.1, true)
        (some (startLabel q (label.1.val + 1)))
    else fieldStart (destination q label.1.val) (label.1, true)
  else finish 0 none

def machine (q : Nat) : FinTM2 where
  K := Fin (q + 1)
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin (q + 1) × Bool
  main := startLabel q 0
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program q

theorem atStart (q r : Nat) (hr : r < q) :
    program q (startLabel q r) = fieldStart (destination q r) (loopLabel q r) := by
  simp [program, startLabel, loopLabel, boundedIndex_val hr.le, hr]

theorem atLoop (q r : Nat) (hr : r < q) :
    program q (loopLabel q r) = fieldLoop (0 : Fin (q + 1)) (destination q r)
      (loopLabel q r) (some (startLabel q (r + 1))) := by
  simp [program, startLabel, loopLabel, boundedIndex_val hr.le, hr]

theorem atDone (q : Nat) : program q (startLabel q q) = finish (0 : Fin (q + 1)) none := by
  simp [program, startLabel]

def machineInTime (q : Nat) (values : List Nat) (hlen : values.length = q)
    (base : Fin (q + 1) → List Bool) (suffix : List Bool)
    (hinput : base 0 = encodeWords values ++ suffix) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (startLabel q 0), ((), register), base⟩
      (some ⟨none, ((), none), sequenceTapes (0 : Fin (q + 1)) (destination q) base 0 values suffix⟩)
      (values.sum + 2 * q + 1) := by
  have hsep : ∀ r, r < values.length → (0 : Fin (q + 1)) ≠ destination q (0 + r) := by
    intro r hr heq
    have hr' : r + 1 ≤ q := by omega
    have hh := congrArg Fin.val heq
    simp only [Nat.zero_add, destination, boundedIndex_val hr'] at hh
    change 0 = r + 1 at hh
    omega
  have hs : ∀ r, r < values.length → program q (startLabel q (0 + r)) =
      fieldStart (destination q (0 + r)) (loopLabel q (0 + r)) := by
    intro r hr
    simpa only [Nat.zero_add] using atStart q r (by omega)
  have hl : ∀ r, r < values.length → program q (loopLabel q (0 + r)) =
      fieldLoop (0 : Fin (q + 1)) (destination q (0 + r)) (loopLabel q (0 + r))
        (some (startLabel q (0 + r + 1))) := by
    intro r hr
    simpa only [Nat.zero_add] using atLoop q r (by omega)
  have hd : program q (startLabel q (0 + values.length)) = finish (0 : Fin (q + 1)) none := by
    simpa [hlen] using atDone q
  simpa only [machine, FinTM2.Cfg, FinTM2.step, hlen] using! sequenceInTime (0 : Fin (q + 1)) (destination q)
    (startLabel q) (loopLabel q) none (program q) base 0 values suffix hsep hs hl hd hinput () register

def machineInTime_inputBound (q : Nat) (values : List Nat) (hlen : values.length = q)
    (base : Fin (q + 1) → List Bool) (suffix : List Bool)
    (hinput : base 0 = encodeWords values ++ suffix) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (startLabel q 0), ((), register), base⟩
      (some ⟨none, ((), none), sequenceTapes (0 : Fin (q + 1)) (destination q) base 0 values suffix⟩)
      ((base 0).length + q + 1) := by
  let run := machineInTime q values hlen base suffix hinput register
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have hi : (base 0).length = values.sum + q + suffix.length := by
    rw [hinput, List.length_append, encodeWords_length, hlen]
  omega

def sixFieldsInTime (base : Fin 7 → List Bool) (a b c d e f : Nat) (suffix : List Bool)
    (hinput : base 0 = encodeWords [a, b, c, d, e, f] ++ suffix) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine 6).step
      ⟨some (startLabel 6 0), ((), register), base⟩
      (some ⟨none, ((), none),
        sequenceTapes (0 : Fin 7) (destination 6) base 0 [a, b, c, d, e, f] suffix⟩)
      (a + b + c + d + e + f + 13) := by
  have h := machineInTime 6 [a, b, c, d, e, f] rfl base suffix hinput register
  convert h using 1
  simp
  omega

end BinPackingGames.Foundations.Hastad.SourceFieldArray

end OAI
