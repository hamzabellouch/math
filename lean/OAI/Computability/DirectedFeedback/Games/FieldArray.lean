import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineLookupSpec

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceFieldArray

open Turing
open DFVSGames.Foundations.Complexity SourceMachine

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
  convert sequenceInTime (0 : Fin (q + 1)) (destination q)
    (startLabel q) (loopLabel q) none (program q) base 0 values suffix hsep hs hl hd hinput () register
    using 1
  simp only [hlen]
  rfl

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

end DFVSGames.Foundations.Hastad.SourceFieldArray


namespace DFVSGames.Foundations.Hastad.SourceClauseLookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition SourceMachine

section Discard

variable {K Λ σ : Type} [DecidableEq K]

theorem discardFieldsTrace (source : K) (label : Nat → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (atLoop : ∀ r, r < values.length → program (label (offset + r)) =
      MachineLookup.discard source (label (offset + r)) (label (offset + r + 1)))
    (hinput : base source = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (label offset), (ambient, none), base⟩) =
      some ⟨some (label (offset + values.length)), (ambient, none),
        Function.update base source suffix⟩ := by
  induction values generalizing base offset with
  | nil =>
    have hbase : Function.update base source suffix = base := by
      have hs : base source = suffix := by simpa only [encodeWords, List.nil_append] using hinput
      funext p
      by_cases hp : p = source
      · subst p; simp [hs]
      · simp [hp]
    simp only [encodeWords, List.length_nil, Nat.add_zero, Function.iterate_zero_apply, hbase]
  | cons n rest ih =>
    have hs : program (label offset) =
        MachineLookup.discard source (label offset) (label (offset + 1)) := by
      simpa only [Nat.add_zero] using atLoop 0 (by simp)
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    have first := MachineLookup.discardTrace source (label offset) (label (offset + 1))
      program hs base n (encodeWords rest ++ suffix) hin ambient none
    have htail : ∀ r, r < rest.length → program (label (offset + 1 + r)) =
        MachineLookup.discard source (label (offset + 1 + r))
          (label (offset + 1 + r + 1)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        atLoop (r + 1) (by simp; omega)
    have second := ih (Function.update base source (encodeWords rest ++ suffix))
      (offset + 1) htail (by simp)
    rw [show (encodeWords (n :: rest)).length = (encodeWords rest).length + (n + 1) by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega]
    rw [Function.iterate_add_apply, first]
    simpa [Function.update_idem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

end Discard

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 6)
  | read (slot : Fin 7 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 5, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, true)
def skipLabel (r : Nat) : Label := if h : r < 6 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (Unit × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .formula .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 6 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

def machine : FinTM2 where
  K := Tape
  k₀ := .formula
  k₁ := .field 0
  Γ _ := Bool
  Λ := Label
  main := .copyOut
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

theorem atSkip (r : Nat) (hr : r < 6) :
    program (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 6) :
    program (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 6) :
    program (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (readStart 6) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem discardHeadersTrace (base : Tape → List Bool) (variableCount clauses : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, clauses] ++ suffix) :
    (advance (TM2.step program))^[variableCount + clauses + 2]
      (some ⟨some .headerFirst, ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, clauses]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ()
  simpa [encodeWords_length, headerLabel] using ht

theorem discardSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ()
  simpa [hlen, skipLabel] using ht

theorem readSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length + 7]
      (some ⟨some (readStart 0), ((), none), base⟩) =
      some ⟨none, ((), none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput () none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 7 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem skipClausesTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (Target.Clause n)) (indexSuffix suffix : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      (some ⟨some .guard, ((), register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap clauseWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), ((), none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix () register
  | cons clause prior ih =>
    have hencoding : encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix =
        encodeWords (clauseWords clause) ++ (encodeWords (prior.flatMap clauseWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((clause :: prior).flatMap clauseWords)).length +
        (clause :: prior).length + 1 =
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
          (encodeWords (clauseWords clause)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
        (encodeWords (clauseWords clause)).length]
      (TM2.step program ⟨some .guard, ((), register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardSixTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
      (clauseWords clause) (clauseWords_length clause)
      (encodeWords (prior.flatMap clauseWords) ++ suffix) (by
        rw [scanTapes_work, hencoding])
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
        (some ⟨some (skipLabel 0), ((), none), scanTapes base prior.length indexSuffix
          (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem fieldDestination_eq (j : Fin 6) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 6) (hs : s < 6)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 6) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 5 by omega),
    Nat.min_eq_left (show s ≤ 5 by omega)] using hv

theorem readSix_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool) (j : Fin 6) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readSix_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readSix_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    0 (clauseWords clause) suffix

def scanSteps {n : Nat} (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n) : Nat :=
  variableCount + declaredClauses + 2 +
    (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
    (encodeWords (clauseWords clause)).length + 7

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    (advance (TM2.step program))^[scanSteps variableCount declaredClauses prior clause]
      (some ⟨some .headerFirst, ((), none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredClauses] ++
          (encodeWords (prior.flatMap clauseWords) ++
            (encodeWords (clauseWords clause) ++ suffix)))⟩) =
      some ⟨none, ((), none), outputTapes base clause indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredClauses] ++
        (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))))
    variableCount declaredClauses
    (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))
    (by simp)
  have hs := skipClausesTrace base prior indexSuffix (encodeWords (clauseWords clause) ++ suffix) none
  have hr := readSixTrace
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    (clauseWords clause) (clauseWords_length clause) suffix (by simp)
  rw [show scanSteps variableCount declaredClauses prior clause =
      ((encodeWords (clauseWords clause)).length + 7 +
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1)) +
        (variableCount + declaredClauses + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

def lookupSteps {n : Nat} (F : Target.Formula) (prior : List (Target.Clause n))
    (clause : Target.Clause n) : Nat :=
  2 * ((formulaBits F).length + 1) + scanSteps F.«variables» F.clauses.length prior clause

theorem lookupWithSplitTrace (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior clause]
      (some ⟨some .copyOut, ((), register), base⟩) =
      some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩ := by
  have hbits : formulaBits F = encodeWords [F.«variables», F.clauses.length] ++
      (encodeWords (prior.flatMap clauseWords) ++
        (encodeWords (clauseWords clause) ++ encodeWords (after.flatMap clauseWords))) := by
    simp only [formulaBits, formulaWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .formula .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch () register
  have htapes : Function.update base .work (base .formula ++ base .work) =
      scanTapes base prior.length indexSuffix (formulaBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hformula, hindex, hwork]
  rw [htapes, hformula] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.«variables» F.clauses.length prior clause indexSuffix
    (encodeWords (after.flatMap clauseWords))

theorem output_formula {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .formula = base .formula := by
  rw [outputTapes, readSix_output_frame _ _ _ .formula (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readSix_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .work = suffix := by
  apply readSix_output_work _ _ (clauseWords_length clause) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (j : Fin 6) :
    outputTapes base clause indexSuffix suffix (.field j) =
      encodeWord ((clauseWords clause)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readSix_output_field _ _ (clauseWords_length clause)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_frame {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    outputTapes base clause indexSuffix suffix p = base p := by
  rw [outputTapes, readSix_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

theorem clauseWords_six {n : Nat} (clause : Target.Clause n) :
    clauseWords clause =
      [clause[0].variableIndex.val, if clause[0].positive then 1 else 0,
       clause[1].variableIndex.val, if clause[1].positive then 1 else 0,
       clause[2].variableIndex.val, if clause[2].positive then 1 else 0] := rfl

def fieldWords (tapes : Tape → List Bool) : List (List Bool) :=
  [tapes (.field 0), tapes (.field 1), tapes (.field 2),
   tapes (.field 3), tapes (.field 4), tapes (.field 5)]

theorem output_fieldWords {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (hempty : ∀ j : Fin 6, base (.field j) = []) :
    fieldWords (outputTapes base clause indexSuffix suffix) =
      (clauseWords clause).map encodeWord := by
  simp [fieldWords, output_field, hempty, clauseWords_six]

theorem lookupSteps_le_input (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
    (hsplit : F.clauses = prior ++ clause :: after) :
    lookupSteps F prior clause ≤ 4 * (formulaBits F).length + 10 := by
  have hlength : (formulaBits F).length = F.«variables» + F.clauses.length + 2 +
      (encodeWords (prior.flatMap clauseWords)).length +
      (encodeWords (clauseWords clause)).length +
      (encodeWords (after.flatMap clauseWords)).length := by
    simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.clauses.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 10

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 10 := by
  simp [timePolynomial]

def lookupWithSplitInTime (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) where
  steps := lookupSteps F prior clause
  evals_in_steps := lookupWithSplitTrace F prior clause after hsplit base indexSuffix
    hformula hindex hwork hscratch register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior clause after hsplit

def lookupInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  have hp : (F.clauses.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.clauses = F.clauses.take i.val ++ F.clauses[i.val] :: F.clauses.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.clauses.take i.val) F.clauses[i.val]
    (F.clauses.drop (i.val + 1)) hs base indexSuffix hformula
    (by simpa only [hp] using hindex) hwork hscratch register

def machineInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  exact lookupInTime F i base indexSuffix hformula hindex hwork hscratch register

end DFVSGames.Foundations.Hastad.SourceClauseLookup

end OAI
