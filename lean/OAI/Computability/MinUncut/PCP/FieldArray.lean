import Mathlib
import OAI.Computability.MinUncut.Machines.Machine

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceFieldArray

open Turing
open MinUncutGames.Foundations.Complexity SourceMachine

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

end MinUncutGames.Foundations.Hastad.SourceFieldArray

end

end OAI
