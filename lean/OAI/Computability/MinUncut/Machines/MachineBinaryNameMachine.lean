import Mathlib
import OAI.Computability.MinUncut.Machines.MachineFiniteAlphabet

namespace OAI

section
namespace MinUncutGames.BinaryNameMachine

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

theorem steps_le (input : List Bool) : steps input ≤ input.length + 1 := by
  induction input using List.twoStepInduction with
  | nil => simp [steps]
  | singleton bit => cases bit <;> simp [steps]
  | cons_cons flag bit rest ih _ =>
      cases flag <;> simp only [steps, List.length_cons]
      · omega
      · omega

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

private theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source, update_destination]

theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

def scanInTime (input output : List Bool) (last register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, last, register), tapesAt source destination base input output⟩
      (some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩)
      (input.length + 1) where
  steps := steps input
  evals_in_steps := scanTrace source destination distinct again accepted rejected program atScan
    base ambient input output last register
  steps_le_m := steps_le input

theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := State Unit
  initialState := clean ()
  m label := if label = 0 then scan false true 0 (some 1) (some 2) else .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

def machineInTime (input output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (0 : Fin 3), clean (), tapesAt false true (fun _ : Bool => []) input output⟩
      (some ⟨if (scanSpec input output none).accepted then some (1 : Fin 3) else some (2 : Fin 3),
        clean (), tapesAt false true (fun _ : Bool => [])
          (scanSpec input output none).remaining (scanSpec input output none).reversedPayload⟩)
      (input.length + 1) :=
  scanInTime false true (by decide) (0 : Fin 3) (some 1) (some 2) machine.m
    (by simp [machine]) (fun _ : Bool => []) () input output none none

end MinUncutGames.BinaryNameMachine

end
section
namespace MinUncutGames.BinaryNameCompare

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copyOut, .copyBack, .compare]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def instruction (tape : Fin 5 → K) (labels : Label → Λ)
    (equalExit differentExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
        (some (labels .copyOut)) malformedExit)
  | .copyOut => MinUncutGames.Reduction.MachineTransfer.loopAt (tape 1) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit)

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem compareTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length key.length]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let finalBase := Function.update base (tape 0) suffix
  let afterScan := Function.update finalBase (tape 2) bits.reverse
  let afterCopy := Function.update afterScan (tape 3) key
  have scanRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterScan⟩ := by
    let back := MachineStateEquiv.program (scanStateEquiv A).symm program
    have atScan : back (labels .scan) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
          (some (labels .copyOut)) malformedExit := by
      change MachineStateEquiv.statement (scanStateEquiv A).symm
        (program (labels .scan)) = _
      rw [atLabels .scan]
      exact MachineStateEquiv.statement_symm_statement (scanStateEquiv A) _
    have backForward : MachineStateEquiv.program (scanStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (scanStateEquiv A)
        (MachineStateEquiv.statement (scanStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (scanStateEquiv A).symm (program l)
    have initialTapes : MinUncutGames.Reduction.MachineTransfer.tapesAt (tape 0) (tape 2)
        base (BinaryNameMachine.frame bits ++ suffix) [] = base := by
      rw [← sourceWord, ← candidateEmpty]
      exact MinUncutGames.Reduction.MachineTransfer.tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scan) (some (labels .copyOut)) malformedExit back atScan base (ambient, false)
      bits suffix [] none
    simp only [canonical, ↓reduceIte, initialTapes, List.append_nil] at native
    have transported := MachineStateEquiv.trace (scanStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, scanStateEquiv, Equiv.coe_fn_mk, BinaryNameMachine.clean,
      clean, afterScan, finalBase, MinUncutGames.Reduction.MachineTransfer.tapesAt] using transported
  have afterScanKey : afterScan (tape 1) = key := by
    simpa [afterScan, finalBase, hd 1 2 (by decide), hd 1 0 (by decide)] using keyWord
  have afterScanCopy : afterScan (tape 3) = [] := by
    simpa [afterScan, finalBase, hd 3 2 (by decide), hd 3 0 (by decide)] using copyEmpty
  have afterScanScratch : afterScan (tape 4) = [] := by
    simpa [afterScan, finalBase, hd 4 2 (by decide), hd 4 0 (by decide)] using scratchEmpty
  have copyRun : (advance (TM2.step program))^[2 * (key.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, afterScan⟩) =
      some ⟨some (labels .compare), clean ambient, afterCopy⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .compare)) program
      (atLabels .copyOut) (atLabels .copyBack) afterScan afterScanScratch
      (ambient, false, none) none
    simpa only [afterScanKey, afterScanCopy, List.append_nil, clean, afterCopy] using h
  have candidateWord : afterCopy (tape 2) = bits.reverse := by
    simp [afterCopy, afterScan, hd 2 3 (by decide)]
  have copiedWord : afterCopy (tape 3) = key := by simp [afterCopy]
  have restored : MinUncutGames.Reduction.MachineTransfer.tapesAt (tape 2) (tape 3)
      afterCopy [] [] = finalBase := by
    funext k
    by_cases hc : k = tape 2
    · subst k
      simp [MinUncutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
        hd 2 3 (by decide), hd 2 0 (by decide), candidateEmpty]
    · by_cases hk : k = tape 3
      · subst k
        simp [MinUncutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
          hd 3 0 (by decide), copyEmpty]
      · simp [MinUncutGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, hc, hk]
  have comparisonRun : (advance (TM2.step program))^[max bits.length key.length + 1]
      (some ⟨some (labels .compare), clean ambient, afterCopy⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, finalBase⟩ := by
    let back := MachineStateEquiv.program (compareStateEquiv A).symm program
    have atCompare : back (labels .compare) =
        MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit := by
      change MachineStateEquiv.statement (compareStateEquiv A).symm
        (program (labels .compare)) = _
      rw [atLabels .compare]
      exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
    have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (compareStateEquiv A)
        (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) equalExit differentExit back atCompare afterCopy
      ambient none none
    rw [candidateWord, copiedWord, restored, List.length_reverse] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, compareStateEquiv, Equiv.coe_fn_mk, clean] using transported
  exact joinTrace (joinTrace scanRun copyRun) comparisonRun

def compareInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩)
      (2 * bits.length + 3 * key.length + 4) where
  steps := steps bits.length key.length
  evals_in_steps := compareTrace tape distinct labels equalExit differentExit malformedExit
    program atLabels base bits suffix key canonical sourceWord keyWord
    candidateEmpty copyEmpty scratchEmpty ambient
  steps_le_m := steps_le bits.length key.length

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label ⊕ Fin 3
  main := .inl .scan
  σ := State Unit
  initialState := clean ()
  m label := match label with
    | .inl l => instruction id Sum.inl (some (.inr 0)) (some (.inr 1)) (some (.inr 2)) l
    | .inr _ => .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MinUncutGames.BinaryNameCompare

end
section
namespace MinUncutGames.BinaryNameSearch

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def afterMatch : List Token → List Bool → List Token
  | [], _ => []
  | token :: tokens, key => if token.2 = key then tokens else afterMatch tokens key

def steps : List Token → List Bool → Nat
  | [], _ => 0
  | token :: tokens, key =>
      1 + BinaryNameCompare.steps token.2.length key.length +
        if token.2 = key then 0 else 1 + steps tokens key

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A

abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | sign
  | comparison (label : BinaryNameCompare.Label)
  | increment
  deriving DecidableEq, Fintype

def compareTapes (tape : Fin 6 → K) : Fin 5 → K := fun i => tape i.castSucc

omit [DecidableEq K] in
theorem compareTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (compareTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 6 => i.val) (distinct h)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt exit)

def instruction (tape : Fin 6 → K) (labels : Label → Λ)
    (foundExit missingExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .sign =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (finish (some (labels (.comparison .scan)))) (finish missingExit))
  | .comparison l => BinaryNameCompare.instruction (compareTapes tape)
      (fun l => labels (.comparison l)) foundExit (some (labels .increment)) malformedExit l
  | .increment => .push (tape 5) (fun _ => true) (.goto fun _ => labels .sign)

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1, base⟩ := by
  cases exit <;> rfl

private theorem update_source (source counter : K) (distinct : source ≠ counter)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) source replacement =
      tapesAt source counter base replacement count := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hc : k = counter
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hc]

private theorem update_counter (source counter : K)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) counter replacement =
      tapesAt source counter base input replacement := by
  simp [tapesAt]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (foundExit missingExit malformedExit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) =
  instruction tape labels foundExit missingExit malformedExit l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem signStep (sign : Bool) (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (sign :: input) counter⟩ =
      some ⟨some (labels (.comparison .scan)), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source]

theorem emptyStep (counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base [] counter⟩ =
      some ⟨missingExit, clean ambient, tapesAt (tape 0) (tape 5) base [] counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source]

omit distinct in
theorem incrementStep (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ =
      some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base input (true :: counter)⟩ := by
  change some (TM2.stepAux (program (labels .increment)) _ _) = _
  rw [atLabels .increment]
  simp [instruction, TM2.stepAux, update_counter]

theorem tokenTrace (token : Token) (key suffix counter : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[1 + BinaryNameCompare.steps token.2.length key.length]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨if token.2 = key then foundExit else some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base suffix counter⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := tapesAt (tape 0) (tape 5) base
    (BinaryNameMachine.frame token.2 ++ suffix) counter
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨some (labels (.comparison .scan)), clean ambient, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, tokenBits, List.cons_append] using
      signStep tape distinct labels foundExit missingExit malformedExit program atLabels
        base ambient token.1 (BinaryNameMachine.frame token.2 ++ suffix) counter
  have second := BinaryNameCompare.compareTrace (compareTapes tape)
    (compareTapes_injective tape distinct) (fun l => labels (.comparison l))
    foundExit (some (labels .increment)) malformedExit program
    (fun l => atLabels (.comparison l)) initial token.2 suffix key.reverse canonical
    (by simp [initial, compareTapes, hd 0 5 (by decide)])
    (by simpa [initial, compareTapes, tapesAt,
      hd 1 0 (by decide), hd 1 5 (by decide)] using keyWord)
    (by simpa [initial, compareTapes, tapesAt, hd 2 0 (by decide), hd 2 5 (by decide)]
      using candidateEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 3 0 (by decide), hd 3 5 (by decide)] using copyEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 4 0 (by decide), hd 4 5 (by decide)] using scratchEmpty)
    ambient
  have heq : token.2.reverse = key.reverse ↔ token.2 = key := by
    constructor
    · intro h
      have := congrArg List.reverse h
      simpa only [List.reverse_reverse] using this
    · intro h; rw [h]
  simp only [List.length_reverse, heq] at second
  rw [show Function.update initial (compareTapes tape 0) suffix =
      tapesAt (tape 0) (tape 5) base suffix counter by
    exact update_source _ _ (hd 0 5 (by decide)) base _ counter suffix] at second
  exact joinTrace first second

theorem searchTrace (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps tokens key]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
      some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩ := by
  induction tokens generalizing counter with
  | nil => simp at present
  | cons token tokens ih =>
      have headCanonical := canonical token (by simp)
      have tailCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true :=
        fun t ht => canonical t (by simp [ht])
      have first := tokenTrace tape distinct labels foundExit missingExit malformedExit
        program atLabels base ambient token key (stream tokens ++ suffix) counter
        headCanonical keyWord candidateEmpty copyEmpty scratchEmpty
      by_cases same : token.2 = key
      · simpa only [steps, same, ite_true, Nat.add_zero, stream_cons,
          List.append_assoc, afterMatch, payloads_cons, List.idxOf_cons_self,
          List.replicate_zero, List.nil_append] using first
      · have remaining : key ∈ payloads tokens := by
          rcases List.mem_cons.mp present with equal | remaining
          · exact False.elim (same equal.symm)
          · exact remaining
        have increment : (advance (TM2.step program))^[1]
            (some ⟨some (labels .increment), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
            some ⟨some (labels .sign), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) (true :: counter)⟩ := by
          simpa only [Function.iterate_one, advance_some] using
            incrementStep tape labels foundExit missingExit malformedExit program
              atLabels base ambient (stream tokens ++ suffix) counter
        have rest := ih (true :: counter) tailCanonical remaining
        simp only [same, ite_false] at first
        have full := joinTrace first (joinTrace increment rest)
        have counterEq : List.replicate ((payloads tokens).idxOf key) true ++
            (true :: counter) =
            List.replicate ((payloads tokens).idxOf key + 1) true ++ counter := by
          rw [List.replicate_succ']
          simp only [List.append_assoc, List.singleton_append]
        have indexEq : (token.2 :: payloads tokens).idxOf key =
            (payloads tokens).idxOf key + 1 := by
          exact List.idxOf_cons_ne _ same
        simpa only [steps, same, ite_false, stream_cons, List.append_assoc, afterMatch,
          payloads_cons, indexEq, counterEq] using full

def searchInTime (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩
      (some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩)
      ((3 * key.length + 7) * (stream tokens).length) where
  steps := steps tokens key
  evals_in_steps := searchTrace tape distinct labels foundExit missingExit malformedExit
    program atLabels base ambient tokens key suffix counter canonical present keyWord
      candidateEmpty copyEmpty scratchEmpty
  steps_le_m := steps_le_stream tokens key

end Program

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label ⊕ Fin 3
  main := .inl .sign
  σ := State Unit
  initialState := clean ()
  m label := match label with
    | .inl l => instruction id Sum.inl (some (.inr 0)) (some (.inr 1)) (some (.inr 2)) l
    | .inr _ => .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MinUncutGames.BinaryNameSearch

end

end OAI
