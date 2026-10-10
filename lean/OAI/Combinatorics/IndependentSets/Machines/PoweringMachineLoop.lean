import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

instance : Fintype HeaderTape where
  elems := {.source, .counter, .vertices, .darts}
  complete value := by cases value <;> simp

inductive HeaderLabel
  | initialize | scan
  deriving DecidableEq

instance : Fintype HeaderLabel where
  elems := {.initialize, .scan}
  complete value := by cases value <;> simp

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

theorem stepAux_pushTrue {K Λ σ : Type} [DecidableEq K]
    (destination : K) (count : Nat) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushTrue destination count next) state tapes =
      TM2.stepAux next state
        (Function.update tapes destination (List.replicate count true ++ tapes destination)) := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih =>
    rw [pushTrue, ih]
    simp [TM2.stepAux, List.replicate_succ, Function.update_idem]

theorem pushTrue_pushBound {K Λ σ : Type} (destination : K) (count : Nat)
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (pushTrue destination count next) =
      count + Runtime.statementPushBound next := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih => simp only [pushTrue, ih, Runtime.statementPushBound]; omega

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

def headerMachine (B : Nat) : FinTM2 where
  K := HeaderTape
  k₀ := .source
  k₁ := .darts
  Γ := HeaderAlphabet
  Λ := HeaderLabel
  main := .initialize
  σ := HeaderState Unit
  initialState := ((), none)
  m := headerProgram B

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

def headerInTime {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (headerProgram B))
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩
      (some (finalConfiguration B n suffix ambient)) (n + 2) where
  steps := n + 2
  evals_in_steps := headerTrace B n suffix ambient register
  steps_le_m := Nat.le_refl _

def remainingRows (rowBlock : Nat → List Bool) (n r : Nat) : List Bool :=
  (List.range' r (n - r)).flatMap rowBlock

@[simp] theorem remainingRows_top (rowBlock : Nat → List Bool) (n : Nat) :
    remainingRows rowBlock n n = [] := by simp [remainingRows]

theorem remainingRows_step (rowBlock : Nat → List Bool) (n r : Nat) (hr : r < n) :
    remainingRows rowBlock n r = rowBlock r ++ remainingRows rowBlock n (r + 1) := by
  have h : n - r = (n - (r + 1)) + 1 := by omega
  simp only [remainingRows, h, List.range'_succ, List.flatMap_cons]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

end OAI
