import Mathlib
import OAI.Computability.MinUncut.Machines.MachineUnaryCounter

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCompare

open Turing
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

private theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

private theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

private theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

theorem drained_other (left right k : K) (notLeft : k ≠ left) (notRight : k ≠ right)
    (base : K → List Bool) : tapesAt left right base [] [] k = base k :=
  tapesAt_other left right k notLeft notRight base [] []

def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end MinUncutGames.Foundations.Complexity.MachineCompare

namespace MinUncutGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

def program (labels : Λ ≃ Λ') (states : σ ≃ σ') (source : Λ → Stmt Γ Λ σ) :
    Λ' → Stmt Γ Λ' σ' := fun l => statement labels states (source (labels.symm l))

theorem step_simulation (labels : Λ ≃ Λ') (states : σ ≃ σ')
    (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program labels states source) (configuration labels states c) =
      (step source c).map (configuration labels states) := by
  cases c with
  | mk l state tapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement labels states (source (labels.symm (labels l))))
        (states state) tapes) = _
      rw [Equiv.symm_apply_apply, stepAux_simulation]
      rfl

end MinUncutGames.Foundations.Complexity.MachineControl

namespace MinUncutGames.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

theorem equalityProfile_encodeWord {q : Nat} (names : Fin q → Nat) (i j : Fin q) :
    equalityProfile (fun k => encodeWord (names k)) i j = decide (names i = names j) := by
  have h : encodeWord (names i) = encodeWord (names j) ↔ names i = names j := by
    constructor
    · intro heq
      have hh := congrArg List.length heq
      simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
    · rintro heq
      rw [heq]
  simp only [equalityProfile, h]

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

section PreservedComparison
variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end PreservedComparison

def setEntry {q : Nat} (profile : Profile q) (pair : Fin q × Fin q) (bit : Bool) : Profile q :=
  Function.update profile pair.1 (Function.update (profile pair.1) pair.2 bit)

theorem setEntry_apply {q : Nat} (profile : Profile q) (pair : Fin q × Fin q)
    (bit : Bool) (i j : Fin q) :
    setEntry profile pair bit i j = if (i, j) = pair then bit else profile i j := by
  rcases pair with ⟨a, b⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [setEntry, hi, hj]

def setExpected {q : Nat} (words : Fin q → List Bool) (profile : Profile q)
    (pair : Fin q × Fin q) : Profile q :=
  setEntry profile pair (equalityProfile words pair.1 pair.2)

def foldProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) : Profile q := cells.foldl (setExpected words) initial

theorem foldProfile_apply {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (i j : Fin q) :
    foldProfile words initial cells i j =
      if (i, j) ∈ cells then equalityProfile words i j else initial i j := by
  induction cells generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    change foldProfile words (setExpected words initial pair) rest i j = _
    rw [ih]
    by_cases hrest : (i, j) ∈ rest
    · simp [hrest]
    · by_cases hpair : (i, j) = pair
      · subst pair
        simp [hrest, setExpected, setEntry_apply]
      · simp [hrest, hpair, setExpected, setEntry_apply]

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3
abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def storePair {q : Nat} (pair : Fin q × Fin q) (bit : Bool)
    {Λ : Type} (nextLabel : Λ) :
    TM2.Stmt (fun _ : Tape q => Bool) Λ (MachineCompare.State (Profile q)) :=
  .load (fun state => normalState (setEntry state.1 pair bit)) (.goto fun _ => nextLabel)

def profileProgram {q : Nat} (cells : List (Fin q × Fin q)) (label : Label cells) :
    TM2.Stmt (fun _ : Tape q => Bool) (Label cells) (MachineCompare.State (Profile q)) :=
  if h : label.1.val < cells.length then
    let pair := cells[label.1.val]
    let r := label.1.val
    match label.2.val with
    | 0 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.1) (.inr 2) id false
        (labelAt cells r 0) (some (labelAt cells r 1)))
    | 1 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.1) (.inr 0) false
        (labelAt cells r 1) (some (labelAt cells r 2)))
    | 2 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.2) (.inr 2) id false
        (labelAt cells r 2) (some (labelAt cells r 3)))
    | 3 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.2) (.inr 1) false
        (labelAt cells r 3) (some (labelAt cells r 4)))
    | 4 => MachineCompare.loop (.inr 0) (.inr 1) (labelAt cells r 4)
        (some (labelAt cells r 5)) (some (labelAt cells r 6))
    | 5 => storePair pair true (labelAt cells (r + 1) 0)
    | _ => storePair pair false (labelAt cells (r + 1) 0)
  else .halt

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) : Profile q :=
  foldProfile words initial (cells.take r)

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixProfile_succ {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixProfile words initial cells (r + 1) =
      setExpected words (prefixProfile words initial cells r) cells[r] := by
  unfold prefixProfile foldProfile
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append]
  rfl

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

def stageInTime {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length)
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (profile : Profile q) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells r 0), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile cells[r]), base⟩)
      (pairTime (fun i => base (.inl i)) cells[r]) := by
  let pair := cells[r]
  have copied := nonDestructiveCompareInTime (.inl pair.1) (.inl pair.2)
    (.inr 0 : Tape q) (.inr 1) (.inr 2) (by simp) (by simp) (by simp)
    (labelAt cells r 0) (labelAt cells r 1) (labelAt cells r 2) (labelAt cells r 3)
    (labelAt cells r 4) (some (labelAt cells r 5)) (some (labelAt cells r 6))
    (profileProgram cells)
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr])
    base (hwork 0) (hwork 1) (hwork 2) profile
  have stored : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
        else some (labelAt cells r 6), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile pair), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
          else some (labelAt cells r 6), normalState profile, base⟩ = _
      by_cases heq : base (.inl pair.1) = base (.inl pair.2)
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  dsimp only [pair] at h
  dsimp only [pairTime]
  omega

def prefixInTime {q : Nat} (cells : List (Fin q × Fin q))
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (r : Nat) (hr : r ≤ cells.length) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells 0 0), normalState initial, base⟩
      (some ⟨some (labelAt cells r 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells r), base⟩)
      (prefixTime (fun i => base (.inl i)) cells r) := by
  induction r with
  | zero =>
    exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  | succ r ih =>
    have hrl : r < cells.length := by omega
    let first := ih (by omega)
    let second := stageInTime cells r hrl base hwork
      (prefixProfile (fun i => base (.inl i)) initial cells r)
    let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
    rw [prefixProfile_succ _ _ _ _ hrl, prefixTime_succ _ _ _ hrl]
    exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem foldProfile_allPairs {q : Nat} (words : Fin q → List Bool) (initial : Profile q) :
    foldProfile words initial (allPairs q) = equalityProfile words := by
  funext i j
  simp [foldProfile_apply, mem_allPairs]

def profileMachine (q : Nat) : FinTM2 where
  K := Tape q
  k₀ := .inr 0
  k₁ := .inr 0
  Γ _ := Bool
  Λ := Label (allPairs q)
  main := labelAt (allPairs q) 0 0
  σ := MachineCompare.State (Profile q)
  initialState := normalState (fun _ _ => false)
  m := profileProgram (allPairs q)

def profileInTime (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (((allPairs q).map (pairTime (fun i => base (.inl i)))).sum + 1) := by
  let cells := allPairs q
  have first := prefixInTime cells base hwork initial cells.length (Nat.le_refl _)
  have last : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells cells.length 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨some (labelAt cells cells.length 0),
          normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩ = _
      simp [TM2.step, profileProgram, labelAt, TM2.stepAux,
        prefixProfile, cells, foldProfile_allPairs]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simpa [prefixTime, cells, Nat.add_comm] using h

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def profileInTime_bounded (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (L : Nat) (hL : ∀ i, (base (.inl i)).length ≤ L) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (q * q * (5 * L + 6) + 1) := by
  let run := profileInTime q base hwork initial
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  apply Nat.add_le_add_right
  simpa only [length_allPairs] using totalTime_le (fun i => base (.inl i)) L hL (allPairs q)

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

end OAI
