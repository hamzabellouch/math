import Mathlib.Computability.TuringMachine.StackTuringMachine
import OAI.Computability.BinPacking.Reductions.MachineSubstitution
import OAI.Computability.BinPacking.Reductions.MachineTransfer

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

theorem stepAux_preserves_extra_state (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    (stepAux (statement haltTarget q) (state, extraState)
      (tapes source extraTapes)).var.2 = extraState := by
  rw [stepAux_simulation]
  rfl

theorem stepAux_preserves_extra_tape (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) (e : E) :
    (stepAux (statement haltTarget q) (state, extraState)
      (tapes source extraTapes)).stk (.inr e) = extraTapes e := by
  rw [stepAux_simulation]
  rfl

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end BinPackingGames.Foundations.Complexity.MachineEmbedding

namespace BinPackingGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

theorem tapes_involutive (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    tapes (tapes source) = source := by
  funext k
  rcases k with a | b | c <;> rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

def program (source : Λ → Stmt (Alphabet ΓA ΓB ΓC) Λ σ) :
    Λ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ := fun l => statement (source l)

theorem step_simulation (source : Λ → Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    step (program source) (configuration c) = (step source c).map configuration := by
  cases c with
  | mk l state sourceTapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement (source l)) state (tapes sourceTapes)) = _
      rw [stepAux_simulation]
      rfl

end BinPackingGames.Foundations.Complexity.MachineStackSwap

namespace BinPackingGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

def fourPhaseExecution {σ : Type} (step : σ → Option σ)
    (start afterFirst afterTransfer₁ afterTransfer₂ : σ) (finish : Option σ)
    (first second intermediate : Polynomial Nat) (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength)
    (runFirst : StateTransition.EvalsToInTime step start (some afterFirst) (first.eval inputLength))
    (transfer₁ : StateTransition.EvalsToInTime step afterFirst (some afterTransfer₁)
      (intermediateLength + 1))
    (transfer₂ : StateTransition.EvalsToInTime step afterTransfer₁ (some afterTransfer₂)
      (intermediateLength + 1))
    (runSecond : StateTransition.EvalsToInTime step afterTransfer₂ finish
      (second.eval intermediateLength)) :
    StateTransition.EvalsToInTime step start finish
      ((compositionPolynomial first second intermediate).eval inputLength) := by
  let firstTwo := StateTransition.EvalsToInTime.trans step _ _ start afterFirst
    (some afterTransfer₁) runFirst transfer₁
  let firstThree := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₁
    (some afterTransfer₂) firstTwo transfer₂
  let allFour := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₂
    finish firstThree runSecond
  refine {
    toEvalsTo := allFour.toEvalsTo
    steps_le_m := Nat.le_trans allFour.steps_le_m ?_
  }
  have bounded := compositionBudget_le first second intermediate inputLength intermediateLength
    intermediateBound
  omega

end BinPackingGames.Foundations.Complexity.MachineComposition

namespace BinPackingGames.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

def forkLoop (source left right : K) (fallback : β) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push left (fun state => state.2.getD fallback)
        (.push right (fun state => state.2.getD fallback) (.goto fun _ => loopLabel)))
      (Reduction.MachineTransfer.exitAt right exit))

def forkTapes (source left right : K) (base : K → List β)
    (input leftOutput rightOutput : List β) : K → List β :=
  Function.update (Function.update (Function.update base source input) left leftOutput)
    right rightOutput

@[simp] theorem forkTapes_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput source = input := by
  simp [forkTapes, sourceLeft, sourceRight]

@[simp] theorem forkTapes_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput left = leftOutput := by
  simp [forkTapes, leftRight]

@[simp] theorem forkTapes_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput right = rightOutput := by
  simp [forkTapes]

@[simp] theorem forkTapes_self (source left right : K) (base : K → List β) :
    forkTapes source left right base (base source) (base left) (base right) = base := by
  simp [forkTapes]

private theorem update_fork_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      source replacement = forkTapes source left right base replacement leftOutput rightOutput := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, sourceLeft, sourceRight]
  · by_cases hl : k = left
    · subst k; simp [forkTapes, Ne.symm sourceLeft, leftRight]
    · by_cases hr : k = right
      · subst k; simp [forkTapes, Ne.symm sourceRight]
      · simp [forkTapes, hs, hl, hr]

private theorem update_fork_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      left replacement = forkTapes source left right base input replacement rightOutput := by
  funext k
  by_cases hl : k = left
  · subst k; simp [forkTapes, leftRight]
  · by_cases hr : k = right
    · subst k; simp [forkTapes, Ne.symm leftRight]
    · simp [forkTapes, hl, hr]

private theorem update_fork_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      right replacement = forkTapes source left right base input leftOutput replacement := by
  simp [forkTapes]

theorem forkStep_empty (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (leftOutput rightOutput : List β) (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), forkTapes source left right base [] leftOutput rightOutput⟩ =
        some ⟨exit, (ambient, none), forkTapes source left right base [] leftOutput rightOutput⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base [] leftOutput rightOutput)) = _
  rw [atLoop]
  cases exit <;>
    simp [forkLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, sourceLeft, sourceRight,
      leftRight, update_fork_source]

theorem forkStep_cons (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (head : β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩ =
      some ⟨some loopLabel, (ambient, some head),
        forkTapes source left right base input (head :: leftOutput) (head :: rightOutput)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base (head :: input) leftOutput rightOutput)) = _
  rw [atLoop]
  simp [forkLoop, TM2.stepAux, sourceLeft, sourceRight, leftRight,
    update_fork_source, update_fork_left, update_fork_right]

theorem forkTrace (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register),
        forkTapes source left right base input leftOutput rightOutput⟩) =
      some ⟨exit, (ambient, none), forkTapes source left right base []
        (input.reverse ++ leftOutput) (input.reverse ++ rightOutput)⟩ := by
  induction input generalizing leftOutput rightOutput register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, List.reverse_nil, List.nil_append] using
        forkStep_empty source left right sourceLeft sourceRight leftRight fallback loopLabel exit
          program atLoop base leftOutput rightOutput ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩) = _
    rw [forkStep_cons source left right sourceLeft sourceRight leftRight fallback loopLabel exit
      program atLoop base head input leftOutput rightOutput ambient register, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def forkInTime (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), forkTapes source left right base []
        ((base source).reverse ++ base left) ((base source).reverse ++ base right)⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) = _
    simpa only [forkTapes_self] using
      forkTrace source left right sourceLeft sourceRight leftRight fallback loopLabel exit
        program atLoop base (base source) (base left) (base right) ambient register
  steps_le_m := Nat.le_refl _

def drainedTapes (source scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse

theorem restoredTapes (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    forkTapes scratch source destination (drainedTapes source scratch base) []
      (base source) (base source ++ base destination) =
        Function.update base destination (base source ++ base destination) := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [forkTapes, sourceDestination]
  · by_cases hd : k = destination
    · subst k; simp [forkTapes]
    · by_cases ht : k = scratch
      · subst k
        simp [forkTapes, Ne.symm sourceScratch, Ne.symm destinationScratch, scratchEmpty]
      · simp [forkTapes, drainedTapes, Reduction.MachineTransfer.tapesAt, hs, hd, ht]

theorem copyTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id fallback firstLabel (some secondLabel) program atFirst base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  have second := forkTrace scratch source destination (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) sourceDestination fallback secondLabel exit program atSecond
    (drainedTapes source scratch base)
    (drainedTapes source scratch base scratch) (drainedTapes source scratch base source)
    (drainedTapes source scratch base destination) ambient none
  simp only [forkTapes_self] at second
  have scratchWord : drainedTapes source scratch base scratch = (base source).reverse := by
    simp [drainedTapes]
  have sourceWord : drainedTapes source scratch base source = [] := by
    simp [drainedTapes, sourceScratch]
  have destinationWord : drainedTapes source scratch base destination = base destination := by
    simp [drainedTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  rw [scratchWord, sourceWord, destinationWord] at second
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at second
  rw [restoredTapes source destination scratch sourceDestination sourceScratch destinationScratch
    base scratchEmpty] at second
  rw [show 2 * ((base source).length + 1) =
    ((base source).length + 1) + ((base source).length + 1) by omega,
    Function.iterate_add_apply, first]
  exact second

def copyInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) where
  steps := 2 * ((base source).length + 1)
  evals_in_steps := copyTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel exit program atFirst atSecond base
    scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.MachineCopy

namespace BinPackingGames.Foundations.Complexity.MachineDrain

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

end BinPackingGames.Foundations.Complexity.MachineDrain

namespace BinPackingGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

private theorem update_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

private theorem update_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

private theorem update_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

def affineInTime (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩
      (some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩)
      (2 * (a + 1)) where
  steps := 2 * (a + 1)
  evals_in_steps := affineTrace source scratch destination hs hd hsd coefficient scanLabel
    restoreLabel exit program atScan atRestore base a b suffix output ambient register
  steps_le_m := Nat.le_refl _

theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

inductive Label
  | seed | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan, .restore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def program (source scratch destination : K) (coefficient offset : Nat) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .seed => seed destination offset .scan
  | .scan => scan source scratch destination coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false .restore none

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program 0 1 2 coefficient offset

end BinPackingGames.Foundations.Complexity.MachineUnaryAffineAt

namespace BinPackingGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def zeroTest (operand : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek operand (fun s head => (s.1, head))
    (.load (fun s => ((s.1.1, !(s.2.getD false)), none))
      (Reduction.MachineTransfer.exitAt operand exit))

theorem zeroTestTrace (operand : K) (testLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atTest : program testLabel = zeroTest operand exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (word : base operand = encodeWord n ++ suffix)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some testLabel, ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (n = 0)), none), base⟩ := by
  change some (TM2.stepAux (program testLabel) _ _) = _
  rw [atTest]
  cases n <;> cases exit <;>
    simp [zeroTest, TM2.stepAux, word, encodeWord, List.replicate_succ,
      Reduction.MachineTransfer.exitAt]

def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .scan => scan slots (labels .scan) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (slots 2) (slots 0) id false
      (labels .restoreLeft) (some (labels .restoreRight))
  | .restoreRight => Reduction.MachineTransfer.loopAt (slots 3) (slots 1) id false
      (labels .restoreRight) exit

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

theorem lessThanTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none), base⟩ := by
  have h := comparisonTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    ambient flag register
  have hframe := tapes_self slots base
  rw [leftWord, rightWord, leftEmpty, rightEmpty] at hframe
  rw [hframe] at h
  exact h

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 3 * Polynomial.X + Polynomial.C 3

theorem steps_le_time (a b : Nat) : steps a b ≤ timePolynomial.eval (a + b) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have := Nat.min_le_left a b
  omega

def lessThanInPolynomialTime (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), ((ambient, flag), register), base⟩
      (some ⟨exit, ((ambient, decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) where
  steps := steps a b
  evals_in_steps := lessThanTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    leftWord rightWord leftEmpty rightEmpty ambient flag register
  steps_le_m := steps_le_time a b

abbrev machine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := State Unit
  initialState := (((), false), none)
  m := statement (Function.Embedding.refl _) id none

def machineInPolynomialTime (base : Fin 4 → List Bool) (a b : Nat)
    (leftSuffix rightSuffix : List Bool)
    (leftWord : base 0 = encodeWord a ++ leftSuffix)
    (rightWord : base 1 = encodeWord b ++ rightSuffix)
    (leftEmpty : base 2 = []) (rightEmpty : base 3 = []) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .scan, (((), false), none), base⟩
      (some ⟨none, (((), decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) :=
  lessThanInPolynomialTime (Function.Embedding.refl _) id none machine.m (fun _ => rfl)
    base a b leftSuffix rightSuffix leftWord rightWord leftEmpty rightEmpty () false none

end BinPackingGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
