import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSequential
import OAI.Computability.MaxCut.Machines.MachineUnaryAffine
import OAI.Computability.MaxCut.Encoding.FormulaEncoding
import OAI.Computability.MaxCut.Games.TranslationTarget

namespace OAI

/-! Intermediate tape-space bounds derived from actual successful machine
prefixes, and their use in the separately checked physical finalizer. -/

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

/-- All stacks are counted, even when their symbol types differ. -/
def configurationLength (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

theorem initial_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    configurationLength tm (initList tm input) = input.length := by
  have point (k : tm.K) : ((initList tm input).stk k).length =
      if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, h]
  simp [configurationLength, point]

theorem step_configurationLength (tm : FinTM2) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    configurationLength tm b ≤ configurationLength tm a +
      Fintype.card tm.K * Runtime.programPushBound tm := by
  calc
    _ ≤ ∑ k : tm.K, ((a.stk k).length + Runtime.programPushBound tm) :=
      Finset.sum_le_sum (fun k _ => Runtime.stepStackLength tm k a b transition)
    _ = _ := by simp [configurationLength, Finset.sum_add_distrib]

/-- Every successfully executed prefix bounds the space in its actual endpoint. -/
theorem execution_configurationLength (tm : FinTM2) {start finish : tm.Cfg}
    {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    configurationLength tm finish ≤ configurationLength tm start +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) :=
  Runtime.executionSizeBound tm.step (configurationLength tm)
    (Fintype.card tm.K * Runtime.programPushBound tm) (step_configurationLength tm) run

theorem prefix_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget) :
    configurationLength tm finish ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simpa only [initial_configurationLength] using execution_configurationLength tm run

noncomputable def spacePolynomial (tm : FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X + time * Polynomial.C (Fintype.card tm.K * Runtime.programPushBound tm)

theorem spacePolynomial_eval (tm : FinTM2) (time : Polynomial Nat) (N : Nat) :
    (spacePolynomial tm time).eval N = N +
      time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simp [spacePolynomial]

theorem prefix_length_polynomial (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {finish : tm.Cfg}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      (time.eval input.length)) :
    configurationLength tm finish ≤ (spacePolynomial tm time).eval input.length := by
  rw [spacePolynomial_eval]
  exact prefix_configurationLength tm input run

/-- This equality only identifies the actual endpoint stacks with a Boolean
finalizer's stacks. It makes no execution or time assumption. -/
theorem totalLength_eq_configurationLength (tm : FinTM2) (finish : tm.Cfg)
    (base : tm.K → List Bool)
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.totalLength base = configurationLength tm finish := by
  exact Finset.sum_congr rfl (fun k _ => sameLengths k)

/-- The actual physical finalizer's cost is bounded by the space reached by
the actual prefix. Repeated cleanup keys remain permitted. -/
theorem finishCost_le_of_prefix (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget)
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.finishCost clearKeys accumulator base ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) + clearKeys.length + 2 := by
  rw [SourceRuntimeFinish.finishCost_eq_totalLength clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty,
    totalLength_eq_configurationLength tm finish base sameLengths]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (prefix_configurationLength tm input run) clearKeys.length) 2

noncomputable def completedTime (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) : Polynomial Nat :=
  time + spacePolynomial tm time + Polynomial.C (clearKeyCount + 2)

theorem completedTime_eval (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) (N : Nat) :
    (completedTime tm clearKeyCount time).eval N = time.eval N +
      (N + time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm)) +
      (clearKeyCount + 2) := by
  simp [completedTime, spacePolynomial_eval]

/-- Composition retains both actual execution witnesses. The cleanup witness
is supplied by `SourceRuntimeFinish.finishInTime` in the caller's real program. -/
def prefixAndFinishInTime (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {middle finish : tm.Cfg}
    (prefixRun : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some middle) (time.eval input.length))
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (middle.stk k).length)
    (finishRun : StateTransition.EvalsToInTime tm.step middle (some finish)
      (SourceRuntimeFinish.finishCost clearKeys accumulator base)) :
    StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      ((completedTime tm clearKeys.length time).eval input.length) := by
  have joined := StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ prefixRun finishRun
  have hc := finishCost_le_of_prefix tm input prefixRun clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty sameLengths
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  rw [completedTime_eval]
  omega

end MaxCutGames.Foundations.Hastad.SourceRuntimeSpace

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace MaxCutGames.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_getElem?_ctorIdx_eq (x : Phase) :
    Phase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s v => (s.1,v))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.push (.inr .counter) (fun _ => input.symm true)
          (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .parse))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .guard))))
  | .guard => .pop (.inr .counter) (fun s v => (s.1,v))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.main)))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .finalToTemp))))
  | .bodyToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₁) (.inr .temporary)
      (fun b => input.symm (output b)) (input.symm false)
      (.inr .bodyToTemp) (some (.inr .tempToBody))
  | .tempToBody => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inl M.k₀)
      id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
  | .finalToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₀) (.inr .temporary)
      id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
  | .tempToOutput => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inr .output)
      id (input.symm false) (.inr .tempToOutput) none

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .bodyToTemp)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState,none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

private theorem inputTapes_update_input_inline_MachineRepeat (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

private theorem inputTapes_update_counter_inline_MachineRepeat (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

private def oneStep_inline_MachineRepeat {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_true (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm true :: word) counter) =
    some (inputConfig M .parse word (input.symm true :: counter)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm true :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input_inline_MachineRepeat, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input_inline_MachineRepeat, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some]
      using! parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simpa only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.map_nil, List.singleton_append, List.append_assoc] using! h

theorem guardStep_some (word counter : List (M.Γ M.k₀)) (symbol : M.Γ M.k₀) :
    (machine M input output).step (inputConfig M .guard word (symbol :: counter)) =
      some (embedded M counter (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word (symbol :: counter))) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter_inline_MachineRepeat,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter_inline_MachineRepeat,
    inputConfig]

/-- Lift the actual certified body run while preserving the remaining counter. -/
def bodyExecution (counter : List (M.Γ M.k₀))
    (word : List (M.Γ M.k₀)) (result : List (M.Γ M.k₁)) (budget : Nat)
    (run : TM2OutputsInTime M word (some result) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (initList M word))
      (some (embedded M counter (haltList M result))) budget :=
  MachineComposition.embeddedExecution (some (.inr .bodyToTemp : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M counter [] []) M.m
    (auxProgram M input output) run

private theorem bodyToTemp_tapes_inline_MachineRepeat (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

private theorem tempToBody_tapes_inline_MachineRepeat (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem finalToTemp_tapes_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem tempToOutput_tapes_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inr .output)
      (temporaryTapes M word []) [] word.reverse =
        (haltList (machine M input output) word.reverse).stk := by
  funext k
  cases k with
  | inl k => simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList, machine]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList,
      machine, extraTapes]; rfl

def bodyToTemp (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (temporaryConfig M .tempToBody
        (result.reverse.map (fun b => input.symm (output b))) counter)) (result.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₁) (.inr .temporary) (by intro h; cases h)
    (fun b => input.symm (output b)) (input.symm false)
    (.inr .bodyToTemp) (some (.inr .tempToBody)) (program M input output) rfl
    (embedded M counter (haltList M result)).stk M.initialState none
  have hs : (embedded M counter (haltList M result)).stk (.inl M.k₁) = result := by
    simp [embedded, MachineEmbedding.configuration, haltList]
  have hd : (embedded M counter (haltList M result)).stk (.inr .temporary) = [] := rfl
  rw [hs,hd,List.append_nil,bodyToTemp_tapes_inline_MachineRepeat] at run
  exact run

def tempToBody (word counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToBody word counter)
      (some (inputConfig M .guard word.reverse counter)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inl M.k₀) (by intro h; cases h)
    id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
    (program M input output) rfl (temporaryTapes M word counter) M.initialState none
  simp only [temporaryTapes, MachineEmbedding.tapes, extraTapes,
    List.map_id, List.append_nil] at run
  rw [show Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])) [] word.reverse =
        inputTapes M word.reverse counter from tempToBody_tapes_inline_MachineRepeat M word counter] at run
  exact run

def finalToTemp (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .finalToTemp word [])
      (some (temporaryConfig M .tempToOutput word.reverse [])) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₀) (.inr .temporary) (by intro h; cases h)
    id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
    (program M input output) rfl (inputTapes M word []) M.initialState none
  have hd : inputTapes M word [] (.inr .temporary) = [] := rfl
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes_inline_MachineRepeat] at run
  exact run

def tempToOutput (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToOutput word [])
      (some (haltList (machine M input output) word.reverse)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .tempToOutput) none
    (program M input output) rfl (temporaryTapes M word []) M.initialState none
  have hs : temporaryTapes M word [] (.inr .temporary) = word := rfl
  have hd : temporaryTapes M word [] (.inr .output) = [] := rfl
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes_inline_MachineRepeat] at run
  exact run

/-- Transfer the literal body output back to the input, preserving its order. -/
def bodyReturn (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (inputConfig M .guard (result.map (fun b => input.symm (output b))) counter))
      (2*(result.length+1)) := by
  have first := bodyToTemp M input output result counter
  have second := tempToBody M input output (result.reverse.map (fun b => input.symm (output b))) counter
  simp only [List.map_reverse,List.reverse_reverse,List.length_reverse,List.length_map] at first second
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

/-- Zero remaining iterations still run the actual final transfers and halt
with every tape other than the designated output empty. -/
def finish (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard word []) (some (haltList (machine M input output) word))
      (2*word.length+3) := by
  have guard := oneStep_inline_MachineRepeat _ _ _ (guardStep_none M input output word)
  have first := finalToTemp M input output word
  have second := tempToOutput M input output word.reverse
  simp only [List.reverse_reverse,List.length_reverse] at second
  have gfirst := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard first
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ gfirst second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

/-- Running time after the parser: actual body budgets, two transfers per
body result, one guard per iteration, and the final transfer and empty guard. -/
def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

def loopExecution (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))
      (some (haltList (machine M input output) ((words count).map input.symm)))
      (loopBudget count words budgets) := by
  induction count generalizing words budgets with
  | zero =>
    simpa only [loopBudget,List.replicate_zero,List.length_map] using!
      finish M input output ((words 0).map input.symm)
  | succ count ih =>
    rw [List.replicate_succ]
    have guard := oneStep_inline_MachineRepeat _ _ _ (guardStep_some M input output ((words 0).map input.symm)
      (List.replicate count (input.symm true)) (input.symm true))
    have body := bodyExecution M input output (List.replicate count (input.symm true))
      ((words 0).map input.symm) ((words 1).map output.symm) (budgets 0)
      (runs 0 (Nat.zero_lt_succ count))
    have returned := bodyReturn M input output ((words 1).map output.symm)
      (List.replicate count (input.symm true))
    have handoff : ((words 1).map output.symm).map (fun b => input.symm (output b)) =
        (words 1).map input.symm := by
      simp only [List.map_map,Function.comp_def,Equiv.apply_symm_apply]
    rw [handoff,List.length_map] at returned
    have tail := ih (fun i => words (i+1)) (fun i => budgets (i+1))
      (fun i hi => runs (i+1) (Nat.succ_lt_succ hi))
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first returned
    have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second tail
    exact {
      toEvalsTo := full.toEvalsTo
      steps_le_m := by
        have h := full.steps_le_m
        simp only [loopBudget]
        omega
    }

private theorem inputConfig_init_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    inputConfig M .parse word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes,initList,machine]; rfl
    · simp [inputTapes,initList,machine,h]
  | inr k => cases k <;> simp [inputTapes,initList,machine,extraTapes]

def executeSequence (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + loopBudget count words budgets) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])
      (some (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))) (count+1) := {
    steps := count+1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[count+1]
        (some (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])) = _
      simpa only [List.append_nil] using! parseTrace M input output count
        ((words 0).map input.symm) []
    steps_le_m := le_refl _
  }
  have body := loopExecution M input output count words budgets runs
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed body
  rw [inputConfig_init_inline_MachineRepeat M input output] at full
  have input_append := @List.map_append Bool
    ((machine M input output).Γ (machine M input output).k₀) input.symm
    (encodeWord count) (words 0)
  simpa only [TM2OutputsInTime, Option.map_some, input_append, Nat.add_comm] using! full

omit M input output in
/-- Explicit sum form of the actual repeat budget. -/
theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

/-- The sum of supplied body budgets and explicit linear transfer overheads. -/
def executeSequenceSum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + ((∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) +
        2*(words count).length+3)) := by
  rw [← loopBudget_eq_sum]
  exact executeSequence M input output count words budgets runs

omit M input output in
/-- A uniform bound along the executed sequence is enough to bound the actual
repeat runtime. No polynomial growth of an arbitrary iteration is asserted. -/
theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i<count → budgets i ≤ bodyBound)
    (hl : ∀i, i≤count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end MaxCutGames.Foundations.Complexity.MachineRepeat

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-- Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/
def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

/-- This one alphabet is already finite in the underlying machine record. -/
theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

/-- All concrete Boolean-stack machines satisfy the stronger alphabet condition. -/
theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

theorem of_equiv (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k ≃ α) : FiniteAlphabet M := by
  intro k
  exact Finite.of_equiv α (alphabet k).symm

theorem symbols_finite (M : FinTM2) (finiteAlphabet : FiniteAlphabet M) :
    Finite (Σ k, M.Γ k) := by
  let := M.kFin
  let : ∀ k, Finite (M.Γ k) := finiteAlphabet
  infer_instance

/-- The first two tape groups retain their original alphabets. The sole new
bridge tape uses the second machine's already finite input alphabet. -/
theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

/-- Preservation for the machine actually stored in the polynomial-time
composition certificate, with its actual relabeling bridge. -/
theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

/-- Counter, temporary, and output tapes of the actual repeat machine all use
the body's finite input alphabet; body tapes retain their original alphabets. -/
theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace MaxCutGames.Explicit.MachineUniformRun

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineUniformProgram

def outputBits (C n q Q : Nat) (body : List Bool) : List Bool :=
  encodeWords [n, q, C * Q] ++ MachineUniformCopyOrder.copyMajor C body

def afterScale (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineUniformHeaders.resultTapes n q Q body)
    .newOccurrences (encodeWord (C * Q))

def afterEmit (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterScale C n q Q body)
    .accumulator (outputBits C n q Q body)

def scaleInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩
      (some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩)
      (2 * (Q + 1) + 1) where
  steps := 2 * (Q + 1) + 1
  evals_in_steps := by
    change (MachineComposition.advance (machine C).step)^[2 * (Q + 1) + 1]
      (some ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩) =
      some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
    have h := MachineUnaryAffineAt.seededAffineTrace Tape.occurrences .affineScratch
      .newOccurrences (by decide) (by decide) (by decide) C 0
      (.scale 0 : Label C) (.scale 1) (.scale 2) (some (emitEntry C))
      (program C) rfl rfl rfl (MachineUniformHeaders.resultTapes n q Q body)
      Q [] (by simp [MachineUniformHeaders.resultTapes])
      (by simp [MachineUniformHeaders.resultTapes]) ((), ()) none
    simpa only [machine, FinTM2.step, FinTM2.Cfg,
      initialState, afterScale,
      show MachineUniformHeaders.resultTapes n q Q body .newOccurrences = [] from rfl,
      Nat.add_zero, List.append_nil] using! h
  steps_le_m := Nat.le_refl _

theorem repeated_template (C : Nat) (fields : Fin 4 → List Bool) :
    MachineFieldTemplate.templateOutput (List.replicate C (.copy 3)) fields =
      MachineUniformCopyOrder.copyMajor C (fields 3) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput,
      MachineUniformCopyOrder.copyMajor, List.flatten_cons] at *
    rw [ih]

theorem template_output (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) = outputBits C n q Q body := by
  simp only [tokens, MachineFieldTemplate.templateOutput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, MachineFieldTemplate.tokenOutput]
  rw [show (List.replicate C (MachineFieldTemplate.Token.copy (3 : Fin 4))).flatMap
      (MachineFieldTemplate.tokenOutput (fun i => afterScale C n q Q body (emitField i))) =
        MachineUniformCopyOrder.copyMajor C (afterScale C n q Q body (emitField 3)) from
      repeated_template C _]
  simp [afterScale, MachineUniformHeaders.resultTapes, emitField, outputBits,
    encodeWords, List.append_assoc]

theorem template_copiedLength (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) =
        n + q + C * Q + 3 + C * body.length := by
  simp [MachineFieldTemplate.copiedLength, tokens, afterScale,
    MachineUniformHeaders.resultTapes, emitField, Nat.add_assoc] ; omega

def emitInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      (3 * (n + q + C * Q + 3 + C * body.length) + 3 * (C + 3) + 1) := by
  have h := MachineFieldTemplate.phaseInTime (tokens C) emitField
    Tape.copyScratch .accumulator
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by decide)
    (Label.emit (C := C)) (some .finishStart) (program C) (fun _ => rfl)
    (afterScale C n q Q body) (by simp [afterScale, MachineUniformHeaders.resultTapes])
    initialState
  simpa only [machine, FinTM2.step, FinTM2.Cfg, emitEntry,
    MachineFieldTemplate.reset, initialState,
    template_output, template_copiedLength, afterEmit,
    show (tokens C).length = C + 3 by simp [tokens]] using! h

noncomputable def prefixPolynomial (C : Nat) : Polynomial Nat :=
  Polynomial.C (3 * C + 6) * Polynomial.X + Polynomial.C (3 * C + 16)

theorem input_length (n q Q : Nat) (body : List Bool) :
    (encodeWords [n, q, Q] ++ body).length = n + q + Q + 3 + body.length := by
  simp [Nat.add_assoc]

def prefixInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      ((prefixPolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let first := MachineUniformHeaders.headersInTime C q n Q body
  let second := scaleInTime C n q Q body
  let third := emitInTime C n q Q body
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, input_length]
  have hcopy : n + q + C * Q + 3 + C * body.length ≤
      (C + 1) * (n + q + Q + 3 + body.length) := by nlinarith
  nlinarith

noncomputable def timePolynomial (C : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine C) clearKeys.length (prefixPolynomial C + 1)

theorem haltList_eq (C : Nat) (bits : List Bool) :
    haltList (machine C) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (C : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program C .finishStart) initialState base) = _
    rfl
  steps_le_m := Nat.le_refl _

/-- The complete actual run, including the physical cleanup and output reversal. -/
noncomputable def outputInTime (C n q Q : Nat) (body : List Bool) :
    TM2OutputsInTime (machine C) (encodeWords [n, q, Q] ++ body)
      (some (outputBits C n q Q body))
      ((timePolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let initialRun := prefixInTime C n q Q body
  let bridge := finishStartInTime C (afterEmit C n q Q body)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun bridge
  let prefixRun : StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState,
        afterEmit C n q Q body⟩)
      ((prefixPolynomial C + 1).eval (encodeWords [n, q, Q] ++ body).length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm]
      using joined.steps_le_m }
  have hout : afterEmit C n q Q body .output = [] := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  let finish := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (C := C)) none (program C) (fun _ => rfl)
    (afterEmit C n q Q body) hout ((), ()) none
  let whole := SourceRuntimeSpace.prefixAndFinishInTime (machine C)
    (encodeWords [n, q, Q] ++ body) (prefixPolynomial C + 1) prefixRun
    clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys covers (afterEmit C n q Q body) hout (fun _ => rfl) finish
  have hword : (afterEmit C n q Q body .accumulator).reverse = outputBits C n q Q body := by
    simp [afterEmit, MachineFieldTemplate.outputTapes, afterScale,
      MachineUniformHeaders.resultTapes]
  change StateTransition.EvalsToInTime (machine C).step _
    (some (haltList (machine C) (outputBits C n q Q body))) _
  rw [haltList_eq, ← hword]
  exact whole

/-- A fixed actual program works for every game and every alphabet size. -/
noncomputable def computation {q : Nat} (C : Nat) (hC : 0 < C) :
    TM2ComputableInPolyTime gameBits gameBits (UniformTarget.construct (q := q) C hC) where
  tm := machine C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial C
  outputsFun g := by
    change TM2OutputsInTime (machine C) ((gameBits g).map id)
      (some ((gameBits (UniformTarget.construct C hC g)).map id)) _
    have hi := @List.map_id ((machine C).Γ (machine C).k₀) (gameBits g)
    have ho := @List.map_id ((machine C).Γ (machine C).k₁)
      (gameBits (UniformTarget.construct C hC g))
    simp only [hi, ho]
    rw [UniformTarget.gameBits_construct]
    have input : gameBits g = encodeWords [g.vertices, q, g.constraints.length] ++
        encodeWords (g.constraints.flatMap constraintWords) := by
      simp [gameBits, gameWords, encodeWords, List.append_assoc]
    rw [input]
    exact outputInTime C g.vertices q g.constraints.length
      (encodeWords (g.constraints.flatMap constraintWords))

theorem finiteAlphabet {q : Nat} (C : Nat) (hC : 0 < C) :
    MachineFiniteAlphabet.FiniteAlphabet (computation (q := q) C hC).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end MaxCutGames.Explicit.MachineUniformRun

end OAI
