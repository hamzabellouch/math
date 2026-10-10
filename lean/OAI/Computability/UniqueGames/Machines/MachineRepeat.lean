import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
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

private theorem inputTapes_update_input (M : FinTM2)
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

private theorem inputTapes_update_counter (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

private def oneStep {α : Type*} (step : α → Option α) (a b : α)
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
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
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
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter, inputConfig]

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

private theorem bodyToTemp_tapes (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
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

private theorem tempToBody_tapes (word counter : List (M.Γ M.k₀)) :
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

private theorem finalToTemp_tapes (word : List (M.Γ M.k₀)) :
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

private theorem tempToOutput_tapes (word : List (M.Γ M.k₀)) :
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
  rw [hs,hd,List.append_nil,bodyToTemp_tapes] at run
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
        inputTapes M word.reverse counter from tempToBody_tapes M word counter] at run
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
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes] at run
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
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes] at run
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
  have guard := oneStep _ _ _ (guardStep_none M input output word)
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
    have guard := oneStep _ _ _ (guardStep_some M input output ((words 0).map input.symm)
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

private theorem inputConfig_init (word : List (M.Γ M.k₀)) :
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
  rw [inputConfig_init M input output] at full
  erw [List.map_append]
  simpa only [TM2OutputsInTime, Option.map_some, Nat.add_comm] using! full

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

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
