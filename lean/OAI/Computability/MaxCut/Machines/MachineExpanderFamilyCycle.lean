import Mathlib
import OAI.Computability.MaxCut.Machines.Runtime2
import OAI.Computability.MaxCut.Machines.MachineExpanderTableRows

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem cleaned_multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    fromBoolTapes (cleanedCounterTapes
      (toBoolTapes (multipliedFrame d remaining current newWord suffix))) =
      boundaryTapes remaining (current * cloudSize d) newWord suffix := by
  rw [boundaryTapes_eq_cycleTapes]
  unfold multipliedFrame
  rw [toBool_cycleTapes]
  have multiply : cloudSize d * current = current * cloudSize d := Nat.mul_comm _ _
  rw [multiply]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

structure ResizeRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr (.affine .copyCount .seed)), state,
      boundaryTapes remaining v (MachineExpanderTable.oldTableWord G) suffix⟩
    (some ⟨some (.inr .levelGuard), finalState,
      boundaryTapes remaining (v * cloudSize d)
        (encodeWords (rotationWords (step G H))) suffix⟩)
    (resizeCost G H)

/-- The resize certificate is built from actual primitive and table executions;
its caller supplies no phase trace or computational hypothesis. -/
noncomputable def resizeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    ResizeRun positive H growth G remaining state suffix := by
  let oldWord := MachineExpanderTable.oldTableWord G
  let newWord := encodeWords (rotationWords (step G H))
  have copy := copyCountInTime positive H growth
    (boundaryTapes remaining v oldWord suffix) v rfl rfl rfl state
  rw [copyFrame_eq_update] at copy
  let called := MachineExpanderTable.tableInTime positive G H (clearRegister state).1 []
  let returned : State ρ d := (called.finalState, ())
  have eta : ((clearRegister state).1, ()) = clearRegister state := by
    rcases state with ⟨state, extra⟩
    cases extra
    rfl
  have call : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inl (.inr .initialize)), clearRegister state,
        copyFrame remaining v oldWord suffix⟩
      (some ⟨some (.inr .clearOldTable), returned,
        returnFrame remaining v oldWord newWord suffix⟩)
      ((MachineExpanderTable.timePolynomial d).eval oldWord.length) := by
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, tableReturn, eta,
      copyFrame, returnFrame, oldWord, newWord, returned] using
      tableExecution positive H growth (extraFrame remaining v suffix) called.execution
  have install := installTableInTime positive H growth
    (returnFrame remaining v oldWord newWord suffix) newWord
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl)
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl) returned
  rw [installed_returnFrame] at install
  have installRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), returned, returnFrame remaining v oldWord newWord suffix⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister returned,
        installedFrame remaining v newWord suffix⟩)
      (oldWord.length + 2 * newWord.length + (v + 1) + 4) := by
    simpa only [returnFrame_eq_cycleTapes, toBool_cycleTapes, cycleWords, tableTape,
      encodeWord_length] using install
  have multiply := multiplySizeInTime positive H growth
    (installedFrame remaining v newWord suffix) v rfl rfl rfl (clearRegister returned)
  rw [clearRegister_idempotent, multipliedFrame_eq_update] at multiply
  have clean := cleanupCountersInTime positive H growth
    (multipliedFrame d remaining v newWord suffix) (clearRegister returned)
  rw [clearRegister_idempotent, cleaned_multipliedFrame] at clean
  have cleanRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), clearRegister returned,
        multipliedFrame d remaining v newWord suffix⟩
      (some ⟨some (.inr .levelGuard), clearRegister returned,
        boundaryTapes remaining (v * cloudSize d) newWord suffix⟩) (v + 4) := by
    simpa only [multipliedFrame, toBool_cycleTapes, cycleWords, inputVertexTape,
      vertexCountTape, encodeWord_length, Nat.zero_add, Nat.add_assoc] using clean
  let a := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ copy call
  let b := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ a installRun
  let c := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ b multiply
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ c cleanRun
  refine ⟨clearRegister returned, ?_, ?_⟩
  · exact (caller_clearRegister returned).trans
      (called.caller_preserved.trans (caller_clearRegister state))
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    unfold resizeCost
    change _ ≤ (MachineExpanderTable.timePolynomial d).eval oldWord.length +
      6 * v + oldWord.length + 2 * newWord.length + 15
    omega

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_initialState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) : caller (initialState positive H ambient) = ambient := rfl

@[simp] theorem caller_normalizeState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (normalizeState positive H state) = caller state := rfl

@[simp] theorem clearRegister_initialState (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) :
    clearRegister (initialState positive H ambient) = initialState positive H ambient := rfl

/-- The guard changes only the physical remaining-level word. -/
theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

/-- The two literal prefixes install the actual level-zero table and unary one. -/
theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

/-- Static alphabet transport preserves this actual single transition. -/
theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

/-- The literal initialization executes in one transition of the actual program. -/
theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

/-- A positive level physically loses one true bit, retaining its delimiter and suffix. -/
theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

/-- The zero delimiter is retained when the family loop enters its final halt. -/
theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

noncomputable def levelLoopCost {d : Nat} (H : Table (cloudSize d) d) : Nat → Nat → Nat
  | _, 0 => 1
  | start, remaining + 1 => 1 + resizeCost (family H start) H +
      levelLoopCost H (start + 1) remaining

theorem levelLoopCost_prefix {d : Nat} (H : Table (cloudSize d) d) (start remaining : Nat) :
    levelLoopCost H start remaining + resizeSum H start =
      resizeSum H (start + remaining) + remaining + 1 := by
  induction remaining generalizing start with
  | zero => simp [levelLoopCost, Nat.add_comm]
  | succ remaining ih =>
      have h := ih (start + 1)
      rw [resizeSum_succ] at h
      have index : start + 1 + remaining = start + (remaining + 1) := by omega
      rw [index] at h
      simp only [levelLoopCost]
      omega

theorem levelLoopCost_zero_start {d : Nat} (H : Table (cloudSize d) d) (remaining : Nat) :
    levelLoopCost H 0 remaining = resizeSum H remaining + remaining + 1 := by
  simpa only [resizeSum_zero, Nat.add_zero, Nat.zero_add] using
    levelLoopCost_prefix H 0 remaining

def levelLoopTapes {d : Nat} (H : Table (cloudSize d) d)
    (completed remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes remaining (vertexCount (degree d) completed)
    (encodeWords (rotationWords (family H completed))) suffix

structure LevelLoopRun {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr .levelGuard), state, levelLoopTapes H completed remaining suffix⟩
    (some ⟨some (.inr .done), finalState, familyTapes H (completed + remaining) suffix⟩)
    (levelLoopCost H completed remaining)

private def familySingleStep_inline_MachineExpanderFamilyLoop {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

/-- Every body is the already constructed actual resize run. There is no
whole-loop, body-trace, or computational-correctness premise. -/
noncomputable def levelLoopInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    LevelLoopRun positive H growth completed remaining state suffix := by
  induction remaining generalizing completed state with
  | zero =>
      refine ⟨clearRegister state, caller_clearRegister state, ?_⟩
      simpa only [levelLoopCost, levelLoopTapes, familyTapes, Nat.add_zero] using
        familySingleStep_inline_MachineExpanderFamilyLoop _ _ _ (levelGuard_boundary_zeroStep positive H growth
          (vertexCount (degree d) completed) (encodeWords (rotationWords (family H completed)))
          suffix state)
  | succ remaining ih =>
      let cycle := resizeInTime positive H growth (family H completed) remaining
        (clearRegister state) suffix
      let rest := ih (completed + 1) cycle.finalState
      let guard := familySingleStep_inline_MachineExpanderFamilyLoop _ _ _ (levelGuard_boundary_succStep positive H growth
        remaining (vertexCount (degree d) completed)
        (encodeWords (rotationWords (family H completed))) suffix state)
      have cycleRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
          ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
            levelLoopTapes H completed remaining suffix⟩
          (some ⟨some (.inr .levelGuard), cycle.finalState,
            levelLoopTapes H (completed + 1) remaining suffix⟩)
          (resizeCost (family H completed) H) := cycle.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ guard cycleRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ first rest.execution
      have index : completed + 1 + remaining = completed + (remaining + 1) := by omega
      refine ⟨rest.finalState, ?_, ?_⟩
      · exact rest.caller_preserved.trans
          (cycle.caller_preserved.trans (caller_clearRegister state))
      · rw [index] at all
        refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [levelLoopCost]
        omega

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

private def singleFamilyStep_inline_MachineExpanderFamily {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

/-- Complete initialization, actual counted loop, and normalized halt. -/
noncomputable def familyInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      (familyBudget H level) := by
  let loop := levelLoopInTime positive H growth 0 level
    (initialState positive H (caller state)) suffix
  have initialRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩) 1 :=
    singleFamilyStep_inline_MachineExpanderFamily _ _ _ (initialize_boundaryStep positive H growth level suffix state)
  have finalCaller : caller loop.finalState = caller state := loop.caller_preserved
  have done : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩) 1 := by
    simpa only [normalizeState, finalCaller] using
      singleFamilyStep_inline_MachineExpanderFamily _ _ _ (doneStep positive H growth (familyTapes H level suffix)
        loop.finalState)
  have loopRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩
      (some ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩)
      (levelLoopCost H 0 level) := by simpa only [Nat.zero_add] using loop.execution
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ initialRun loopRun
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ first done
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  have bound := all.steps_le_m
  have costEquality := levelLoopCost_zero_start H level
  unfold familyBudget
  omega

/-- The actual complete computation is polynomial in the final full vertex
count; the level is never silently treated as an equally long input. -/
noncomputable def familyInOutputSizeTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      ((resizeCoefficient d + 4) * (vertexCount (degree d) level + 1)^5) where
  toEvalsTo := (familyInTime positive H growth level state suffix).toEvalsTo
  steps_le_m := (familyInTime positive H growth level state suffix).steps_le_m.trans
    (familyBudget_le H growth level)

theorem baseDegree_cloud_growth :
    cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
  unfold cloudSize degree PCP.ExpanderFamily.growth
  ring

theorem baseDegree_cloud_gt_one : 1 < cloudSize PCP.Expanders.baseDegree := by
  rw [baseDegree_cloud_growth]
  exact PCP.ExpanderFamily.growth_gt_one

theorem baseDegree_positive : 0 < PCP.Expanders.baseDegree := by
  have h := baseDegree_cloud_gt_one
  unfold cloudSize degree at h
  by_contra hn
  have hz : PCP.Expanders.baseDegree = 0 := by omega
  rw [hz] at h
  norm_num at h

/-- At the physically computable padding level, the actual family run has a
fixed polynomial bound in requested unary size. The separate ceiling-power
machine supplies this exact level and preserves the requested size. -/
noncomputable def paddedFamilyInTime {ρ : Type} [Fintype ρ]
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree)
    (requested : Nat) (state : State ρ PCP.Expanders.baseDegree) (suffix : List Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (program baseDegree_positive H baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize), state,
        initialTapes (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩
      (some ⟨none, initialState baseDegree_positive H (caller state),
        familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩)
      (inputCoefficient * (requested + 1)^5) where
  toEvalsTo := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).toEvalsTo
  steps_le_m := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).steps_le_m.trans
      (familyBudget_at_boundedLevel_le H requested)

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev fixedDegree := PCP.Expanders.baseDegree
abbrev SmallTable := Table (cloudSize fixedDegree) fixedDegree
abbrev Tape := MachineExpanderFamily.Tape ⊕ MachineCeilingPower.Tape
abbrev Alphabet (_ : Tape) := Bool
abbrev Label := MachineExpanderFamily.Label fixedDegree ⊕ MachineCeilingPower.Label
abbrev State (ρ : Type) := MachineExpanderFamily.State ρ fixedDegree × (Bool × Option Bool)

def familyTape (tape : MachineExpanderFamily.Tape) : Tape := .inl tape

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl tape => some tape
  | .inr _ => none

@[simp] theorem familyView_left (tape : MachineExpanderFamily.Tape) :
    familyView (familyTape tape) = some tape := rfl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

/-- The only shared tape is the level: the first phase writes the exact word
that the second phase's unary guard consumes. -/
def ceilingTape : MachineCeilingPower.Tape → Tape
  | .level => .inl (.inr .remainingLevel)
  | tape => .inr tape

def ceilingView : Tape → Option MachineCeilingPower.Tape
  | .inl (.inr .remainingLevel) => some .level
  | .inl _ => none
  | .inr .level => none
  | .inr tape => some tape

@[simp] theorem ceilingView_left (tape : MachineCeilingPower.Tape) :
    ceilingView (ceilingTape tape) = some tape := by
  cases tape <;> rfl

theorem ceilingView_right (j : Tape) (tape : MachineCeilingPower.Tape)
    (h : ceilingView j = some tape) : ceilingTape tape = j := by
  cases j with
  | inl j =>
    cases j with
    | inl j => simp [ceilingView] at h
    | inr j => cases j <;> simp_all [ceilingView, ceilingTape] ; cases h ; rfl
  | inr j => cases j <;> simp_all [ceilingView, ceilingTape] <;> cases h <;> rfl

def familyLabel (label : MachineExpanderFamily.Label fixedDegree) : Label := .inl label
def ceilingLabel (label : MachineCeilingPower.Label) : Label := .inr label
def main : Label := .inr .init
def familyEntry : Label := .inl (.inr .initialize)

def ceilingStates (ρ : Type) :
    MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree) ≃ State ρ :=
  Equiv.prodAssoc _ _ _

@[simp] theorem ceilingStates_apply (ρ : Type)
    (state : MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree)) :
    ceilingStates ρ state = (state.1.1, (state.1.2, state.2)) := rfl

variable {ρ : Type} [Fintype ρ]

/-- The family retains the completed ceiling machine's two finite registers. -/
def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

/-- The ceiling program preserves the family state as its ambient component. -/
def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

/-- Actual composition on shared Boolean tapes. No runtime bridge operation
is required, because both programs use the same physical level tape. -/
def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label (State ρ)
  | .inl label =>
    MachineCloudPadding.Placement.statement familyTape familyLabel none (familySource H label)
  | .inr label =>
    MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
      (ceilingSource (ρ := ρ) label)

@[simp] theorem program_family (H : SmallTable)
    (label : MachineExpanderFamily.Label fixedDegree) :
    program (ρ := ρ) H (familyLabel label) =
      MachineCloudPadding.Placement.statement familyTape familyLabel none
        (familySource H label) := rfl

@[simp] theorem program_ceiling (H : SmallTable) (label : MachineCeilingPower.Label) :
    program (ρ := ρ) H (ceilingLabel label) =
      MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
        (ceilingSource (ρ := ρ) label) := rfl

/-- Initial state for an arbitrary preserved family-state component. -/
def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

/-- Only the unary request is initially present. -/
def initialTapes (requested : Nat) : Tape → List Bool
  | .inr .input => encodeWord requested
  | _ => []

def retainedCeilingTapes (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) [] [] [] [] []

def handoffTapes (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

def finalTapes (H : SmallTable) (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

@[simp] theorem initialTapes_input (requested : Nat) :
    initialTapes requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_input (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_power (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .power) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := rfl

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def ceilingInput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) [] [] [] [] [] [] []

def ceilingOutput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) []
    (encodeWord (PCP.PreprocessingLevels.boundedLevel requested)) [] [] []

def retainedFrame (requested : Nat) : Tape → List Bool
  | .inl _ => []
  | .inr tape => retainedCeilingTapes requested tape

theorem ceiling_initial_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingInput requested) (fun _ => []) =
      initialTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rfl
    · cases tape <;> rfl
  · cases tape <;> rfl

/-- The produced unary level is already on the exact family input tape. -/
theorem ceiling_handoff_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingOutput requested) (fun _ => []) =
      handoffTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rcases tape with tape | tape
      · cases tape <;> rfl
      · cases tape <;> rfl
    · cases tape <;>
        simp [Placement.tapes, ceilingView, ceilingOutput, handoffTapes,
          MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
          MachineExpanderFamily.initialTapes, MachineEmbedding.tapes,
          MachineCeilingPower.memory]
  · cases tape <;> rfl

theorem family_initial_tapes (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = handoffTapes requested := by
  funext tape
  cases tape <;> rfl

theorem family_final_tapes (H : SmallTable) (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = finalTapes H requested := by
  funext tape
  cases tape <;> rfl

theorem ceiling_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨some .init, ((state, false), register), ceilingInput requested⟩) =
      ⟨some main, initialState state register, initialTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_initial_tapes, ceilingLabel, main, initialState]

/-- Ceiling halt enters the family initializer with no intervening transition. -/
theorem ceiling_handoff_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨none, ((state, false), none), ceilingOutput requested⟩) =
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_handoff_tapes]

/-- Static alphabet and state framing of the actual family initial endpoint. -/
theorem family_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (metadata : Bool × Option Bool) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration metadata
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨some (.inr .initialize), state,
            MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨some familyEntry, (state, metadata), handoffTapes requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_initial_tapes, familyEntry, familyLabel]

/-- The family endpoint retains both external ceiling words and its original
normalized state; its remaining-level word is the consumed zero word. -/
theorem family_final_configuration {ρ : Type} (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration (false, none)
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨none,
            MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
              (MachineExpanderFamily.caller state),
            MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨none, finalState H state, finalTapes H requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_final_tapes, finalState]

@[simp] theorem handoffTapes_level (requested : Nat) :
    handoffTapes requested (ceilingTape .level) =
      encodeWord (PCP.PreprocessingLevels.boundedLevel requested) := by
  simp [handoffTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
    MachineEmbedding.tapes]

@[simp] theorem handoffTapes_level_shadow (requested : Nat) :
    handoffTapes requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_level_shadow (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_remainingLevel (H : SmallTable) (requested : Nat) :
    finalTapes H requested (ceilingTape .level) = encodeWord 0 := by
  simp [finalTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
    MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
    MachineEmbedding.tapes]

theorem finalTapes_currentSize (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape (.inr .currentSize)) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := by
  change encodeWord (vertexCount (degree fixedDegree)
    (PCP.PreprocessingLevels.boundedLevel requested)) = _
  exact congrArg encodeWord (PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize requested)

theorem finalTapes_table (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape MachineExpanderFamily.tableTape) =
      encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel requested))) := rfl

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
