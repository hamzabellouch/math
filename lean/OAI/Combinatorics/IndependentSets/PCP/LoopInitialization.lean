import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Body
import OAI.Combinatorics.IndependentSets.Machines.Initialization

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopInitialization

open IndependentSetsGames.Foundations.Complexity
open RuntimeModel LoopState

theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopInitialization
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

structure LoopResult (input : GenericGraphTables.Table q) (e remaining : Nat)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (remaining * Body.bodyTime q (LoopState.inputBits input).length + 1)

def runRemaining (input : GenericGraphTables.Table q) :
    (remaining e : Nat) → e + remaining = input.darts →
    (base : Tape → List Bool) → LoopState.Ready input e base →
    (oldRelation : GenericGraphTables.RelationTable q) → (oldFlag : Bool) →
      LoopResult input e remaining base oldRelation oldFlag
  | 0, e, finished, base, ready, oldRelation, oldFlag => by
    have atEnd : e = input.darts := by omega
    subst e
    exact {
      tapes := base
      relation := oldRelation
      flag := oldFlag
      ready := ready
      run := by
        simpa only [Nat.zero_mul, Nat.zero_add] using
          zeroGuardInTime input base ready oldRelation oldFlag }
  | remaining + 1, e, finished, base, ready, oldRelation, oldFlag => by
    have beforeEnd : e < input.darts := by omega
    let edge : Fin input.darts := ⟨e, beforeEnd⟩
    let one := Body.rowStep input edge base ready oldRelation oldFlag
    let rest := runRemaining input remaining (e + 1) (by omega) one.tapes one.ready
      input.rows[edge].relation (CompareLoop.rowLoop input edge)
    let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one.run rest.run
    refine {
      tapes := rest.tapes
      relation := rest.relation
      flag := rest.flag
      ready := rest.ready
      run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
    have budget := composed.steps_le_m
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using budget

def prefixTime (q N : Nat) : Nat :=
  Initialization.time N + N * Body.bodyTime q N + 1

structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

def runPrefix (input : GenericGraphTables.Table q) : PrefixResult input := by
  let rows := runRemaining input input.darts 0 (by simp)
    (Initialization.loopTapes input) (LoopInitialization.initialization_ready input)
    (Vector.replicate (q * q) false) false
  let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (Initialization.initializeInTime input) rows.run
  refine {
    tapes := rows.tapes
    relation := rows.relation
    flag := rows.flag
    ready := rows.ready
    run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
  have budget := composed.steps_le_m
  change composed.steps ≤
    input.darts * Body.bodyTime q (LoopState.inputBits input).length + 1 +
      Initialization.time (LoopState.inputBits input).length at budget
  have rowCount : input.darts ≤ (LoopState.inputBits input).length :=
    GenericGraphTables.darts_le_tableBits_length input
  have rowBudget := Nat.mul_le_mul_right (Body.bodyTime q (LoopState.inputBits input).length)
    rowCount
  unfold prefixTime
  omega

theorem PrefixResult.reversed {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .reversed = (GraphTables.tableBits (Table.build input)).reverse :=
  result.ready.reversed_at_end

theorem PrefixResult.output {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .output = [] := result.ready.output

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop

end OAI
