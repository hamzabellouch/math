import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineStart

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

private theorem mapIdx_ofFn {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.«variables» 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.«variables» i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.«variables» 0 F.clauses ++
          RawInitialRows.dummyWords F.«variables» F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .«variables» => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

theorem decrement_counter (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i (remaining + 1) input reversed)
      Tape.counter (encodeWord remaining) = loopTapes n i remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes]

theorem increment_index (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i remaining input reversed)
      Tape.index (true :: encodeWord i) = loopTapes n (i + 1) remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes, encodeWord, List.replicate_succ]

end IndependentSetsGames.Foundations.PCP.RawInitialMachineLoopData
namespace IndependentSetsGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

private theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

def loadSignsInTime (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .loadSigns, state, base⟩
      (some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩) 1 where
  steps := 1
  evals_in_steps := loadSigns_step base a b c ha hb hc state
  steps_le_m := Nat.le_refl _

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end IndependentSetsGames.Foundations.PCP.RawInitialMachinePhases

end OAI
