import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderTableRows

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderTable

section

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def oldTableWord {v d : Nat} (G : Table v (degree d)) : List Bool :=
  encodeWords (rotationWords G)

def accumulatedVertices {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) : List Bool :=
  accumulate (priorVertices G H current) []

@[simp] theorem accumulatedVertices_zero {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H 0 = [] := by
  simp [accumulatedVertices, accumulate]

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

def vertexBodyBudget {v d : Nat} (G : Table v (degree d)) : Nat :=
  rowFactor d * (80 * ((oldTableWord G).length + 1) + 2)

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

private def boundarySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

def vertexLoopInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool)
    (count : current + remaining = v) (position : state.2 = zeroPosition positive) :
    VertexLoopRun positive G H current remaining state suffix := by
  induction remaining generalizing current state with
  | zero =>
      have hc : current = v := by omega
      subst current
      refine ⟨clearRegister state, caller_clearRegister state, ?_, ?_⟩
      · simpa only [clearRegister] using position
      · simpa only [vertexLoopBudget, Nat.zero_mul, Nat.zero_add, vertexLoopTapes] using
          boundarySingleStep _ _ _ (vertexGuard_boundary_zeroStep positive H v (oldTableWord G)
            (accumulatedVertices G H v) suffix [] state)
  | succ remaining ih =>
      have valid : current < v := by omega
      let vertex : Fin v := ⟨current, valid⟩
      let body := vertexInTime positive G H vertex (clearRegister state)
        (by simpa only [clearRegister] using position) remaining
        (accumulatedVertices G H current) suffix []
      have nextCount : current + 1 + remaining = v := by omega
      let rest := ih (current + 1) body.finalState nextCount body.position_zero
      have output_eq : accumulate (vertexWords G H vertex)
          (accumulatedVertices G H current) = accumulatedVertices G H (current + 1) :=
        (accumulatedVertices_succ G H current valid).symm
      let guard := boundarySingleStep _ _ _
        (vertexGuard_boundary_succStep positive H current remaining (oldTableWord G)
          (accumulatedVertices G H current) suffix [] state)
      have bodyRun : StateTransition.EvalsToInTime (TM2.step (program positive H))
          ⟨some (.inr .prepareRow), clearRegister state,
            boundaryTapes current remaining (oldTableWord G)
              (accumulatedVertices G H current) suffix []⟩
          (some ⟨some (.inr .vertexGuard), body.finalState,
            vertexLoopTapes G H (current + 1) remaining suffix⟩)
          (vertexBodyBudget G) := by
        simpa only [vertexLoopTapes, vertexBodyBudget, oldTableWord, output_eq] using body.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ guard bodyRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ first rest.execution
      refine ⟨rest.finalState, ?_, rest.position_zero, ?_⟩
      · exact rest.caller_preserved.trans
          (body.caller_preserved.trans (caller_clearRegister state))
      · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [vertexLoopBudget, Nat.succ_mul] at bound ⊢
        omega

end

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).2 = state.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.2 = none := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 1) where
  steps := output.length + 1
  evals_in_steps := reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.Complexity.MachineExpanderTable

end OAI
