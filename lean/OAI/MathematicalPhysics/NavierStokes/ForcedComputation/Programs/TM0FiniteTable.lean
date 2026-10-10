import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MachinePartialStep
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.List.OfFn

namespace OAI

/-! Compile finite TM0 tables into the finite table presentation used by the
fluid theorems.  A move writes back the symbol that was read; a write uses the
stationary move. -/

namespace ForcedComputation.FiniteMachine

open Alternating Turing

def encodeAction {g q : ℕ} (a : Fin (g + 1)) :
    Fin (q + 1) × TM0.Stmt (Fin (g + 1)) → Instruction
  | (r, .move .left) => (r.val, a.val, 0)
  | (r, .move .right) => (r.val, a.val, 2)
  | (r, .write b) => (r.val, b.val, 1)

def compileTM0 {g q : ℕ} (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) : Machine :=
  (q, g, ∅, List.ofFn fun r => List.ofFn fun a => (M r a).map (encodeAction a))

@[simp] theorem compileTM0_stateCount {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    (compileTM0 M).stateCount = q + 1 := rfl

@[simp] theorem compileTM0_symbolCount {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    (compileTM0 M).symbolCount = g + 1 := rfl

theorem encodeAction_bounds {g q : ℕ} (a : Fin (g + 1))
    (s : Fin (q + 1) × TM0.Stmt (Fin (g + 1))) :
    (encodeAction a s).1 < q + 1 ∧ (encodeAction a s).2.1 < g + 1 := by
  rcases s with ⟨r, s⟩
  cases s with
  | move d => cases d <;> exact ⟨r.isLt, a.isLt⟩
  | write b => exact ⟨r.isLt, b.isLt⟩

theorem compileTM0_wellFormed {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) :
    (compileTM0 M).WellFormed := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · simp [compileTM0, Machine.haltingStates]
  · intro row hr
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨List.length_ofFn, ?_⟩
    intro i hi
    obtain ⟨a, ha⟩ := List.mem_ofFn.mp hi
    obtain ⟨s, _, rfl⟩ := Option.map_eq_some_iff.mp ha
    exact encodeAction_bounds a s

@[simp] theorem compileTM0_instruction {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (r : Fin (q + 1)) (a : Fin (g + 1)) :
    (compileTM0 M).instruction r.val a.val = (M r a).map (encodeAction a) := by
  change (((List.ofFn (fun r => List.ofFn (fun a =>
    (M r a).map (encodeAction a))))[r.val]?).bind
      (fun row => row[a.val]?)).join = _
  simp only [List.getElem?_ofFn, r.isLt, a.isLt, ↓reduceDIte,
    Option.bind_some, Option.join_some]

@[simp] theorem compileTM0_not_halting {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1))) (r : Fin (q + 1)) :
    (compileTM0 M).isHalting r.val = false := by
  change decide (r.val = q + 1 ∨ r.val ∈ (∅ : Finset ℕ)) = false
  simp only [Finset.notMem_empty, or_false, decide_eq_false_iff_not,
    ne_of_lt r.isLt, not_false_eq_true]

def compileTM0Input {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (w : List (Fin (g + 1))) : MachineInput :=
  (compileTM0 M, w.map Fin.val)

theorem compileTM0Input_valid {g q : ℕ}
    (M : TM0.Machine (Fin (g + 1)) (Fin (q + 1)))
    (w : List (Fin (g + 1))) : ValidInput (compileTM0Input M w) := by
  refine ⟨compileTM0_wellFormed M, ?_⟩
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact b.isLt

end ForcedComputation.FiniteMachine

end OAI
