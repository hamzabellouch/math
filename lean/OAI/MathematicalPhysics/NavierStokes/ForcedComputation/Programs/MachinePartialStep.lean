import OAI.MathematicalPhysics.NavierStokes.Material.Model
import Mathlib.Computability.StateTransition

namespace OAI

/-! Partial execution semantics for the finite table model.  A missing table
entry stops this semantics immediately; the existing total semantics records
the same event by entering its distinguished terminal state. -/

namespace ForcedComputation.FiniteMachine

open Alternating

def partialStep (M : Machine) (c : Configuration) : Option Configuration :=
  if M.isHalting c.state then none else
    (M.instruction c.state (c.tape c.head)).map fun i =>
      { state := i.1
        head := c.head + (i.2.2.val : ℤ) - 1
        tape := Function.update c.tape c.head i.2.1 }

theorem step_of_partialStep_some (M : Machine) {c c' : Configuration}
    (h : partialStep M c = some c') : M.step c = c' := by
  unfold partialStep at h
  split at h
  · contradiction
  · rename_i hn
    cases hi : M.instruction c.state (c.tape c.head) with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, Option.map_some, Option.some.injEq] at h
      simp only [Machine.step, hn, Bool.false_eq_true, ↓reduceIte, hi]
      exact h

theorem halting_after_partialStep_none (M : Machine) {c : Configuration}
    (h : partialStep M c = none) : M.isHalting (M.step c).state = true := by
  unfold partialStep at h
  split at h
  · rename_i hh
    rw [Machine.step, ite_eq_left hh]
    exact hh
  · rename_i hn
    have hi : M.instruction c.state (c.tape c.head) = none := by
      simpa only [Option.map_eq_none_iff] using h
    rw [Machine.step, ite_eq_right hn, hi]
    simp [Machine.isHalting]

theorem partialStep_none_of_halting (M : Machine) {c : Configuration}
    (h : M.isHalting c.state = true) : partialStep M c = none := by
  simp only [partialStep, h, ↓reduceIte]

theorem reaches_iterate (M : Machine) {c c' : Configuration}
    (h : StateTransition.Reaches (partialStep M) c c') :
    ∃ n : ℕ, M.step^[n] c = c' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail b d _ hd ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hn]
    exact step_of_partialStep_some M hd

theorem eval_dom_iff (M : Machine) (c : Configuration) :
    (StateTransition.eval (partialStep M) c).Dom ↔
      ∃ n : ℕ, M.isHalting (M.step^[n] c).state = true := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp h
    obtain ⟨hr, hs⟩ := StateTransition.mem_eval.mp hd
    obtain ⟨n, hn⟩ := reaches_iterate M hr
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hn]
    exact halting_after_partialStep_none M hs
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero =>
      exact Part.dom_iff_mem.mpr ⟨c,
        StateTransition.mem_eval.mpr ⟨.refl, partialStep_none_of_halting M hn⟩⟩
    | succ n ih =>
      cases hs : partialStep M c with
      | none =>
        exact Part.dom_iff_mem.mpr ⟨c, StateTransition.mem_eval.mpr ⟨.refl, hs⟩⟩
      | some d =>
        have hstep := step_of_partialStep_some M hs
        have hd : (StateTransition.eval (partialStep M) d).Dom := by
          apply ih
          simpa only [Function.iterate_succ_apply, hstep] using hn
        have he := StateTransition.reaches_eval
          (Relation.ReflTransGen.single hs)
        rw [he]
        exact hd

theorem halts_iff_eval_dom (I : MachineInput) :
    Halts I ↔ (StateTransition.eval (partialStep I.1)
      (initialConfiguration I.2)).Dom :=
  (eval_dom_iff I.1 (initialConfiguration I.2)).symm

end ForcedComputation.FiniteMachine

end OAI
