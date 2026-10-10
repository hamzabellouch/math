import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FreshMachine
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteRecorder

namespace OAI

/-! The incoming row of the fresh checkpoint is unreachable. Removing this
row leaves every actual recorder transition intact and frees a loader target. -/

namespace ForcedComputation
open Alternating

theorem freshMachine_normalized_nonzero (M : Alternating.Machine) (q a : ℕ) :
    ((freshMachine M).normalizedInstruction q a).1 ≠ 0 := by
  unfold Machine.normalizedInstruction
  split
  · rename_i hhalt
    intro hq
    change q = 0 at hq
    subst q
    simp at hhalt
  · cases hi : (freshMachine M).instruction q a with
    | none => simp [Machine.stateCount, freshMachine]
    | some i => exact freshMachine_no_incoming hi

namespace Recorder
open Control

def FreshControl {Q A : Type*} (q₀ : Q) (c : Control Q A) : Prop :=
  c ≠ advance q₀ ∧ c ≠ scanLeft q₀

theorem LocalStep.freshControl {Q A : Type*} {M : Machine Q A} {q₀ : Q}
    (hn : ∀ q a, M.next q a ≠ q₀)
    {q q' : Control Q A} {a a' : Symbol Q A} {d : ℤ}
    (h : LocalStep M q a q' a' d) (hq : FreshControl q₀ q) : FreshControl q₀ q' := by
  cases h <;> simp_all [FreshControl]

theorem LocalStep.not_fresh_checkpoint {Q A : Type*} {M : Machine Q A} {q₀ : Q}
    {q q' : Control Q A} {a a' : Symbol Q A} {d : ℤ}
    (h : LocalStep M q a q' a' d) (hq : FreshControl q₀ q) : q' ≠ checkpoint q₀ := by
  cases h <;> simp_all [FreshControl]

theorem Step.freshControl {Q A : Type*} {M : Machine Q A} {q₀ : Q}
    (hn : ∀ q a, M.next q a ≠ q₀)
    {C D : Configuration Q A} (h : Step M C D) (hC : FreshControl q₀ C.control) :
    FreshControl q₀ D.control := by
  obtain ⟨q, a, d, hl, rfl⟩ := h
  exact hl.freshControl hn hC

theorem Steps.freshControl {Q A : Type*} {M : Machine Q A} {q₀ : Q}
    (hn : ∀ q a, M.next q a ≠ q₀)
    {C D : Configuration Q A} {n : ℕ} (h : Steps M n C D)
    (hC : FreshControl q₀ C.control) : FreshControl q₀ D.control := by
  induction h with
  | zero => exact hC
  | next h hs ih => exact hs.freshControl hn (ih hC)

theorem fresh_finiteMachine_next (M : Alternating.Machine)
    (hM : (freshMachine M).WellFormed) (q : State (freshMachine M))
    (a : Alphabet (freshMachine M)) :
    (finiteMachine (freshMachine M) hM).next q a ≠ initialState (freshMachine M) := by
  intro he
  have hv := congrArg Fin.val he
  exact freshMachine_normalized_nonzero M q.val a.val hv

theorem fresh_recorder_never_returns (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {n : ℕ}
    {C D : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (hc : Steps (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) n
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)) C)
    (hd : Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D) :
    D.control ≠ checkpoint (initialState (freshMachine I.1)) := by
  have hzero : FreshControl (initialState (freshMachine I.1))
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)).control := by
    constructor <;> intro he <;> cases he
  have hC := hc.freshControl (fresh_finiteMachine_next I.1 (freshInput_valid hI).1) hzero
  obtain ⟨q, a, d, hl, rfl⟩ := hd
  exact hl.not_fresh_checkpoint hC

end Recorder
end ForcedComputation

end OAI
