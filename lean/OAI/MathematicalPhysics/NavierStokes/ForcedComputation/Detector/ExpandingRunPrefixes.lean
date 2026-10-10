import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderSupport

namespace OAI

/-! A nonhalting input has recorder prefixes of every finite length.
This uses the proved simulation, including its positive macro-step lengths. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

theorem recorderSteps_prefix {Q A : Type*} {M : Recorder.Machine Q A}
    {m n : ℕ} {U V : Configuration Q A} (h : Steps M m U V) (hn : n ≤ m) :
    ∃ W, Steps M n U W := by
  induction h generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst n
    exact ⟨_, Steps.zero _⟩
  | @next m U V W h hs ih =>
    by_cases hnm : n ≤ m
    · exact ih hnm
    · have : n = m + 1 := by omega
      subst n
      exact ⟨_, Steps.next h hs⟩

theorem recorder_nonhalting_control (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (hnot : ¬ Alternating.Halts I)
    {n : ℕ} {U : Configuration (State I.1) (Alphabet I.1)}
    (hU : Steps (finiteMachine I.1 hI.1) n (finiteInitializedRecorder I hI) U) :
    haltingControl (finiteMachine I.1 hI.1) U.control = false := by
  cases hq : U.control with
  | checkpoint q =>
    change I.1.isHalting q.val = false
    cases hh : I.1.isHalting q.val with
    | false => rfl
    | true =>
      exact False.elim (hnot ((finite_recorder_halts_iff I hI).mp ⟨n, U, q, hU, hq, hh⟩))
  | mark r => rfl
  | scanRight r => rfl
  | advance q => rfl
  | scanLeft q => rfl

theorem nonhalting_recorder_prefix (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (hnot : ¬ Alternating.Halts I) (n : ℕ) :
    ∃ U, Steps (finiteMachine I.1 hI.1) n (finiteInitializedRecorder I hI) U ∧
      haltingControl (finiteMachine I.1 hI.1) U.control = false := by
  have hn (i : ℕ) : (finiteMachine I.1 hI.1).halting
      (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) i).state = false := by
    have hs := congrArg WorkConfiguration.state (finite_workAt I hI i)
    change (workAt (finiteMachine I.1 hI.1) (initialState I.1)
      (initialAlphabet I hI) i).state.val = (Alternating.configurationAt I i).state at hs
    change I.1.isHalting _ = false
    rw [hs]
    cases hh : I.1.isHalting (Alternating.configurationAt I i).state with
    | false => rfl
    | true => exact False.elim (hnot ⟨i, hh⟩)
  obtain ⟨m, hnm, hm⟩ := simulate_prefix_length (finiteMachine I.1 hI.1)
    (initialState I.1) (initialAlphabet I hI) 2 (by norm_num) n (fun i _ => hn i)
  obtain ⟨U, hU⟩ := recorderSteps_prefix hm hnm
  exact ⟨U, hU, recorder_nonhalting_control I hI hnot hU⟩

end ForcedComputation.ExpandingDetector

end OAI
