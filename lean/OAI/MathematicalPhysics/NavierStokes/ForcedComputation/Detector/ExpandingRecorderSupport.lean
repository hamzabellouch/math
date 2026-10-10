import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteGraph
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderInputEncoding

namespace OAI

/-! Finite tape windows grow by one cell per recorder instruction. The
actual recorder step therefore appears in the finite stage graph. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

variable {Q A : Type*}

def CenteredBlank (blank : Recorder.Symbol Q A) (d : ℕ)
    (C : Configuration Q A) : Prop :=
  ∀ j : ℤ, j ≤ C.head - (d : ℤ) ∨ C.head + (d : ℤ) ≤ j → C.tape j = blank

theorem CenteredBlank.step {blank : Recorder.Symbol Q A} {d : ℕ}
    {M : Recorder.Machine Q A} {C D : Configuration Q A}
    (hC : CenteredBlank blank d C) (hd : 0 < d) (h : Step M C D) :
    CenteredBlank blank (d + 1) D := by
  obtain ⟨q, s, m, hm, rfl⟩ := h
  have hb := hm.displacement_bounds
  intro j hj
  change j ≤ C.head + m - ((d + 1 : ℕ) : ℤ) ∨
    C.head + m + ((d + 1 : ℕ) : ℤ) ≤ j at hj
  have hne : j ≠ C.head := by omega
  change Function.update C.tape C.head s j = blank
  rw [Function.update_of_ne hne]
  apply hC
  rcases hj with hj | hj
  · left
    omega
  · right
    omega

theorem CenteredBlank.steps {blank : Recorder.Symbol Q A} {d n : ℕ}
    {M : Recorder.Machine Q A} {C D : Configuration Q A}
    (hC : CenteredBlank blank d C) (hd : 0 < d) (h : Steps M n C D) :
    CenteredBlank blank (d + n) D := by
  induction h with
  | zero => simpa only [Nat.add_zero] using hC
  | @next n C D E hrun hstep ih =>
    simpa only [Nat.add_assoc] using (ih hC).step (by omega) hstep

theorem CenteredBlank.coded_tails (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {d : ℕ}
    {C : Configuration (State M) (Alphabet M)} (hC : CenteredBlank blank d C) :
    Lattice.StackTailZero d (codedTape M blank (tapeAt C)).1 ∧
      Lattice.StackTailZero d (codedTape M blank (tapeAt C)).2 := by
  constructor
  · intro i hi
    change symbolCode M blank (C.tape (C.head - ((i : ℤ) + 1))) = 0
    rw [hC _ (Or.inl (by omega)), symbolCode_blank]
  · intro i hi
    change symbolCode M blank (C.tape (C.head + (i : ℤ))) = 0
    rw [hC _ (Or.inr (by omega)), symbolCode_blank]

def configurationAddress (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (C : Configuration (State M) (Alphabet M)) : RecorderAddress M blank d :=
  ⟨C.control, ⟨(configurationStacks M blank d C).1,
      (configurationStacks_bounds M blank d C).1⟩,
    ⟨(configurationStacks M blank d C).2,
      (configurationStacks_bounds M blank d C).2⟩⟩

theorem configurationAddress_step (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {d : ℕ} (hd : 0 < d)
    {C D : Configuration (State M) (Alphabet M)}
    (hC : CenteredBlank blank d C) (h : Step (finiteMachine M hM) C D) :
    stageEdge M hM blank d (configurationAddress M blank d C)
      (configurationAddress M blank (d + 1) D) := by
  obtain ⟨hL, hR⟩ := hC.coded_tails M blank
  exact (boundedIntegerStep_iff M hM blank _ _ _ _ _ _).mpr
    (recorder_step_integer M hM blank hd h hL hR)

theorem initial_centeredBlank (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    CenteredBlank (recorderBlank I.1) (initialWordLength I) (finiteInitializedRecorder I hI) := by
  intro j hj
  have hhead : (finiteInitializedRecorder I hI).head = 0 := rfl
  rw [hhead] at hj
  apply initialTape_blank I hI
  have hlen : 3 ≤ initialWordLength I := le_max_right _ _
  rcases hj with hj | hj
  · left
    omega
  · right
    omega

theorem initialized_steps_centeredBlank (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {n : ℕ}
    {C : Configuration (State I.1) (Alphabet I.1)}
    (h : Steps (finiteMachine I.1 hI.1) n (finiteInitializedRecorder I hI) C) :
    CenteredBlank (recorderBlank I.1) (initialWordLength I + n) C :=
  (initial_centeredBlank I hI).steps
    (lt_of_lt_of_le (by decide : 0 < 3) (le_max_right _ _)) h

end ForcedComputation.ExpandingDetector

end OAI
