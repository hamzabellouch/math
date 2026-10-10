import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderTransitions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteStackUpdates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderCoordinates

namespace OAI

/-! The integer address of the actual reversible recorder configuration.
The finite prefix is enlarged by one at every local instruction, and its
integer update agrees with the full guarded table. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

def codedTape (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    (T : Radix.Tape (Recorder.Symbol (State M) (Alphabet M))) : Radix.Tape ℕ :=
  (fun n => symbolCode M blank (T.1 n), fun n => symbolCode M blank (T.2 n))

theorem codedTape_left (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M))
    (T : Radix.Tape (Recorder.Symbol (State M) (Alphabet M))) :
    codedTape M blank (Radix.writeLeft s T) =
      Radix.writeLeft (symbolCode M blank s) (codedTape M blank T) := by
  apply Prod.ext
  · rfl
  · funext n
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

theorem codedTape_stay (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M))
    (T : Radix.Tape (Recorder.Symbol (State M) (Alphabet M))) :
    codedTape M blank (Radix.writeStay s T) =
      Radix.writeStay (symbolCode M blank s) (codedTape M blank T) := by
  apply Prod.ext
  · rfl
  · funext n
    cases n <;> rfl

theorem codedTape_right (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M))
    (T : Radix.Tape (Recorder.Symbol (State M) (Alphabet M))) :
    codedTape M blank (Radix.writeRight s T) =
      Radix.writeRight (symbolCode M blank s) (codedTape M blank T) := by
  apply Prod.ext
  · funext n
    cases n <;> rfl
  · rfl

def configurationStacks (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (C : Configuration (State M) (Alphabet M)) : ℕ × ℕ :=
  Lattice.integerTapeCode (alphabetBase M blank) d (codedTape M blank (tapeAt C))

theorem configurationStacks_bounds (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (C : Configuration (State M) (Alphabet M)) :
    (configurationStacks M blank d C).1 < alphabetBase M blank ^ d ∧
      (configurationStacks M blank d C).2 < alphabetBase M blank ^ d := by
  have hb : 0 < alphabetBase M blank :=
    lt_of_lt_of_le (by decide) (alphabetBase_two_le M blank)
  constructor <;> apply Lattice.stackValue_lt hb d <;>
    intro i _ <;> exact symbolCode_lt_base M blank _

theorem configurationStacks_read (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {d : ℕ} (hd : 0 < d)
    (C : Configuration (State M) (Alphabet M)) :
    (configurationStacks M blank d C).2 % alphabetBase M blank =
      symbolCode M blank (C.tape C.head) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  simpa only [configurationStacks, Lattice.integerTapeCode, codedTape, tapeAt,
    Nat.cast_zero, add_zero] using
      (Lattice.stackValue_head (b := alphabetBase M blank) (d := k)
        (a := (codedTape M blank (tapeAt C)).2) (symbolCode_lt_base M blank _))

theorem configurationStacks_update (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {d : ℕ} (hd : 0 < d)
    (C : Configuration (State M) (Alphabet M))
    (q' : Control (State M) (Alphabet M)) (s : Recorder.Symbol (State M) (Alphabet M))
    {m : ℤ} (hm : -1 ≤ m ∧ m ≤ 1)
    (hL : Lattice.StackTailZero d (codedTape M blank (tapeAt C)).1)
    (hR : Lattice.StackTailZero d (codedTape M blank (tapeAt C)).2) :
    configurationStacks M blank (d + 1)
        ⟨q', C.head + m, Function.update C.tape C.head s⟩ =
      (Lattice.nextLeft (alphabetBase M blank) (configurationStacks M blank d C).1
        (symbolCode M blank s) (moveCode m),
       Lattice.nextRight (alphabetBase M blank) (configurationStacks M blank d C).1
        (configurationStacks M blank d C).2 (symbolCode M blank s) (moveCode m)) := by
  have hb : 0 < alphabetBase M blank :=
    lt_of_lt_of_le (by decide) (alphabetBase_two_le M blank)
  have hu := Lattice.integerTapeCode_move hb hd (symbolCode M blank s)
    (codedTape M blank (tapeAt C)) (symbolCode_lt_base M blank _)
    (symbolCode_lt_base M blank _) hL hR (moveCode m)
  have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa [configurationStacks, show C.head + (-1) = C.head - 1 by omega,
      tapeAt_left, codedTape_left, moveCode] using hu
  · simpa [configurationStacks, tapeAt_stay, codedTape_stay, moveCode] using hu
  · simpa [configurationStacks, tapeAt_right, codedTape_right, moveCode] using hu

theorem recorder_step_integer (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {d : ℕ} (hd : 0 < d)
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    (hL : Lattice.StackTailZero d (codedTape M blank (tapeAt C)).1)
    (hR : Lattice.StackTailZero d (codedTape M blank (tapeAt C)).2) :
    IntegerStep M hM blank C.control (configurationStacks M blank d C).1
      (configurationStacks M blank d C).2 D.control
      (configurationStacks M blank (d + 1) D).1
      (configurationStacks M blank (d + 1) D).2 := by
  obtain ⟨q', s, m, hs, rfl⟩ := h
  have hu := configurationStacks_update M blank hd C q' s hs.displacement_bounds hL hR
  refine ⟨C.tape C.head, s, m, hs, (configurationStacks_read M blank hd C).symm, ?_, ?_⟩
  · exact (congrArg Prod.fst hu).symm
  · exact (congrArg Prod.snd hu).symm

end ForcedComputation.ExpandingDetector

end OAI
