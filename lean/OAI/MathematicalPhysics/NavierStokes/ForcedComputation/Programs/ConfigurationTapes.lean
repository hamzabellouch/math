import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Recorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TapeCoordinates

namespace OAI

/-! Exact two-stream coordinates of a one-head tape update. -/

namespace ForcedComputation.Recorder

variable {Q A : Type*}

def tapeAt (C : Configuration Q A) : Radix.Tape (Symbol Q A) :=
  (fun n => C.tape (C.head - ((n : ℤ) + 1)), fun n => C.tape (C.head + (n : ℤ)))

theorem tapeAt_right (C : Configuration Q A) (q' : Control Q A) (b : Symbol Q A) :
    tapeAt ⟨q', C.head + 1, Function.update C.tape C.head b⟩ =
      Radix.writeRight b (tapeAt C) := by
  apply Prod.ext
  · funext n
    cases n with
    | zero => simp [tapeAt, Radix.writeRight, Radix.prepend]
    | succ n =>
      dsimp [tapeAt, Radix.writeRight, Radix.prepend]
      rw [Function.update_of_ne (by omega)]
      congr 1
      omega
  · funext n
    dsimp [tapeAt, Radix.writeRight]
    rw [Function.update_of_ne (by omega)]
    congr 1
    omega

theorem tapeAt_stay (C : Configuration Q A) (q' : Control Q A) (b : Symbol Q A) :
    tapeAt ⟨q', C.head, Function.update C.tape C.head b⟩ =
      Radix.writeStay b (tapeAt C) := by
  apply Prod.ext
  · funext n
    dsimp [tapeAt, Radix.writeStay]
    rw [Function.update_of_ne (by omega)]
  · funext n
    cases n with
    | zero => simp [tapeAt, Radix.writeStay, Radix.prepend]
    | succ n =>
      dsimp [tapeAt, Radix.writeStay, Radix.prepend]
      rw [Function.update_of_ne (by omega)]

theorem tapeAt_left (C : Configuration Q A) (q' : Control Q A) (b : Symbol Q A) :
    tapeAt ⟨q', C.head - 1, Function.update C.tape C.head b⟩ =
      Radix.writeLeft b (tapeAt C) := by
  apply Prod.ext
  · funext n
    dsimp [tapeAt, Radix.writeLeft]
    rw [Function.update_of_ne (by omega)]
    congr 1
    omega
  · funext n
    cases n with
    | zero =>
      dsimp [tapeAt, Radix.writeLeft, Radix.prepend]
      rw [Function.update_of_ne (by omega)]
      congr 1
      omega
    | succ n =>
      cases n with
      | zero => simp [tapeAt, Radix.writeLeft, Radix.prepend]
      | succ n =>
        dsimp [tapeAt, Radix.writeLeft, Radix.prepend]
        rw [Function.update_of_ne (by omega)]
        congr 1
        omega

end ForcedComputation.Recorder

end OAI
