import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderFlow
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionExpressions

namespace OAI

/-! Iterating a spatial suspension: a completed processor period advances
the vertical lift by one while implementing the next recorder step. -/

noncomputable section
namespace ForcedComputation
open ShearFlows

def verticalInteger (n : ℤ) : Fin 3 → ℤ := ![0, 0, n]

theorem atHeight_add_verticalInteger (p : Plane) (z : ℝ) (n : ℤ) :
    atHeight p (z + n) = atHeight p z + latticeVector 1 (verticalInteger n) := by
  funext j
  fin_cases j <;> simp [atHeight, latticeVector, verticalInteger]

theorem suspension_one_at_integer {W : Space → Space} {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => W y.2) Φ) {p q : Plane}
    (hstep : Φ 1 (atHeight p 0) = atHeight q 1) (n : ℕ) :
    Φ 1 (atHeight p (n : ℝ)) = atHeight q ((n : ℝ) + 1) := by
  have hp : atHeight p (n : ℝ) =
      atHeight p 0 + latticeVector 1 (verticalInteger (n : ℤ)) := by
    simpa only [Int.cast_natCast, zero_add] using atHeight_add_verticalInteger p 0 (n : ℤ)
  have hq : atHeight q ((n : ℝ) + 1) =
      atHeight q 1 + latticeVector 1 (verticalInteger (n : ℤ)) := by
    simpa only [Int.cast_natCast, add_comm] using atHeight_add_verticalInteger q 1 (n : ℤ)
  rw [hp, hΦ.equivariant, hstep, hq]

theorem suspension_recorder_steps {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    {M : Recorder.Machine Q A} {W : Space → Space} {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => W y.2) Φ)
    (code : Recorder.Configuration Q A → Plane)
    (hone : ∀ {C D}, Recorder.Step M C D →
      Φ 1 (atHeight (code C) 0) = atHeight (code D) 1)
    {C D : Recorder.Configuration Q A} {n : ℕ} (h : Recorder.Steps M n C D) :
    Φ n (atHeight (code C) 0) = atHeight (code D) n := by
  induction h with
  | zero C => simpa only [Nat.cast_zero] using hΦ.initial (atHeight (code C) 0)
  | @next n C D E h hs ih =>
    rw [Nat.cast_add, Nat.cast_one, add_comm,
      hΦ.nat_shift (show TimePeriodic (fun y => W y.2) from fun _ _ => rfl) n 1, ih]
    simpa only [add_comm] using suspension_one_at_integer hΦ (hone hs) n

end ForcedComputation

end

end OAI
