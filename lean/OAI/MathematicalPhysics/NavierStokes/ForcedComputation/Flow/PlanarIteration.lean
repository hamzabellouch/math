import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderRun

namespace OAI

/-! Integer-phase iteration of a periodic planar processor. -/

noncomputable section
namespace ForcedComputation
open ShearFlows

theorem IsPlanarTransition.phase_nat {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hV : ∀ y, Function.Periodic (fun t => V t y) 1)
    (a : ℝ) (n : ℕ) (t : ℝ) (x : Plane) : Ψ (a + n) t x = Ψ a t x := by
  apply hΨ.unique a x (fun s => Ψ (a + n) s x) (hΨ.initial (a + n) x)
  intro s
  have he : V ((a + n) + s) (Ψ (a + n) s x) = V (a + s) (Ψ (a + n) s x) := by
    have h := (hV (Ψ (a + n) s x)).nat_mul n (a + s)
    convert h using 1
    congr 1
    ring
  exact (hΨ.ode (a + n) s x).congr_deriv he

theorem IsPlanarTransition.nat_shift {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hV : ∀ y, Function.Periodic (fun t => V t y) 1)
    (n : ℕ) (s : ℝ) (x : Plane) : Ψ 0 ((n : ℝ) + s) x = Ψ 0 s (Ψ 0 n x) := by
  rw [hΨ.compose]
  simpa only [zero_add] using hΨ.phase_nat hV 0 n s (Ψ 0 n x)

theorem planar_recorder_steps {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    {M : Recorder.Machine Q A} {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition V Ψ) (hV : ∀ y, Function.Periodic (fun t => V t y) 1)
    (code : Recorder.Configuration Q A → Plane)
    (hone : ∀ {C D}, Recorder.Step M C D → Ψ 0 1 (code C) = code D)
    {C D : Recorder.Configuration Q A} {n : ℕ} (h : Recorder.Steps M n C D) :
    Ψ 0 n (code C) = code D := by
  induction h with
  | zero C => simpa only [Nat.cast_zero] using hΨ.initial 0 (code C)
  | @next n C D E h hs ih =>
      rw [Nat.cast_add, Nat.cast_one, hΨ.nat_shift hV, ih]
      exact hone hs

end ForcedComputation

end

end OAI
