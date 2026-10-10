import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenFlow

namespace OAI

                                      
section

/-! True-prefix measurability and service mass for literal hidden trajectories. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

omit [Fintype X] in
theorem refines_le (D : Data X Ω k) (s t : ℕ) (hst : s≤t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : (D.filtration s).r ω v := by
  induction t,hst using Nat.le_induction with
  | base => exact h
  | succ t hst ih => exact ih (D.refines t ω v h)

theorem current_measurable (D : Data X Ω k) (s t : ℕ) (hst : s≤t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : current D s ω=current D s v := by
  exact (flow D).post_measurable s ω v (refines_le D s t hst ω v h)

omit [Fintype X] in
theorem request_past (D : Data X Ω k) (s t : ℕ) (hst : s<t) (ω v : Ω)
    (h : (D.filtration t).r ω v) : D.request s ω=D.request s v := by
  exact D.request_measurable s ω v (refines_le D (s+1) t (by omega) ω v h)

theorem serving_mass (D : Data X Ω k) (t : ℕ) (ω : Ω) : 1≤current D (t+1) ω (D.request t ω) := by
  have hu := (flow D).update t ω (D.request t ω)
  have hl := (flow D).mover_le t ω (D.request t ω)
  change current D (t+1) ω (D.request t ω)=filtered D t ω (D.request t ω)-mover D t ω (D.request t ω)+(if D.request t ω=D.request t ω then 1 else 0) at hu
  rw [ite_eq_left rfl] at hu
  change mover D t ω (D.request t ω)≤filtered D t ω (D.request t ω) at hl
  linarith

end UniformKServer.HiddenFlow

end


end

end OAI
