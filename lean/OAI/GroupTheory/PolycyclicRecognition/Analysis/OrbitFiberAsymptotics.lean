import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFromLogProducts

namespace OAI

/-! # Combining the two stabilizer invariances for boundary descent -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

section RelativeLimits

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- Asymptotic equality in a topological group is transitive. -/
theorem relative_limit_trans {f g h : ℕ → Q}
    (hfg : Tendsto (fun n => (f n)⁻¹ * g n) atTop (𝓝 1))
    (hgh : Tendsto (fun n => (g n)⁻¹ * h n) atTop (𝓝 1)) :
    Tendsto (fun n => (f n)⁻¹ * h n) atTop (𝓝 1) := by
  simpa only [mul_assoc, mul_inv_cancel_left, one_mul] using hfg.mul hgh

end RelativeLimits

/-- The two actual stabilizer invariances imply asymptotic equality on
every fiber of the orbit map. No boundary limit is assumed. -/
theorem orbit_fiber_asymptotic_of_stabilizer
    {G S Q I D : Type*} [Group G] [One S]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (act : G →* Equiv.Perm S) (ι : I → G) (κ : D → G)
    (hstab : ∀ g, act g 1 = 1 ↔ ∃ i d, ι i * κ d = g)
    (f : G → ℕ → Q)
    (hI : ∀ g i, Tendsto (fun n => (f g n)⁻¹ * f (g * ι i) n) atTop (𝓝 1))
    (hD : ∀ g d, Tendsto (fun n => (f g n)⁻¹ * f (g * κ d) n) atTop (𝓝 1)) :
    ∀ g g', act g 1 = act g' 1 →
      Tendsto (fun n => (f g n)⁻¹ * f g' n) atTop (𝓝 1) := by
  intro g g' heq
  have hs : act (g⁻¹ * g') 1 = 1 := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← heq]
    exact (act g).symm_apply_apply 1
  obtain ⟨i, d, hid⟩ := (hstab _).mp hs
  have hgg' : (g * ι i) * κ d = g' := by
    rw [mul_assoc, hid, mul_inv_cancel_left]
  have ht := relative_limit_trans (hI g i) (hD (g * ι i) d)
  simpa only [hgg'] using ht

end PolycyclicRecognition

end

end OAI
