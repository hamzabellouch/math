import OAI.MathematicalPhysics.AlternatingFlow.EnergyUniqueness
import OAI.MathematicalPhysics.AlternatingFlow.DerivativeBounds

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Construction

theorem alternating_analytic (ν : ℝ) (hν : 0 < ν) (M : Machine) (w : List ℕ)
    (hM : M.WellFormed) (hw : M.ValidInput w) :
    IsCompact Spatial.box ∧
    Smooth (force ν M w) ∧ Smooth (velocity M w) ∧
    SupportedIn (force ν M w) Spatial.box ∧ SupportedIn (velocity M w) Spatial.box ∧
    Rapid (force ν M w) ∧ Rapid (velocity M w) ∧
    force ν M w = residual ν (velocity M w) ∧
    NavierStokes ν (force ν M w) (velocity M w) (fun _ _ => 0) ∧
    EnergyClass (velocity M w) (fun _ _ => 0) ∧
    (∀ (v : Velocity) (p : Pressure),
      NavierStokes ν (force ν M w) v p → CompetitorEnergyClass v p →
      ∀ t, 0 ≤ t → ∀ x, v t x = velocity M w t x ∧ p t x = 0) ∧
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory (velocity M w) a (X a)) ∧
      (∀ a γ, IsTrajectory (velocity M w) a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
      ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w) := by
  obtain ⟨hf, hU, hfs, hUs, hNS, hX⟩ := smooth_forced_simulation ν M hM w hw
  exact ⟨Spatial.box_compact, hf, hU, hfs, hUs, Bounds.force_rapid ν M w,
    Bounds.velocity_rapid M w, rfl, hNS, velocity_energyClass M w,
    velocity_unique ν hν M w, hX⟩

end Construction
end AlternatingNS

end OAI
