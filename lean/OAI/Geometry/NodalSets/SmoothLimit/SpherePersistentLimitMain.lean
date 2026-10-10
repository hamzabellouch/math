import OAI.Geometry.NodalSets.Elliptic.SeedFrequencyDivergence
import OAI.Geometry.NodalSets.SmoothLimit.SphereIterationInterface

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

theorem sphere_persistent_limit_implies_main {r delta : ℝ}
    (s : (k : ℕ) → SphereNodalStage r delta k) (hN : ∀ k, k+1 ≤ (s k).frequency)
    (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (hnear : ∀ k, sphereCoefficientDistance (s k).charts 8
      (s k).energy.tensor (s k).energy.density b.tensor b.density < (s k).radius) :
    MainTarget := by
  have H (k : ℕ) := (s k).persistence b hb (hnear k)
  choose mu v hwindow hmu hv hv0 he hlift hln hle hratio using H
  exact mainTarget_of_seed_windows
    (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
    (fun k ↦ (s k).frequency) mu (fun k ↦ circleLift (v k)) hN hmu
    (fun k ↦ (hwindow k).1) hln hlift hle hratio

end
end Yau.Target

end OAI
