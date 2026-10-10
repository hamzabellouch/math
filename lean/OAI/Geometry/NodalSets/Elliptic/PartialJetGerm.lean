import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets

namespace OAI

namespace Yau.Analysis
open Filter
open scoped Topology
noncomputable section

theorem partialJet_eventuallyEq (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (h : f =ᶠ[𝓝 x] g) (ds : List (Fin 4)) :
    partialJet f ds =ᶠ[𝓝 x] partialJet g ds := by
  induction ds with
  | nil => exact h
  | cons i ds ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A ↦ A (Pi.single i 1)) hy

theorem partialJet_germ_eq (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (h : f =ᶠ[𝓝 x] g) (ds : List (Fin 4)) :
    partialJet f ds x = partialJet g ds x :=
  (partialJet_eventuallyEq f g x h ds).eq_of_nhds

end
end Yau.Analysis

end OAI
