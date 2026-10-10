import OAI.Geometry.NodalSets.Elliptic.RealJetErrorEquation
import OAI.Geometry.NodalSets.Elliptic.RealLocalEquationDifferentiation

namespace OAI

namespace Yau.Geometry
open Set Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_local_jet_error_equation (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0)
    (ds : List (Fin 4)) :
    ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C (partialJet W ds)) x+V x*partialJet W ds x =
      Yau.coordDiv (realJetErrorFlux C W ds) x+realJetErrorSource V W ds x := by
  induction ds with
  | nil =>
    intro x hx
    simpa [partialJet,realJetErrorFlux,realJetErrorSource,Yau.coordDiv,Yau.coordPartial] using he x hx
  | cons l ds ih =>
    exact real_local_inhomogeneous_differentiation O hO C V (partialJet W ds) (realJetErrorSource V W ds)
      (realJetErrorFlux C W ds) hC hV (partialJet_smooth W hW ds)
      (realJetErrorSource_smooth V W hV hW ds) (realJetErrorFlux_smooth C W hC hW ds) ih l

end
end Yau.Geometry

end OAI
