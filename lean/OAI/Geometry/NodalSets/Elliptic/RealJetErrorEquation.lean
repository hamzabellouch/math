import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Elliptic.RealCutoffIntegralsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realJetErrorFlux (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → Yau.Jets.Coord
  | [] => fun _ _ ↦ 0
  | l::ds => fun x i ↦ Yau.coordPartial (fun y ↦ realJetErrorFlux C W ds y i) x l -
      realDerivativeErrorFlux C (partialJet W ds) l x i

def realJetErrorSource (V W : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → ℝ
  | [] => fun _ ↦ 0
  | l::ds => fun x ↦ Yau.coordPartial (realJetErrorSource V W ds) x l -
      Yau.coordPartial V x l*partialJet W ds x

lemma realJetErrorFlux_smooth (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realJetErrorFlux C W ds x i) := by
  induction ds with
  | nil => exact contDiff_const
  | cons l ds ih =>
    exact (Yau.real_coordPartial_smooth _ ih l).sub
      (realDerivativeErrorFlux_smooth C (partialJet W ds) l hC (partialJet_smooth W hW ds) i)

lemma realJetErrorSource_smooth (V W : Yau.Jets.Coord → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    ContDiff ℝ ∞ (realJetErrorSource V W ds) := by
  induction ds with
  | nil => exact contDiff_const
  | cons l ds ih =>
    exact (Yau.real_coordPartial_smooth _ ih l).sub
      ((Yau.real_coordPartial_smooth V hV l).mul (partialJet_smooth W hW ds))

theorem real_jet_error_equation (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0)
    (ds : List (Fin 4)) :
    ∀ x, Yau.coordDiv (realMatrixFlux C (partialJet W ds)) x+V x*partialJet W ds x =
      Yau.coordDiv (realJetErrorFlux C W ds) x+realJetErrorSource V W ds x := by
  induction ds with
  | nil =>
    intro x
    simpa [partialJet,realJetErrorFlux,realJetErrorSource,Yau.coordDiv,Yau.coordPartial] using he x
  | cons l ds ih =>
    exact real_inhomogeneous_differentiation C V (partialJet W ds) (realJetErrorSource V W ds)
      (realJetErrorFlux C W ds) hC hV (partialJet_smooth W hW ds)
      (realJetErrorSource_smooth V W hV hW ds) (realJetErrorFlux_smooth C W hC hW ds) ih l

end
end Yau.Geometry

end OAI
