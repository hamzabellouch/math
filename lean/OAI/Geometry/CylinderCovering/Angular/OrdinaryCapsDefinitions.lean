import OAI.Geometry.CylinderCovering.Convexity.GeneralCapAreaDefinitions
import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.AngularOrdinaryCaps

open GeneralCapArea

def secantAlpha (l r : ℝ) : ℝ := (1 + l * r) / 4
def secantBeta (l r : ℝ) : ℝ := (l + r) / 4

def taggedRadius (ε η t : ℝ) : ℝ := 1 / 2 + ε ^ 2 * (profile t + η)
def midpointRadius (ε η l r : ℝ) : ℝ := taggedRadius ε η ((l + r) / 2)
def maximumRadius (ε η l r : ℝ) : ℝ :=
  1 / 2 + ε ^ 2 * (max (profile l) (profile r) + η)
def radialRadius (ε η q : ℝ) : ℝ := taggedRadius ε η q

inductive CapChoice where
  | midpoint
  | maximum
  | radial
  deriving DecidableEq

def chosenRadius (choice : CapChoice) (ε η l r q : ℝ) : ℝ :=
  match choice with
  | .midpoint => midpointRadius ε η l r
  | .maximum => maximumRadius ε η l r
  | .radial => radialRadius ε η q

def ordinaryData (choice : CapChoice) (N : ℕ) (a : ℕ → ℝ) (ε η : ℝ) :
    AngularGeneral.Data where
  count := N
  node := a
  alpha := fun j => secantAlpha (a j) (a (j + 1))
  beta := fun j => secantBeta (a j) (a (j + 1))
  radius := fun j q => chosenRadius choice ε η (a j) (a (j + 1)) q

def OrdinaryCoverStatement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 / 480 → ∀ M : ℝ, 0 ≤ M →
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ N : ℕ, 0 < N →
        ∀ a : ℕ → ℝ, a 0 = -1 → a N = 1 →
          (∀ j < N, a j < a (j + 1)) →
          (∀ j < N, a (j + 1) - a j ≤ M * ε ^ 2) →
          ∀ choice : CapChoice,
            AngularGeneral.Conclusion ε η A (ordinaryData choice N a ε η) ∧
            (choice ≠ .radial → ∀ j < N,
              AngularGeneral.IsNondegenerateTriangle
                (AngularGeneral.lowerBase ε (ordinaryData choice N a ε η) j) ∧
              AngularGeneral.IsNondegenerateTriangle
                (AngularGeneral.upperBase ε (ordinaryData choice N a ε η) j))

end CylinderCovering.AngularOrdinaryCaps

end

end OAI
