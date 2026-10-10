import Mathlib
import OAI.MathematicalPhysics.RecorderFlows.Model
import OAI.Computability.SolenoidalRecorder.Machines

namespace OAI

/-! Fixed-label material trajectories and the machine observation specification. -/

namespace Solenoidal
namespace Fluid
noncomputable def label : Space := ![1 / 8, 3 / 8, 1 / 2]

 
def InStrip (x : Space) : Prop := (1 / 2 : ℝ) < Int.fract (x 0) ∧ Int.fract (x 0) < 1

def Trajectory (U : Field) (X : ℝ → Space) : Prop :=
  X 0 = label ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt X (U (point t (X t))) (Set.Ici 0) t

def ObservationAssertion (M : Machine) (w : List M.Symbol) (U : Field) : Prop :=
  ∃ X : ℝ → Space, Trajectory U X ∧
    (∀ Y : ℝ → Space, Trajectory U Y → ∀ t : ℝ, 0 ≤ t → Y t = X t) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ InStrip (X t)) ↔ M.Halts w)
end Fluid
end Solenoidal

end OAI
