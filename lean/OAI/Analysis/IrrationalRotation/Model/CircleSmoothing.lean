import OAI.Analysis.IrrationalRotation.Model.SawtoothSmoothing
import Mathlib.Topology.Instances.AddCircle.Defs

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

def circleSmoothSawtooth (δ : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  AddCircle.liftIco 1 0 (smoothSawtooth δ)

def circleSmoothedDrop (C a δ : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  C * (a + circleSmoothSawtooth δ x - circleSmoothSawtooth δ (x + (a : AddCircle (1 : ℝ))))

def circleSmoothingTransfer (C δ : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  C * (circleSmoothSawtooth δ x - (AddCircle.equivIco 1 0 x : ℝ))

end InvariantProjection.Continuity

end

end OAI
