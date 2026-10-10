import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.CircleWeights

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

abbrev Coord (p : CircleParameterData) :=
  Σ j : ℕ, {i : ℕ // i ∈ p.block (j + 1)}

def coordFrequency (p : CircleParameterData) (i : p.Coord) : ℤ := p.q i.2

def coordCost (p : CircleParameterData) (i : p.Coord) : ℝ := p.C (i.1 + 1)

def floorCocycle (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) : ℝ :=
  CircleWeights.cocycle θ p.coordFrequency p.coordCost k x

def measurableWeight (p : CircleParameterData) (θ : ℝ) : Circle → ℝ :=
  CircleWeights.weight θ p.coordFrequency p.coordCost

end Invariant233.CircleParameterData

end

end OAI
