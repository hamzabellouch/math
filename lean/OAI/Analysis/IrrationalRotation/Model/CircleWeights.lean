import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

noncomputable section

namespace Invariant233.CircleWeights

def representative (x : UnitAddCircle) : ℝ :=
  AddCircle.equivIco (1 : ℝ) 0 x

def coordinate {ι : Type*} (q : ι → ℤ) (i : ι) (x : UnitAddCircle) : ℝ :=
  representative (q i • x)

def phase {ι : Type*} (θ : ℝ) (q : ι → ℤ) (i : ι) : ℝ :=
  Int.fract ((q i : ℝ) * θ)

def rotate (θ : ℝ) (k : ℤ) (x : UnitAddCircle) : UnitAddCircle :=
  x + k • (θ : UnitAddCircle)

def floorCost {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : ℝ :=
  ∑' i, c i * (Int.floor (coordinate q i x + (k : ℝ) * phase θ q i) : ℝ)

def cocycle {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : ℝ :=
  Real.exp (-floorCost θ q c k x)

def weight {ι : Type*} (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) : UnitAddCircle → ℝ :=
  cocycle θ q c 1

end Invariant233.CircleWeights

end

end OAI
