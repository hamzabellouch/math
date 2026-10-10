import OAI.Analysis.IrrationalRotation.Model.CharacterLaw
import OAI.Analysis.IrrationalRotation.Model.ScalarSampling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.CharacterSampling

def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def kernel (endpoint : Bool) (m : ℕ) (z v : ℝ) : ℝ :=
  if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
  else ScalarSampling.manuscriptKernel m z v

def average (m : ℕ) (powers : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) (spatial : UnitAddTorus (Fin m)) : ℝ :=
  (powers.card : ℝ)⁻¹ * ∑ n ∈ powers, ∏ i : Fin m,
    kernel endpoint m (representative (spatial i)) ((n : ℝ) * phase i)

def squaredError (m : ℕ) (powers : Finset ℕ) (endpoint : Bool)
    (p : (Fin m → ℝ) × UnitAddTorus (Fin m)) : ℝ :=
  (average m powers endpoint p.1 p.2 - 1) ^ 2

end Invariant233.CharacterSampling

end

end OAI
