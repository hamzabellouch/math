import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.CharacterLaw

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.SamplingTests

def kernel (endpoint : Bool) (m : ℕ) (z v : ℝ) : ℝ :=
  CircleParameterData.orientedKernel endpoint m z (Int.fract v)

def circleKernel (endpoint : Bool) (m : ℕ) (v : ℝ) (x : Circle) : ℝ :=
  kernel endpoint m (CircleParameterData.rep x) v

def average (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) : ℝ :=
  ((s.card : ℝ)⁻¹) * ∑ n ∈ s, ∏ i : Fin d,
    circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)

def errorSq (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) : ℝ :=
  (average endpoint m d s z - 1) ^ 2

end Invariant233.SamplingTests

end

end OAI
