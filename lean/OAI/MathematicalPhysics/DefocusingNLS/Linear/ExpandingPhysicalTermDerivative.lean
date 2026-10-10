import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalCharacter

namespace OAI

/-! # Time derivative of one actual Fourier term at a fixed physical point -/

open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_expandingPhysicalTerm (a k L t : ℝ) (n : frequencyLattice) (y : E)
    (u : ℝ → FourierL2) (d : ℂ)
    (hu : HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n) d t) :
    HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n *
      spatialFourierCharacter n ((expandingRadius L s)⁻¹ • y))
      ((d + ((-((expandingRadius L t)⁻¹) / 2 * ⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I *
        expandingFourierCoefficient a k (expandingRadius L t) (u t) n) *
          spatialFourierCharacter n ((expandingRadius L t)⁻¹ • y)) t := by
  convert hu.mul (hasDerivAt_expandingPhysicalCharacter L t n y) using 1
  ring

end DefocusingNLS

end OAI
