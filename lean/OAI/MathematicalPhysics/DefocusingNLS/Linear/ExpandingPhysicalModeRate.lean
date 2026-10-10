import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModeRateBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyScaling

namespace OAI

/-! # The moving Fourier equation at a fixed Euclidean point -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingModeRate_physical (a b L t : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingModeRate a b L t n =
      (-(a : ℂ) + Complex.I * b) - Complex.I * (((‖n‖ / expandingRadius L t) ^ 2 : ℝ) : ℂ) := by
  have hp := expandingRadius_rpow L t (-2) hL
  have he : -(2 : ℝ) * t / 2 = -t := by ring
  rw [he] at hp
  have hi : (expandingRadius L t ^ 2)⁻¹ = L ^ (-2 : ℝ) * Real.exp (-t) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (show 0 ≤ expandingRadius L t by unfold expandingRadius; positivity), Real.rpow_two] at hp
    simpa only [mul_comm] using hp
  have hq : (‖n‖ / expandingRadius L t) ^ 2 = L ^ (-2 : ℝ) * Real.exp (-t) * ‖n‖ ^ 2 := by
    rw [div_pow, div_eq_mul_inv, hi]
    ring
  rw [hq]
  rfl

theorem hasDerivAt_expandingPhysicalMode (a b k L t : ℝ) (hL : 1 ≤ L)
    (n : frequencyLattice) (y : E) (u : ℝ → FourierL2) (g : ℂ)
    (hu : HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n)
      (expandingModeRate a b L t n * expandingFourierCoefficient a k (expandingRadius L t) (u t) n + g) t) :
    HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n *
      spatialFourierCharacter n ((expandingRadius L s)⁻¹ • y))
      ((physicalModeRate a b (expandingRadius L t) n y *
        expandingFourierCoefficient a k (expandingRadius L t) (u t) n + g) *
        spatialFourierCharacter n ((expandingRadius L t)⁻¹ • y)) t := by
  apply (hasDerivAt_expandingPhysicalTerm a k L t n y u _ hu).congr_deriv
  rw [expandingModeRate_physical a b L t hL]
  unfold physicalModeRate
  ring

end DefocusingNLS

end OAI
