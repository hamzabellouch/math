import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalLocalization

namespace OAI

/-! # The exact motion of a Fourier character at a fixed physical point -/

open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingRadius_inv (L t : ℝ) :
    (expandingRadius L t)⁻¹ = L⁻¹ * Real.exp (-t / 2) := by
  unfold expandingRadius
  rw [mul_inv_rev, ← Real.exp_neg]
  rw [mul_comm]
  congr 1
  ring_nf

theorem hasDerivAt_expandingRadius_inv (L t : ℝ) :
    HasDerivAt (fun s => (expandingRadius L s)⁻¹) (-((expandingRadius L t)⁻¹) / 2) t := by
  simp_rw [expandingRadius_inv]
  have h := ((((hasDerivAt_id t).neg).div_const 2).exp).const_mul L⁻¹
  apply h.congr_deriv
  dsimp
  ring

theorem hasDerivAt_expandingPhysicalCharacter (L t : ℝ) (n : frequencyLattice) (y : E) :
    HasDerivAt (fun s => spatialFourierCharacter n ((expandingRadius L s)⁻¹ • y))
      (((-((expandingRadius L t)⁻¹) / 2 * ⟪y, (n : E)⟫ : ℝ) : ℂ) * Complex.I *
        spatialFourierCharacter n ((expandingRadius L t)⁻¹ • y)) t := by
  have h := (((hasDerivAt_expandingRadius_inv L t).mul_const ⟪y, (n : E)⟫).ofReal_comp.mul_const Complex.I).cexp
  unfold spatialFourierCharacter
  simp only [real_inner_smul_left]
  convert h using 1
  ring

end DefocusingNLS

end OAI
