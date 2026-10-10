import OAI.Analysis.HyperbolicCones.ConeMatrix

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem coneResidual_identity (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) :
    (coneResidual X Z y t : Mat 4 ℝ) =
      (coneResidual X Z y 0 : Mat 4 ℝ) + t • 1 +
        phi y ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹) := by
  have hp := (phiLinear y).map_sub (X : Mat 4 ℝ)⁻¹
    ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹
  change phi y (_ - _) = phi y _ - phi y _ at hp
  rw [hp]
  change (Z : Mat 4 ℝ) + t • 1 - phi y ((X : Mat 4 ℝ) + t • 1)⁻¹ =
    ((Z : Mat 4 ℝ) + (0 : ℝ) • 1 - phi y ((X : Mat 4 ℝ) + (0 : ℝ) • 1)⁻¹) +
      t • 1 + (phi y (X : Mat 4 ℝ)⁻¹ - phi y ((X : Mat 4 ℝ) + t • 1)⁻¹)
  simp only [zero_smul, add_zero]
  module

theorem coneResidual_lower_bound (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (hInv : ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    (coneResidual X Z y 0 : Mat 4 ℝ) + t • 1 ≤ (coneResidual X Z y t : Mat 4 ℝ) := by
  conv_rhs => rw [coneResidual_identity]
  exact le_add_of_nonneg_right (phi_posSemidef y _ hInv).nonneg

theorem coneResidual_posDef (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : 0 < t) (h0 : (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef)
    (hInv : ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    (coneResidual X Z y t : Mat 4 ℝ).PosDef := by
  rw [coneResidual_identity]
  exact (Matrix.PosDef.posSemidef_add h0 (Matrix.PosDef.one.smul ht)).add_posSemidef
    (phi_posSemidef y _ hInv)

end Paper256

end

end OAI
