import OAI.Analysis.HyperbolicCones.PositiveCore
import OAI.Analysis.HyperbolicCones.InverseOrder

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem cone_positive_slice (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) :
    ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  have h := cone_positive_slice_of_inverse_order X Z y hX
    (fun t ht => posDef_inverse_sub_shift_inverse_posSemidef X hX t ht)
  simp only [coneResidual, zero_smul, add_zero] at h
  change ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef at h
  exact h

end Paper256

end

end OAI
