import OAI.Analysis.HyperbolicCones.ConeRoots
import OAI.Analysis.HyperbolicCones.ResidualOrder
import OAI.Analysis.HyperbolicCones.ResidualBound
import OAI.Analysis.HyperbolicCones.ShiftValue
import OAI.Analysis.HyperbolicCones.PositivePath

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem cone_positive_slice_of_inverse_order (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef)
    (hOrder : ∀ t : ℝ, 0 ≤ t →
      ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    ((X, Z), y) ∈ cone ↔ (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef := by
  rw [cone_iff_no_positive_shift]
  constructor
  · intro h
    apply posSemidef_of_nonsingular_path (coneResidual X Z y)
      (continuousOn_coneResidual X Z y hX)
      (continuousAt_coneResidual X Z y 0 (by simpa using hX))
    · intro t ht
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro hz
      apply h t ht
      rw [polynomial_shift_inverse X Z y t (positive_shift X hX t ht.le), hz, mul_zero]
    · exact coneResidual_exists_posDef X Z y hOrder
  · intro h0 t ht
    have hXt := positive_shift X hX t ht.le
    have hFt := coneResidual_posDef X Z y t ht h0 (hOrder t ht.le)
    rw [polynomial_shift_inverse X Z y t hXt]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hXt.det_pos)) (ne_of_gt hFt.det_pos)

end Paper256

end

end OAI
