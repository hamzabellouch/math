import OAI.Analysis.HyperbolicCones.ResidualOrder
import OAI.Analysis.HyperbolicCones.PencilOrder

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem posDef_of_shift_bound {n : ℕ} (H F : Sym n) (t : ℝ)
    (hbound : (H : Mat n ℝ) + t • 1 ≤ (F : Mat n ℝ))
    (ht : ‖(H : Mat n ℝ)‖ < t) : (F : Mat n ℝ).PosDef := by
  apply posDef_of_scalar_lower_bound (n := n) (X := (F : Mat n ℝ))
    (c := t - ‖(H : Mat n ℝ)‖) (sub_pos.mpr ht)
  have hnorm : ((H : Mat n ℝ) - (-‖(H : Mat n ℝ)‖) • 1).PosSemidef :=
    sym_neg_norm_le H
  have hdiff : ((F : Mat n ℝ) - ((H : Mat n ℝ) + t • 1)).PosSemidef := hbound
  change ((F : Mat n ℝ) - (t - ‖(H : Mat n ℝ)‖) • 1).PosSemidef
  convert Matrix.PosSemidef.add hdiff hnorm using 1
  module

theorem coneResidual_exists_posDef (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hOrder : ∀ t : ℝ, 0 ≤ t →
      ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    ∃ t : ℝ, 0 < t ∧ (coneResidual X Z y t : Mat 4 ℝ).PosDef := by
  let m := ‖(coneResidual X Z y 0 : Mat 4 ℝ)‖
  have hm : 0 ≤ m := norm_nonneg _
  have ht : 0 < m + 1 := by linarith
  refine ⟨m + 1, ht, ?_⟩
  apply posDef_of_shift_bound (coneResidual X Z y 0) (coneResidual X Z y (m + 1)) (m + 1)
    (coneResidual_lower_bound X Z y (m + 1) (hOrder (m + 1) ht.le))
  exact lt_add_one m

end Paper256

end

end OAI
