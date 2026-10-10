import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Lifting auxiliary radial directions

The integer-cap argument in `prep:integer-caps` uses the map
`w ↦ P w / ‖P w‖` only where projected separation bounds `‖P w‖`
away from zero. These elementary facts keep the auxiliary direction
map separate from the original Euclidean distance map.
-/

namespace Falconer
open NormedSpace

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalization is Lipschitz on vectors whose norms are bounded below. -/
theorem normalize_dist_le {v w : E} {c : ℝ} (hc : 0 < c)
    (hv : c ≤ ‖v‖) (hw : c ≤ ‖w‖) :
    dist (normalize v) (normalize w) ≤ (2 / c) * dist v w := by
  have hvpos : 0 < ‖v‖ := hc.trans_le hv
  have hwne : w ≠ 0 := norm_pos_iff.mp (hc.trans_le hw)
  have hscale : ‖v‖ * dist (normalize v) (normalize w) ≤ 2 * dist v w := by
    calc
      ‖v‖ * dist (normalize v) (normalize w) =
          dist (‖v‖ • normalize v) (‖v‖ • normalize w) := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ dist (‖v‖ • normalize v) (‖w‖ • normalize w) +
          dist (‖w‖ • normalize w) (‖v‖ • normalize w) := dist_triangle _ _ _
      _ = dist v w + |‖w‖ - ‖v‖| := by
        have he : dist (‖w‖ • normalize w) (‖v‖ • normalize w) = |‖w‖ - ‖v‖| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, norm_normalize hwne,
            Real.norm_eq_abs, mul_one]
        rw [he, norm_smul_normalize, norm_smul_normalize]
      _ ≤ dist v w + dist w v :=
        add_le_add le_rfl (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le w v)
      _ = 2 * dist v w := by rw [dist_comm w v]; ring
  calc
    dist (normalize v) (normalize w) ≤ (2 * dist v w) / ‖v‖ := by
      apply (le_div_iff₀ hvpos).mpr
      simpa only [mul_comm] using hscale
    _ ≤ (2 * dist v w) / c :=
      div_le_div_of_nonneg_left (by positivity) hc hv
    _ = (2 / c) * dist v w := by ring

/-- A linear map commutes with radial directions after re-normalization. -/
theorem normalize_map_radial (P : E →L[ℝ] F) {x y : E} (hxy : y ≠ x) :
    normalize (P (normalize (y - x))) = normalize (P y - P x) := by
  change normalize (P (‖y - x‖⁻¹ • (y - x))) = _
  rw [map_smul, normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))), map_sub]

/-- The auxiliary normalized projection has a uniform Lipschitz bound on the
part of the sphere on which projected separation is available. -/
theorem normalized_projection_dist_le (P : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hP : ‖P‖ ≤ 1) {v w : E} (hv : c ≤ ‖P v‖) (hw : c ≤ ‖P w‖) :
    dist (normalize (P v)) (normalize (P w)) ≤ (2 / c) * dist v w := by
  apply (normalize_dist_le hc hv hw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    dist (P v) (P w) ≤ ‖P‖ * dist v w := by
      simpa only [dist_eq_norm, map_sub] using P.le_opNorm (v - w)
    _ ≤ 1 * dist v w := mul_le_mul_of_nonneg_right hP dist_nonneg
    _ = dist v w := one_mul _

end
end Falconer

end OAI
