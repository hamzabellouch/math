import OAI.Geometry.RCD.Coordinates.CovectorCommutator
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Recovering the displacement from the two-center affine constant -/

noncomputable section
namespace RegularPointCoordinates

/-- Right composition with a near-identity coordinate operator controls
the norm of a constant covector. -/
theorem covector_norm_le_two_comp {n : ℕ} (A : Euclidean n →L[ℝ] Euclidean n)
    (hA : ‖A - 1‖ ≤ 1 / 2) (c : Euclidean n →L[ℝ] ℝ) :
    ‖c‖ ≤ 2 * ‖c.comp A‖ := by
  have he : c = c.comp A - c.comp (A - 1) := by
    ext b
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub]
    ring
  have hn : ‖c‖ ≤ ‖c.comp A‖ + ‖c‖ * ‖A - 1‖ := by
    calc
      _ = ‖c.comp A - c.comp (A - 1)‖ := congrArg norm he
      _ ≤ ‖c.comp A‖ + ‖c.comp (A - 1)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl (c.opNorm_comp_le (A - 1))
  have hh := mul_le_mul_of_nonneg_left hA (norm_nonneg c)
  nlinarith

/-- The controlled commutator constant and matrix difference recover
the actual displacement covector. No inverse matrix is introduced. -/
theorem covector_constant_recovery {n : ℕ}
    (Ax Az : Euclidean n →L[ℝ] Euclidean n) (d c : Euclidean n →L[ℝ] ℝ)
    (hx : ‖Ax - 1‖ ≤ 1 / 2) (hc : c = d.comp Ax)
    {L η M : ℝ} (hB : ‖Az - Ax‖ ≤ L) (hM : ‖c‖ ≤ M)
    (hconst : ‖c.comp (Az - 1)‖ ≤ η) :
    ‖c - d‖ ≤ 2 * (η + M * L) := by
  have hid : c.comp (Ax - 1) = c.comp (Az - 1) - c.comp (Az - Ax) := by
    ext b
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub]
    ring
  have he : (c - d).comp Ax = c.comp (Ax - 1) := by
    ext b
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub]
    have hb := congrArg (fun f : Euclidean n →L[ℝ] ℝ => f b) hc
    change c b = d (Ax b) at hb
    rw [hb]
  have hforce : ‖c.comp (Ax - 1)‖ ≤ η + M * L := by
    rw [hid]
    calc
      _ ≤ ‖c.comp (Az - 1)‖ + ‖c.comp (Az - Ax)‖ := norm_sub_le _ _
      _ ≤ η + ‖c‖ * ‖Az - Ax‖ :=
        add_le_add hconst (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul hM hB (norm_nonneg _) ((norm_nonneg c).trans hM))
  have hlower := covector_norm_le_two_comp Ax hx (c - d)
  rw [he] at hlower
  exact hlower.trans (mul_le_mul_of_nonneg_left hforce (by norm_num))

end RegularPointCoordinates

end

end OAI
