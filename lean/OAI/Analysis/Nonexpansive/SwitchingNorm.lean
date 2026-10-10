import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Norm estimates for the actual switching differences

These elementary estimates are applied to root outputs from one chronological
switching experiment.  The construction of those outputs and their before- and
after-block bounds is separate from the linear-functional calculations here.
-/

noncomputable section

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A functional of operator norm at most one is bounded by the given norm. -/
theorem abs_functional_apply_le_norm (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (z : X) :
    |f z| ≤ ‖z‖ := by
  calc
    |f z| = ‖f z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- Transfer a detector from two comparison points to the actual before/after
outputs.  This uses linearity only of the detector, not of the node maps. -/
theorem detector_transfer_le (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (U V y q : X) :
    f (y - q) - ‖U - y‖ - ‖V - q‖ ≤ f (U - V) := by
  have hU := abs_functional_apply_le_norm f hf (U - y)
  have hV := abs_functional_apply_le_norm f hf (V - q)
  have hU' := (abs_le.mp hU).1
  have hV' := (abs_le.mp hV).2
  have heq : f (U - V) = f (y - q) + f (U - y) - f (V - q) := by
    simp only [map_sub]
    ring
  linarith

/-- The exact `W - 5e` detector estimate from the three already proved actual
terminal, before-block, and after-block inequalities. -/
theorem block_detection_of_norm_bounds (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (U V y q : X) (W e : ℝ)
    (hterminal : 1 - 2 * e ≤ f (y - q))
    (hbefore : ‖U - y‖ ≤ 1 - W + 2 * e)
    (hafter : ‖V - q‖ ≤ e) :
    W - 5 * e ≤ f (U - V) := by
  have htransfer := detector_transfer_le f hf U V y q
  linarith

/-- Normalization of a single actual root increment preserves its subspace,
puts it in the unit ball, and reconstructs it upon multiplication by its weight.
The weight may be arbitrarily small; only strict positivity is required. -/
theorem normalized_switch_difference (Y : Submodule ℝ X)
    (U V : X) (W : ℝ) (hW : 0 < W)
    (hmem : U - V ∈ Y) (hnorm : ‖U - V‖ ≤ W) :
    W⁻¹ • (U - V) ∈ Y ∧
      ‖W⁻¹ • (U - V)‖ ≤ 1 ∧
      W • (W⁻¹ • (U - V)) = U - V := by
  refine ⟨Y.smul_mem W⁻¹ hmem, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW)]
    calc
      W⁻¹ * ‖U - V‖ ≤ W⁻¹ * W :=
        mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hW))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hW)
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hW), one_smul]

/-- Unit-ball vectors have detector score at most one. -/
theorem functional_apply_le_one (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (z : X) (hz : ‖z‖ ≤ 1) : f z ≤ 1 :=
  (le_abs_self _).trans ((abs_functional_apply_le_norm f hf z).trans hz)

end ReflexiveFixedPoints

end

end OAI
