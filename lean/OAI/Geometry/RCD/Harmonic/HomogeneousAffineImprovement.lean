import OAI.Geometry.RCD.Harmonic.ContinuousAffineImprovement

namespace OAI

/-! # Removing the unit-norm restriction in harmonic affine improvement -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)

theorem harmonicTargetNorm_smul (p : X) (r c : ℝ)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicTargetNorm hX p r (c • w) = |c| * harmonicTargetNorm hX p r w := by
  unfold harmonicTargetNorm
  rw [map_smul]
  unfold normalizeLocalL2
  rw [smul_comm, norm_smul, Real.norm_eq_abs]

theorem harmonicAffineResidualNorm_smul
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (p : X) (r c : ℝ)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicAffineResidualNorm hX u p r (c • w) =
      |c| * harmonicAffineResidualNorm hX u p r w := by
  unfold harmonicAffineResidualNorm
  rw [map_smul, map_smul]
  unfold normalizeLocalL2
  rw [smul_comm, norm_smul, Real.norm_eq_abs]

/-- Full support makes the averaging factor nonzero on every positive ball. -/
theorem restrictLp_eq_zero_of_harmonicTargetNorm_eq_zero (p : X) {r : ℝ} (hr : 0 < r)
    (w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : harmonicTargetNorm hX p r w = 0) :
    SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) w = 0 := by
  have hvol : 0 < (hausdorff n X).real (ball p r) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p r hr))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hone : ‖restrictedOne (hausdorff n X) (ball p r)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))‖ ≠ 0 := by
    rw [restrictedOne_norm]
    exact ne_of_gt (Real.sqrt_pos.2 hvol)
  have hz := norm_eq_zero.mp hw
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hone)

/-- A zero target on the outer ball has zero affine residual on any inner ball. -/
theorem harmonicAffineResidualNorm_eq_zero_on_smaller
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (p : X) {r t : ℝ}
    (hr : 0 < r) (htr : t ≤ r) (w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : harmonicTargetNorm hX p r w = 0) :
    harmonicAffineResidualNorm hX u p t w = 0 := by
  have hz := restrictLp_eq_zero_of_harmonicTargetNorm_eq_zero hX p hr w hw
  have hreps := (SobolevSpace.restrictLp_eq_zero_iff (hausdorff n X) hX.quadratic
    (ball p r) w).mp hz
  have hzt := (SobolevSpace.restrictLp_eq_zero_iff (hausdorff n X) hX.quadratic
    (ball p t) w).mpr (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball htr) hreps)
  simp only [harmonicAffineResidualNorm, hzt, map_zero, normalizeLocalL2, smul_zero, norm_zero]

/-- The unit-norm estimate implies the full homogeneous estimate, including
the zero-norm case. -/
theorem HasNormalizedAffineImprovement.homogeneous
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {p : X} {r θ : ℝ}
    (hfit : HasNormalizedAffineImprovement hX u p r θ) (hr : 0 < r) (hθ : θ ≤ 1)
    (w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) w) :
    harmonicAffineResidualNorm hX u p (θ * r) w ≤
      (1 / 2 : ℝ) * θ * Real.sqrt θ * harmonicTargetNorm hX p r w := by
  by_cases hz : harmonicTargetNorm hX p r w = 0
  · rw [harmonicAffineResidualNorm_eq_zero_on_smaller hX u p hr
      (mul_le_of_le_one_left hr.le hθ) w hz, hz, mul_zero]
  have ht : 0 < harmonicTargetNorm hX p r w :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hn : harmonicTargetNorm hX p r ((harmonicTargetNorm hX p r w)⁻¹ • w) ≤ 1 := by
    rw [harmonicTargetNorm_smul, abs_of_pos (inv_pos.2 ht), inv_mul_cancel₀ hz]
  have hh := hfit ((harmonicTargetNorm hX p r w)⁻¹ • w)
    (hw.smul (hausdorff n X) hX.quadratic _) hn
  change harmonicAffineResidualNorm hX u p (θ * r)
    ((harmonicTargetNorm hX p r w)⁻¹ • w) < _ at hh
  rw [harmonicAffineResidualNorm_smul, abs_of_pos (inv_pos.2 ht)] at hh
  have hh' := mul_lt_mul_of_pos_left hh ht
  rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul] at hh'
  exact hh'.le.trans_eq (mul_comm _ _)

end RegularPointCoordinates

end

end OAI
