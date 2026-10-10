import OAI.Geometry.SurfaceImmersion.Geometry.AxisFlatBounds
import OAI.Geometry.SurfaceImmersion.Whitney.SlowCollarCutoff

namespace OAI

/-! A logarithmically slow cutoff preserves the first-order smallness
of any remainder with zero value and derivative along the axis. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem slow_flat_remainder_bound {R : Base → W} {χ : ℝ → ℝ}
    (hR : ContDiff ℝ ∞ R) (hχ : ContDiff ℝ ∞ χ)
    (h0 : ∀ t, R (crosscapAxis t) = 0)
    (hD0 : ∀ t, fderiv ℝ R (crosscapAxis t) = 0)
    {ρ C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ closedBall (0 : Base) ρ, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ C)
    (hχb : ∀ t, |χ t| ≤ 1) (hχd : ∀ t, |t*deriv χ t| ≤ 1)
    {x : Base} (hx : x ∈ closedBall (0 : Base) ρ) :
    ‖fderiv ℝ (fun y => χ (y 0) • R y) x‖ ≤
      (1 + ‖(ContinuousLinearMap.proj 0 : Base →L[ℝ] ℝ)‖)*C*|x 0| := by
  let P : Base →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hv := axis_flat_value_bound hR h0 hD0 hC hb hx
  have hd := axis_flat_first_bound hR hD0 hb hx
  have hχD : HasFDerivAt (fun y : Base => χ (y 0)) (deriv χ (x 0) • P) x := by
    have h := ((hχ.differentiable (by simp) _).hasDerivAt.hasFDerivAt).comp x
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x)
    change HasFDerivAt (fun y : Base => χ (y 0)) _ x at h
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (deriv χ (x 0))).comp
        (ContinuousLinearMap.proj 0) = deriv χ (x 0) • P := by
      ext v
      simp [P, mul_comm]
    rw [he] at h
    exact h
  have hp := hχD.smul (hR.differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun y => χ (y 0) • R y) _ x at hp
  have hweighted : |deriv χ (x 0)| * ‖R x‖ ≤ C*|x 0| := by
    calc
      _ ≤ |deriv χ (x 0)| * (C*|x 0|^2) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = (C*|x 0|) * |x 0*deriv χ (x 0)| := by rw [abs_mul]; ring
      _ ≤ (C*|x 0|)*1 := mul_le_mul_of_nonneg_left (hχd _) (mul_nonneg hC (abs_nonneg _))
      _ = _ := mul_one _
  rw [hp.fderiv]
  calc
    _ ≤ ‖χ (x 0) • fderiv ℝ R x‖ + ‖(deriv χ (x 0) • P).smulRight (R x)‖ := norm_add_le _ _
    _ = |χ (x 0)| * ‖fderiv ℝ R x‖ + ‖P‖*(|deriv χ (x 0)| * ‖R x‖) := by
      rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply,
        norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ 1*(C*|x 0|) + ‖P‖*(C*|x 0|) := add_le_add
      (mul_le_mul (hχb _) hd (norm_nonneg _) (by norm_num))
      (mul_le_mul_of_nonneg_left hweighted (norm_nonneg _))
    _ = _ := by dsimp [P]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
