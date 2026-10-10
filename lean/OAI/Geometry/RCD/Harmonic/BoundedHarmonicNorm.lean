import OAI.Geometry.RCD.Harmonic.HarmonicAffineImprovement

namespace OAI

/-! # The normalized harmonic L2 norm from an actual local value bound -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.harmonicTargetNorm_le_of_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (p : X) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hb : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ M) :
    harmonicTargetNorm hX p R w ≤ M := by
  let μ := hausdorff n X
  have hf : μ (ball p R) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hm : 0 < μ.real (ball p R) := ENNReal.toReal_pos (hX.fullSupport p R hR).ne' hf
  have hi : (∫ x in ball p R, (SobolevSpace.toLp μ hX.quadratic w x)^2 ∂μ) ≤
      M^2*μ.real (ball p R) := by
    calc
      _ ≤ ∫ _ in ball p R, M^2 ∂μ := integral_mono_ae
        (Lp.memLp _).integrable_sq.integrableOn (integrableOn_const hf) (by
          filter_upwards [hb] with x hx
          change |SobolevSpace.toLp μ hX.quadratic w x| ≤ M at hx
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2)
      _ = _ := by simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
  apply (sq_le_sq₀ (norm_nonneg _) hM).mp
  change (harmonicTargetNorm hX p R w)^2 ≤ M^2
  have he : (harmonicTargetNorm hX p R w)^2 = (μ.real (ball p R))⁻¹*
      ∫ x in ball p R, (SobolevSpace.toLp μ hX.quadratic w x)^2 ∂μ :=
    normalized_sobolev_mean_sq μ hX.quadratic (ball p R) hf w
  rw [he]
  exact (mul_le_mul_of_nonneg_left hi (inv_pos.mpr hm).le).trans_eq (by field_simp)

end RegularPointCoordinates

end

end OAI
