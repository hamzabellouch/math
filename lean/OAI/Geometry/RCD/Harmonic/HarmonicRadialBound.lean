import OAI.Geometry.RCD.Sobolev.HarmonicGradientInput
import OAI.Geometry.RCD.Harmonic.RadialDerivativeNorms

namespace OAI

/-! # Radial derivatives of harmonic residuals on an interior ball -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published harmonic gradient estimate controls the actual radial
derivative on the inner ball by the outer value norm. No normalization of
the function or division by that norm is used. -/
theorem LocalHarmonicL2GradientInput.radial_derivative_bound
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (f w : SobolevSpace (hausdorff n X) hX.quadratic) (B : ℝ), 0 ≤ B →
      ∀ hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R / 2)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ B ^ 2,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
      ‖normalizeLocalL2 (hausdorff n X) (ball p (R / 2))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (localRadialDerivative (hausdorff n X) hX.quadratic (ball p (R / 2)) f hf w)‖ ≤
      (B * C / R) * ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ := by
  obtain ⟨C, hC, hgrad⟩ := hinput hn κ (1 / 2) hκ (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv f w B hB hf hw
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := ball p (R / 2)
  let hfin : μ s ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  let α := ‖normalizeLocalL2 μ (ball p R)
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (SobolevSpace.restrictLp μ hQ (ball p R) w)‖
  have hpos : 0 < μ.real s := ENNReal.toReal_pos
    (ne_of_gt (hX.fullSupport p (R / 2) (by linarith))) hfin
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hg : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ w w x ≤ (C / R) ^ 2 * α ^ 2 := by
    have he := normalized_sobolev_mean_sq μ hQ (ball p R)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) w
    simpa only [α, he, one_div_mul_eq_div] using hgrad p R hR hcurv w hw
  have hi : (∫ x in s, localGamma μ hQ w w x ∂μ) ≤ (C / R) ^ 2 * α ^ 2 * μ.real s := by
    have hh := integral_mono_ae (localGamma_memL1 μ hQ w w).integrableOn
      (integrable_const ((C / R) ^ 2 * α ^ 2)) hg
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using hh
  have hd := normalized_radial_derivative_norm_sq μ hQ s hfin f w hf
  have hb := hd.trans (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ B ^ 2 * (μ.real s)⁻¹))
  have halg : B ^ 2 * (μ.real s)⁻¹ * ((C / R) ^ 2 * α ^ 2 * μ.real s) =
      ((B * C / R) * α) ^ 2 := by field_simp
  rw [halg] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg (mul_nonneg hB (by linarith)) hR.le)
    (norm_nonneg _))).mp hb

end RegularPointCoordinates

end

end OAI
