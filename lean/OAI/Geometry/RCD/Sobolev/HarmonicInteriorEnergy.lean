import OAI.Geometry.RCD.Sobolev.HarmonicGradientInput

namespace OAI

/-! # Interior energy bounds from the harmonic gradient estimate -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- Normalizing the outer L² norm gives a uniform scaled energy bound on
every fixed inner fraction. The function need not be bounded pointwise. -/
theorem LocalHarmonicL2GradientInput.interior_energy {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), ∀ _hR : 0 < R, -a ≤ K * R ^ 2 →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
        ‖normalizeLocalL2 (hausdorff n X) (ball p R)
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) w)‖ ≤ 1 →
        R ^ 2 * ((hausdorff n X).real (ball p R))⁻¹ *
          (∫ x in ball p (τ * R), localGamma (hausdorff n X) hX.quadratic w w x
            ∂hausdorff n X) ≤ C ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hinput hn a τ ha hτ hτ1
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv w hw hnorm
  let μ := hausdorff n X
  have hfinite : μ (ball p R) ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  have hmass : 0 < μ.real (ball p R) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p R hR)) hfinite
  have hsub : ball p (τ * R) ⊆ ball p R :=
    ball_subset_ball (by nlinarith)
  have hmean := sobolev_mean_sq_le_one_of_normalized μ hX.quadratic (ball p R) hfinite w hnorm
  have hpoint : ∀ᵐ x ∂μ.restrict (ball p (τ * R)),
      localGamma μ hX.quadratic w w x ≤ (C / R) ^ 2 := by
    filter_upwards [hb p R hR hcurv w hw] with x hx
    exact hx.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hmean (sq_nonneg (C / R)))
  have hint : IntegrableOn (localGamma μ hX.quadratic w w) (ball p (τ * R)) μ :=
    (localGamma_memL1 μ hX.quadratic w w).integrableOn
  let : IsFiniteMeasure (μ.restrict (ball p (τ * R))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hX.finiteOnBounded
      (ball p (τ * R)) isBounded_ball)⟩
  have hi : (∫ x in ball p (τ * R), localGamma μ hX.quadratic w w x ∂μ) ≤
      (C / R) ^ 2 * μ.real (ball p R) := by
    calc
      _ ≤ ∫ _x in ball p (τ * R), (C / R) ^ 2 ∂μ :=
        integral_mono_ae hint (integrable_const _) hpoint
      _ = (C / R) ^ 2 * μ.real (ball p (τ * R)) := by
        simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (measureReal_mono hsub hfinite) (sq_nonneg _)
  calc
    _ ≤ R ^ 2 * (μ.real (ball p R))⁻¹ * ((C / R) ^ 2 * μ.real (ball p R)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = C ^ 2 := by field_simp

end RegularPointCoordinates

end

end OAI
