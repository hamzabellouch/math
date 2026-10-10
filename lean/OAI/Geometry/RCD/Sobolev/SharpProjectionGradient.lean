import OAI.Geometry.RCD.Harmonic.UniformSharpProjection

namespace OAI

/-! # Interior gradient control from the sharp projection estimate -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The uniform sharp L2 projection bound yields the interior gradient
estimate in natural radius units. The constants precede every configuration. -/
theorem SharpProjectionFamily.uniform_gradient_bound {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} {I : Type*} {S ρ : ℝ}
    (d : SharpProjectionFamily hX I S ρ)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S) :
    ∃ G : ℝ, 0 < G ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i, d.error i < δ →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (d.center i) (ρ / 2 * d.radius i)),
        d.radius i ^ 2 * localGamma (hausdorff n X) hX.quadratic
          (d.residual i) (d.residual i) x ≤ G ^ 2 * d.source i ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hbound⟩ := d.uniform_bound hcompact hgradient hn hS hρ hρS
  obtain ⟨D, hD, hgrad⟩ := hgradient hn (ρ ^ 2) (1 / 2)
    (sq_nonneg ρ) (by norm_num) (by norm_num)
  refine ⟨D * C / ρ, div_pos (mul_pos (by linarith) hC) hρ, δ, hδ, ?_⟩
  intro i hi
  have hr := d.radius_pos i
  have hcurv : -(ρ ^ 2) ≤ K * (ρ * d.radius i) ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left (d.curvature i) (sq_nonneg ρ)
    nlinarith only [hc]
  have hw := (d.harmonic i).mono (hausdorff n X) hX.quadratic
    (ball_subset_ball (mul_le_mul_of_nonneg_right hρS.le hr.le))
  have hg := hgrad (d.center i) (ρ * d.radius i) (mul_pos hρ hr) hcurv (d.residual i) hw
  have hmean : ((hausdorff n X).real (ball (d.center i) (ρ * d.radius i)))⁻¹ *
      (∫ x in ball (d.center i) (ρ * d.radius i),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (d.residual i) x) ^ 2 ∂hausdorff n X) =
        d.size i ^ 2 := by
    rw [← normalized_sobolev_mean_sq (hausdorff n X) hX.quadratic _
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)), ← d.size_eq]
  rw [hmean] at hg
  have hsize : 0 ≤ d.size i := by rw [d.size_eq]; exact norm_nonneg _
  have hsq : d.size i ^ 2 ≤ (C * d.source i) ^ 2 :=
    (sq_le_sq₀ hsize (mul_pos hC (d.source_pos i)).le).mpr (hbound i hi)
  have hradius : (1 / 2 : ℝ) * (ρ * d.radius i) = ρ / 2 * d.radius i := by ring
  rw [hradius] at hg
  filter_upwards [hg] with x hx
  calc
    _ ≤ d.radius i ^ 2 * ((D / (ρ * d.radius i)) ^ 2 * d.size i ^ 2) :=
      mul_le_mul_of_nonneg_left hx (sq_nonneg _)
    _ ≤ d.radius i ^ 2 * ((D / (ρ * d.radius i)) ^ 2 * (C * d.source i) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)
    _ = (D * C / ρ) ^ 2 * d.source i ^ 2 := by field_simp [hρ.ne', hr.ne']

end RegularPointCoordinates

end

end OAI
