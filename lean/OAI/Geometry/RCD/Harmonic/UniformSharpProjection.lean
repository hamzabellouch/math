import OAI.Geometry.RCD.Harmonic.SharpProjectionFamily

namespace OAI

/-! # A single sharp-projection constant and Euclidean threshold -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The collected Poisson and projection estimates imply one constant
and one threshold, uniformly over the center, dyadic scale and configuration.
The proof constructs the countersequence rather than assuming compactness
for a normalized projection residual. -/
theorem SharpProjectionFamily.uniform_bound {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    {I : Type*} {S ρ : ℝ} (d : SharpProjectionFamily hX I S ρ)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ i, d.error i < δ → d.size i ≤ C * d.source i := by
  classical
  by_contra hfail
  obtain ⟨t, hpos, hε, hratio, hratioBound⟩ := projection_failure_sequence_with_ratio_bound
    d.error d.size d.source (fun i => (d.error_pos i).le) d.source_pos hfail
  let q := d.compactnessSequence hgradient hn hS t hε
  let M := 2 * d.outerConstant + 1
  have hM : 0 < M := by dsimp only [M]; linarith [d.outerConstant_nonneg]
  have hsmall (i : ℕ) : d.source (t i) ≤ d.size (t i) :=
    (div_le_one (hpos i)).mp (hratioBound i)
  have houter (i : ℕ) : ‖normalizeLocalL2 (hausdorff n X)
      (ball (d.center (t i)) (S * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (S * d.radius (t i))) (d.residual (t i)))‖ ≤ M * d.size (t i) := by
    have hb := (d.outer_bound (t i)).trans (mul_le_mul_of_nonneg_left
      (show d.size (t i) + d.source (t i) ≤ 2 * d.size (t i) by linarith [hsmall i])
      d.outerConstant_nonneg)
    dsimp only [M]
    nlinarith [hpos i]
  have hcoeff (i : ℕ) : ‖d.coefficient (t i)‖ + |d.constant (t i)| ≤
      (2 * d.coefficientConstant) * d.size (t i) := by
    have hb := (d.coefficient_bound (t i)).trans (mul_le_mul_of_nonneg_left
      (show d.size (t i) + d.source (t i) ≤ 2 * d.size (t i) by linarith [hsmall i])
      d.coefficientConstant_nonneg)
    nlinarith
  have herr := normalized_source_error_tendsto_zero
    (fun i => normalizeLocalL2 (hausdorff n X)
      (ball (d.center (t i)) (S * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (S * d.radius (t i))) (d.forcing (t i))))
    hpos (fun i => d.forcing_bound (t i)) hratio
  have hcontr := no_projected_euler_sequence hcompact hgradient hn hS hρ hρS hM q
    (d.target ∘ t) (d.residual ∘ t) (d.forcing ∘ t) (d.coefficient ∘ t) (d.constant ∘ t)
    (fun i => d.radialBound / d.radius (t i) ^ 2)
    (fun i => d.gradient (t i)) (fun i => d.harmonic (t i))
    (fun i => d.projection (t i)) (fun i => d.euler_identity (t i)) (C := 2 * d.coefficientConstant)
  apply hcontr
  · intro i
    change 0 < ‖normalizeLocalL2 (hausdorff n X) (ball (d.center (t i)) (ρ * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (ρ * d.radius (t i))) (d.residual (t i)))‖
    rw [← d.size_eq]
    exact hpos i
  · intro i
    change _ ≤ M * ‖normalizeLocalL2 (hausdorff n X) (ball (d.center (t i)) (ρ * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (ρ * d.radius (t i))) (d.residual (t i)))‖
    rw [← d.size_eq]
    exact houter i
  · intro i
    change _ ≤ (2 * d.coefficientConstant) * ‖normalizeLocalL2 (hausdorff n X)
      (ball (d.center (t i)) (ρ * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (ρ * d.radius (t i))) (d.residual (t i)))‖
    rw [← d.size_eq]
    exact hcoeff i
  · change Tendsto (fun i => ‖normalizeLocalL2 (hausdorff n X)
      (ball (d.center (t i)) (S * d.radius (t i)))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center (t i)) (S * d.radius (t i)))
        ((‖normalizeLocalL2 (hausdorff n X) (ball (d.center (t i)) (ρ * d.radius (t i)))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
            (ball (d.center (t i)) (ρ * d.radius (t i))) (d.residual (t i)))‖)⁻¹ •
          d.forcing (t i)))‖) atTop (𝓝 0)
    simpa only [← d.size_eq, map_smul, normalizeLocalL2_smul] using herr

end RegularPointCoordinates

end

end OAI
