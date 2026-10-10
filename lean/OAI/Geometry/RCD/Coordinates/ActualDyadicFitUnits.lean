import OAI.Geometry.RCD.Coordinates.ActualDyadicFitStep
import OAI.Geometry.RCD.Coordinates.DyadicFitVolumeUnits
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # The canonical dyadic fit recurrence in scale-independent units -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The quarter-error volume regime removes every physical radius and volume
factor from the actual covector-fit step. -/
theorem actual_dyadic_radial_fit_natural_units {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) (hhessian : LocalPoissonHessianInput hX)
    {κ r0 B J C A epsilon Cχ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon) (hCχ : 0 ≤ Cχ)
    (p : X) (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C) (i : ℕ)
    (hs1 : distanceSourceRadius r0 i ≤ 1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball p (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)))
    (hdouble : 2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) ≤
      (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64))))
    (m : ℕ)
    (hfit : HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ m))
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ distanceSourceRadius r0 i →
      |(hausdorff n X).real (ball p t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4) :
    let μ := hausdorff n X
    let s := distanceSourceRadius r0 i
    let r := s / 64
    let θ := (1 / 2 : ℝ) ^ m
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left
      (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; positivity : 0 ≤ r)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)))
    let Λ := Real.sqrt ((5 / 3 : ℝ) * (θ ^ n)⁻¹)
    let D := (4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n
    let coefficient := (64 / θ) * (Λ + (1 / 2 : ℝ) * θ * Real.sqrt θ) *
      Real.sqrt ((n : ℝ) * radialCorrectionConstant K n epsilon A B J Cχ * D)
    ∀ b : Euclidean n,
      let ha := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) (1 + epsilon)
        (fun j => ae_restrict_of_ae_restrict_of_subset
          (ball_subset_ball (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; linarith : r ≤ s / 4))
          (hgrad j)) b
      let hat := ae_restrict_of_ae_restrict_of_subset hsub ha
      radialFitError μ hX.quadratic u p (θ * r) ht (T.distanceDatum μ hX.quadratic (i + m))
        (sobolevColumnMap μ hX.quadratic u b) hat ≤
      (1 / 2 : ℝ) * Real.sqrt θ * radialFitError μ hX.quadratic u p r hs
        (T.distanceDatum μ hX.quadratic i) (sobolevColumnMap μ hX.quadratic u b) ha +
      coefficient * Real.sqrt (normalizedPoissonDefect μ hX.quadratic S i) * ‖b‖ := by
  dsimp only
  let μ := hausdorff n X
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let θ := (1 / 2 : ℝ) ^ m
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hθ : 0 < θ := pow_pos (by norm_num) _
  have hθ1 : θ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hv := hquarter r hr (by dsimp only [r]; linarith)
  have hw := hquarter (θ * r) (mul_pos hθ hr)
    ((mul_le_of_le_one_left hr.le hθ1).trans (by dsimp only [r]; linarith))
  have homega := euclideanUnitVolume_pos n
  have hratio := radial_testing_volume_ratio hs homega hv
  have hV := radial_sqrt_volume_ratio hr hθ homega (measureReal_nonneg : 0 ≤ μ.real (ball p r)) hv hw
  have hC := (radialCorrectionConstant_pos (K := K) (n := n)
    (epsilon := epsilon) (A := A) hB hJ hCχ).le
  have hQ := normalizedPoissonDefect_nonneg μ hX.quadratic S hκ i
  have hstep := actual_dyadic_radial_fit_step hX hn hhessian hκ hK hB hJ hA hepsilon hCχ
    p S T i hs1 u hu hgrad hf χ hvol hdouble m hfit
  dsimp only at hstep
  intro b
  have he := hstep b
  have he' := radial_covector_fit_natural_units hs hθ
    (by positivity : 0 ≤ Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r))))
    hQ (mul_nonneg (Nat.cast_nonneg n) hC)
    (by positivity : 0 ≤ (4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)
    (norm_nonneg b) hV hratio
    (by simpa only [mul_assoc] using he)
  exact he'

end RegularPointCoordinates

end

end OAI
