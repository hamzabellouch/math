import OAI.Geometry.RCD.Coordinates.ActualRadialCovector
import OAI.Geometry.RCD.Sobolev.DirectionalGradientBound
import OAI.Geometry.RCD.Coordinates.RadialFitFromCorrection
import OAI.Geometry.RCD.Harmonic.LocalConstantHarmonic
import OAI.Geometry.RCD.Harmonic.CenteredColumns

namespace OAI

/-! # The actual affine-fit step in every constant covector -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual Poisson construction and harmonic improvement give this
fit estimate. Its only error is the complete summable Poisson defect. -/
theorem actual_distance_radial_covector_fit {K : ℝ} {n : ℕ}
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
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hfit : HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) θ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius r0 i
    let r := s / 64
    let q := positiveSquaredDistance μ hX.quadratic
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left
      (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; positivity : 0 ≤ r) hθ1)
    let C₀ := (1 / 2 : ℝ) * θ * Real.sqrt θ
    let V := Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r)))
    ∀ b : Euclidean n,
      let ha := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) (1 + epsilon)
        (fun j => ae_restrict_of_ae_restrict_of_subset
        (ball_subset_ball (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; linarith : r ≤ s / 4))
        (hgrad j)) b
      let raw := (localGamma_memLp_two_of_bound μ hX.quadratic (ball p r) q
        (sobolevColumnMap μ hX.quadratic u b) ha).toLp
        (localGamma μ hX.quadratic q (sobolevColumnMap μ hX.quadratic u b))
      ‖normalizeLocalL2 μ (ball p (θ * r)) ht
        (affineResidual μ hX.quadratic u (ball p (θ * r)) ht
          (localL2Restriction μ (ball p r) (ball p (θ * r)) hsub raw))‖ ≤
        (V + C₀) * Real.sqrt ((μ.real (ball p r))⁻¹ *
          ((n : ℝ) * (radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 *
            (s ^ (n : ℝ) * normalizedPoissonDefect μ hX.quadratic S i)) * ‖b‖ ^ 2)) +
        C₀ * ‖normalizeLocalL2 μ (ball p r) hs
          (affineResidual μ hX.quadratic u (ball p r) hs raw)‖ := by
  dsimp only
  let μ := hausdorff n X
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let q := positiveSquaredDistance μ hX.quadratic
    (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsub : ball p r ⊆ ball p (s / 4) := ball_subset_ball (by dsimp only [r]; linarith)
  have hu' j := (hu j).mono μ hX.quadratic hsub
  have hη := χ.harmonic_on_inner_ball μ hX.quadratic
  have hone : SobolevSpace.restrictLp μ hX.quadratic (ball p r) χ.sobolev =
      restrictedOne μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) := by
    apply restrictLp_eq_one_of_representative
    filter_upwards [ae_restrict_of_ae χ.representative, ae_restrict_mem measurableSet_ball]
      with x hx hxr
    exact hx.trans (χ.one x hxr)
  have happrox := actual_distance_radial_covector_error hX hn hhessian hκ hK hB hJ hA hepsilon hCχ
    p S T i hs1 u hu hgrad hf χ hvol hdouble
  intro b
  obtain ⟨h, hh, he⟩ := happrox b
  have ha := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) (1 + epsilon)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hgrad j)) b
  have hE : 0 ≤ (n : ℝ) * (radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 *
      (s ^ (n : ℝ) * normalizedPoissonDefect μ hX.quadratic S i)) * ‖b‖ ^ 2 := by
    have hconst := (radialCorrectionConstant_pos (K := K) (n := n)
      (epsilon := epsilon) (A := A) hB hJ hCχ).le
    have hdefect := normalizedPoissonDefect_nonneg μ hX.quadratic S hκ i
    positivity
  exact radial_fit_of_harmonic_correction hX u p hr hθ hθ1 hu' χ.sobolev hη hone hfit
    q (sobolevColumnMap μ hX.quadratic u b) h hE ha hh he

end RegularPointCoordinates

end

end OAI
