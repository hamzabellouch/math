import OAI.Geometry.RCD.Coordinates.ActualCovectorFit
import OAI.Geometry.RCD.Coordinates.DyadicRadialFits

namespace OAI

/-! # The actual dyadic covector-fit step uses the next canonical datum -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Canonical distance targets, actual Poisson corrections and harmonic
improvement give the lagged fit step in every covector. -/
theorem actual_dyadic_radial_fit_step {K : ℝ} {n : ℕ}
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
    (hfit : HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ m)) :
    let μ := hausdorff n X
    let s := distanceSourceRadius r0 i
    let r := s / 64
    let θ := (1 / 2 : ℝ) ^ m
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left
      (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; positivity : 0 ≤ r)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)))
    let V := Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r)))
    ∀ b : Euclidean n,
      let ha := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) (1 + epsilon)
        (fun j => ae_restrict_of_ae_restrict_of_subset
          (ball_subset_ball (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [r, s]; linarith : r ≤ s / 4))
          (hgrad j)) b
      let hat := ae_restrict_of_ae_restrict_of_subset hsub ha
      radialFitError μ hX.quadratic u p (θ * r) ht (T.distanceDatum μ hX.quadratic (i + m))
        (sobolevColumnMap μ hX.quadratic u b) hat ≤
      (V + (1 / 2 : ℝ) * θ * Real.sqrt θ) / (θ * r) *
        Real.sqrt ((μ.real (ball p r))⁻¹ *
          ((n : ℝ) * (radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 *
            (s ^ (n : ℝ) * normalizedPoissonDefect μ hX.quadratic S i)) * ‖b‖ ^ 2)) +
      (1 / 2 : ℝ) * Real.sqrt θ * radialFitError μ hX.quadratic u p r hs
        (T.distanceDatum μ hX.quadratic i) (sobolevColumnMap μ hX.quadratic u b) ha := by
  dsimp only
  let μ := hausdorff n X
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let θ := (1 / 2 : ℝ) ^ m
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hθ : 0 < θ := pow_pos (by norm_num) _
  have hθ1 : θ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsub : ball p r ⊆ ball p (s / 4) := ball_subset_ball (by dsimp only [r]; linarith)
  have hu' j := (hu j).mono μ hX.quadratic hsub
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
  have hstep := radialFitError_step_of_correction hX u p hr hθ hθ1 hu' χ.sobolev
    (χ.harmonic_on_inner_ball μ hX.quadratic) hone hfit
    (T.distanceDatum μ hX.quadratic i) (sobolevColumnMap μ hX.quadratic u b) h hE ha hh he
  have hrad : θ * r = distanceSourceRadius r0 (i + m) / 64 :=
    (distanceSourceRadius_testing_shift r0 i m).symm
  have hat := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)) ha
  have hsame : radialFitError μ hX.quadratic u p (θ * r)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (T.distanceDatum μ hX.quadratic i) (sobolevColumnMap μ hX.quadratic u b) hat =
      radialFitError μ hX.quadratic u p (θ * r)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (T.distanceDatum μ hX.quadratic (i + m)) (sobolevColumnMap μ hX.quadratic u b) hat := by
    apply radialFitError_congr
    rw [hrad]
    exact T.distanceDatum_pairing_later μ hX.quadratic (Nat.le_add_right i m) _
  dsimp only at hstep
  rw [hsame] at hstep
  exact hstep

end RegularPointCoordinates

end

end OAI
