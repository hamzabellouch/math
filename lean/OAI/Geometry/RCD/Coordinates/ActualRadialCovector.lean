import OAI.Geometry.RCD.Harmonic.ActualRadialError
import OAI.Geometry.RCD.Harmonic.RadialLinearCombination

namespace OAI

/-! # Actual radial approximation in every constant covector -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual component corrections extend to every constant covector.
The dimension loss is fixed and the only source remains the same complete
Poisson defect; no direction-dependent error is postulated. -/
theorem actual_distance_radial_covector_error {K : ℝ} {n : ℕ}
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
      (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64)))) :
    let s := distanceSourceRadius r0 i
    let q := positiveSquaredDistance (hausdorff n X) hX.quadratic
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
    ∀ b : Euclidean n, ∃ h : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (s / 64)) h ∧
      (∫ x in ball p (s / 64),
        (localGamma (hausdorff n X) hX.quadratic q
          (sobolevColumnMap (hausdorff n X) hX.quadratic u b) x -
          SobolevSpace.toLp (hausdorff n X) hX.quadratic h x) ^ 2 ∂hausdorff n X) ≤
        (n : ℝ) * (radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 *
          (s ^ (n : ℝ) * normalizedPoissonDefect (hausdorff n X) hX.quadratic S i)) * ‖b‖ ^ 2 := by
  dsimp only
  let μ := hausdorff n X
  let s := distanceSourceRadius r0 i
  let q := positiveSquaredDistance μ hX.quadratic
    (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
  have ha := actual_distance_radial_error hX hn hhessian hκ hK hB hJ hA hepsilon hCχ
    p S T i hs1 u hu hgrad hf χ hvol hdouble
  dsimp only at ha
  choose h hh he using ha
  intro b
  refine ⟨sobolevColumnMap μ hX.quadratic h b, ?_⟩
  apply radial_linear_harmonic_correction μ hX.quadratic q u h hh
  · intro j
    have hj := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by have := distanceSourceRadius_pos S.radius_pos i; dsimp only [s]; linarith :
        s / 64 ≤ s / 4)) (hgrad j)
    exact (localGamma_memLp_two_of_bound μ hX.quadratic (ball p (s / 64)) q (u j) hj).sub
      ((Lp.memLp (SobolevSpace.toLp μ hX.quadratic (h j))).restrict _)
  · exact he

end RegularPointCoordinates

end

end OAI
