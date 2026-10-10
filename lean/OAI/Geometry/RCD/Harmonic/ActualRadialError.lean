import OAI.Geometry.RCD.Harmonic.RadialErrorUnits

namespace OAI

/-! # Actual radial approximation controlled by one normalized defect -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The coefficient is independent of the center, scale and harmonic column.
The source and curvature terms are exactly the summable complete defect. -/
theorem actual_distance_radial_error {K : ℝ} {n : ℕ}
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
    ∀ j : Fin n, ∃ h : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (s / 64)) h ∧
      (∫ x in ball p (s / 64),
        (localGamma (hausdorff n X) hX.quadratic q (u j) x -
          SobolevSpace.toLp (hausdorff n X) hX.quadratic h x) ^ 2 ∂hausdorff n X) ≤
        radialCorrectionConstant K n epsilon A B J Cχ * s ^ 2 *
          (s ^ (n : ℝ) * normalizedPoissonDefect (hausdorff n X) hX.quadratic S i) := by
  dsimp only
  obtain ⟨L, hL, happrox⟩ := actual_distance_radial_approximation hX hn hhessian
    hκ hK hB hJ hA hepsilon hCχ p S T i hs1 u hu hgrad hf χ hvol hdouble
  intro j
  obtain ⟨h, hh, he⟩ := happrox j
  refine ⟨h, hh, he.trans ?_⟩
  rw [normalizedPoissonDefect_units]
  exact radial_correction_error_units hs1 hκ measureReal_nonneg measureReal_nonneg
    hB hJ hA hepsilon hCχ hL

end RegularPointCoordinates

end

end OAI
