import OAI.Geometry.RCD.Coordinates.UniformCenteredFits
import OAI.Geometry.RCD.Harmonic.UniformRadialSummability
import OAI.Geometry.RCD.Harmonic.DyadicCenteredRadial

namespace OAI

/-! # Uniform centered radial estimates from the original Poisson sources -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Choose the centered radial-fit constant before every center, root,
coordinate map and splitting tolerance. -/
theorem dyadic_centered_radial_estimate_uniform {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    {B J A Cχ κ₀ : ℝ} {d : ℕ} (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A)
    (hCχ : 0 ≤ Cχ) (hκ₀ : 0 ≤ κ₀) (hd : 0 < d) :
    ∃ D : ℝ, 0 < D ∧ ∀ {a κ r0 C L δ ε : ℝ} {p : X},
    ∀ (_ha : 0 ≤ a) (_hκ : 0 ≤ κ) (_hK : -κ ≤ K)
    (_hr01 : r0 ≤ 1) (_hscale : a * (3 * r0) ≤ 1)
    (_hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (_hP : Summable (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    (_hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (v : ℕ → X → Euclidean (m + 2)) (_hδ : 0 ≤ δ)
    (_hδ1 : radialNormalizationRestrictionConstant (m + 2) * δ ≤ 1)
    (_hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (_hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (_hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (v i))
    (_hmetric : ∀ i, IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v i x - v i p)))
    (_hf : ∀ i, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_χ : ∀ i, GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (_hfit : ∀ i, HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ d))
    (V : X → Euclidean (m + 2))
    (_hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u V)
    (_hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2),
    ∀ b : Euclidean (m + 2), b ≠ 0 →
      ∃ c : ℕ → ℝ, ∃ A : ℕ → Euclidean (m + 2),
      (∀ i, affineProjection (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase i b) =
        affineCoordinateMap (hausdorff (m + 2) X) hX.quadratic u
          (ball p (distanceSourceRadius r0 i / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c i, A i)) ∧
      (∀ i, |c i + ⟪V p, A i⟫_ℝ| ≤ D * (distanceSourceRadius r0 i / 64) *
        ‖(F i).symm b‖ * Real.sqrt (pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
            (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S) i)) ∧
      (∀ i, ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball p (distanceSourceRadius r0 i / 64))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (dyadicRadialTarget hX T u hbase i b -
          affineCoordinateMap (hausdorff (m + 2) X) hX.quadratic u
            (ball p (distanceSourceRadius r0 i / 64))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (-⟪V p, A i⟫_ℝ, A i))‖ ≤
        D * (distanceSourceRadius r0 i / 64) * ‖(F i).symm b‖ *
          Real.sqrt (pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
            (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S) i)) := by
  obtain ⟨Z, hZ, hallfits⟩ := dyadic_radial_fit_summability_uniform m hX hhessian
    hB hJ hA hCχ hd
  obtain ⟨D, hD, hcentered⟩ := canonical_centered_fits_of_squared_bound_uniform m hX hmean
    hκ₀ (show (0 : ℝ) ≤ 1 by norm_num) hZ
  refine ⟨D, hD, ?_⟩
  intro a κ r0 C L δ ε p ha hκ hK hr01 hscale hBG S T hP hquarter u hbase F v hδ
    hδ1 hsmall hexact hfirst hmetric hf χ hfit V hu hcurv
  have hfits := hallfits ha hκ hK hr01 hscale hBG S T hP hquarter u hbase F v hδ
    hδ1 hsmall hexact hfirst hmetric hf χ hfit
  have hδle : δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (radialNormalizationRestrictionConstant_ge_one (m + 2)) hδ
    linarith
  have hη : 0 ≤ radialFitQualitativeConstant (m + 2) Cχ * δ :=
    mul_nonneg (radialFitQualitativeConstant_nonneg (m + 2) hCχ) hδ
  have hPN := normalizedPoissonDefect_nonneg (hausdorff (m + 2) X) hX.quadratic S hκ
  have hQ := forwardDefect_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hη hPN
  have hQs := (forwardDefect_budget (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hη hPN hP).1
  exact hcentered ha hδ hδle hBG S T u V hu hbase hscale hsmall F v hexact hfirst hcurv
    hquarter (forwardDefect (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
      (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    hQ hQs (fun b hb => (hfits b hb).1)

end RegularPointCoordinates

end

end OAI
