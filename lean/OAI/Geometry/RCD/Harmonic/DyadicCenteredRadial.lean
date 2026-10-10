import OAI.Geometry.RCD.Coordinates.CanonicalCenteredFits

namespace OAI

/-! # Centered radial fits with the actual summable Poisson defect -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The original distance replacements, common harmonic map and exact
normalizing frames produce centered radial fits with the two-convolution
Poisson envelope. No radial-fit estimate is assumed. -/
theorem dyadic_centered_radial_estimate {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [IsFiniteMeasureOnCompacts (hausdorff (m + 2) X)]
    (hhessian : LocalPoissonHessianInput hX)
    {a κ r0 B J C A Cχ L δ : ℝ} {p : X}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hCχ : 0 ≤ Cχ)
    (hr01 : r0 ≤ 1) (hscale : a * (3 * r0) ≤ 1)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (S : DyadicDistanceSources (hausdorff (m + 2) X) hX.quadratic (m + 2) κ p r0)
    (T : DyadicDistanceReplacements (hausdorff (m + 2) X) hX.quadratic S B J C)
    (hP : Summable (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ r0 →
      |(hausdorff (m + 2) X).real (ball p t) / (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4)
    (u : Fin (m + 2) → SobolevSpace (hausdorff (m + 2) X) hX.quadratic)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (F : ℕ → Euclidean (m + 2) ≃L[ℝ] Euclidean (m + 2))
    (v : ℕ → X → Euclidean (m + 2)) (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant (m + 2) * δ ≤ 1)
    (hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * δ) ≤ 1 / 64)
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 2) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 2) X) hX.quadratic u)
      (ball p (2 * distanceSourceRadius r0 i)) measurableSet_ball (F i))
    (hfirst : ∀ i, FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p
      (2 * distanceSourceRadius r0 i) δ (transformedColumn (hausdorff (m + 2) X) hX.quadratic u (F i)) (v i))
    (hmetric : ∀ i, IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v i x - v i p)))
    (hf : ∀ i, ∀ᵐ x ∂(hausdorff (m + 2) X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff (m + 2) X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : ∀ i, GoodLaplacianCutoff (hausdorff (m + 2) X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    {d : ℕ} (hd : 0 < d)
    (hfit : ∀ i, HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ d))
    (hmean : LocalHarmonicL2MeanValueInput hX) {κ₀ ε : ℝ} (hκ₀ : 0 ≤ κ₀)
    (V : X → Euclidean (m + 2))
    (hu : FirstOrderSplittingOn (hausdorff (m + 2) X) hX.quadratic p r0 ε u V)
    (hcurv : ∀ i, -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ b : Euclidean (m + 2), b ≠ 0 →
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
  obtain ⟨Z, hZ, hfits⟩ := dyadic_radial_fit_summability m hX hhessian ha hκ hK hB hJ hA hCχ
    hr01 hscale hBG S T hP hquarter u hbase F v hδ hδ1 hsmall hexact hfirst hmetric hf χ hd hfit
  have hη : 0 ≤ radialFitQualitativeConstant (m + 2) Cχ * δ :=
    mul_nonneg (radialFitQualitativeConstant_nonneg (m + 2) hCχ) hδ
  have hPN := normalizedPoissonDefect_nonneg (hausdorff (m + 2) X) hX.quadratic S hκ
  have hQ := forwardDefect_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hη hPN
  have hQs := (forwardDefect_budget (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hη hPN hP).1
  exact canonical_centered_fits_of_squared_bound m hX hmean hκ₀ ha hδ hBG
    S T u V hu hbase hscale hsmall F v hexact hfirst hcurv hquarter hZ
    (forwardDefect (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
      (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S))
    hQ hQs (fun b hb => (hfits b hb).1)

/-- The envelope used above is summable with its original full Poisson
budget. The two fixed geometric convolutions cost the explicit factor 64. -/
theorem radial_fit_pinching_envelope_budget {μ : Measure X} {hQ : QuadraticCheegerEnergy μ}
    [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} {κ r0 Cχ δ : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0)
    (hκ : 0 ≤ κ) (hCχ : 0 ≤ Cχ) (hδ : 0 ≤ δ)
    (hP : Summable (normalizedPoissonDefect μ hQ S)) :
    let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * δ)
      (normalizedPoissonDefect μ hQ S)
    Summable E ∧ (∑' i, E i) ≤
      64 * (radialFitQualitativeConstant n Cχ * δ + ∑' i, normalizedPoissonDefect μ hQ S i) ∧
      ∀ i, 0 ≤ E i ∧ normalizedPoissonDefect μ hQ S i ≤ E i := by
  dsimp only
  have hη := mul_nonneg (radialFitQualitativeConstant_nonneg n hCχ) hδ
  have hPN := normalizedPoissonDefect_nonneg μ hQ S hκ
  have hQn := forwardDefect_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hη hPN
  obtain ⟨hQs, hQsum⟩ := forwardDefect_budget (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hη hPN hP
  obtain ⟨hEs, hEsum⟩ := symmetricDefect_budget (by norm_num : (0 : ℝ) ≤ 7 / 8)
    (by norm_num : (7 / 8 : ℝ) < 1) hQn hQs
  refine ⟨hEs, ?_, fun i => ⟨symmetricDefect_nonneg (by norm_num) hQn i, ?_⟩⟩
  · have hh := hEsum.trans (mul_le_mul_of_nonneg_left hQsum (by norm_num))
    norm_num at hh
    simpa only [pinchingEnvelope, ← mul_assoc, show (16 : ℝ) * 4 = 64 by norm_num] using hh
  · exact (le_forwardDefect (by norm_num) hη hPN i).trans
      (le_symmetricDefect (by norm_num) (by norm_num) hQn hQs i)

end RegularPointCoordinates

end

end OAI
