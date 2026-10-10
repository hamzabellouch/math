import OAI.Geometry.RCD.Coordinates.DyadicRadialFitEstimates
import OAI.Geometry.RCD.Coordinates.DyadicCovectorGrowth
import OAI.Geometry.RCD.Coordinates.RadialFitEnvelope

namespace OAI

/-! # Summable errors for the actual radial derivative and original covectors -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual distance replacements and the same dyadic normalizing
frames give summable normalized squared fit errors. All analytic error
terms are the original Poisson defect; no radial estimate is assumed. -/
theorem dyadic_radial_fit_summability {K : ℝ} (m : ℕ)
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
    (hfit : ∀ i, HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ d)) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ b : Euclidean (m + 2), b ≠ 0 →
      (∀ i, (dyadicRadialFit hX T u L hbase i b) ^ 2 ≤
        Z * forwardDefect (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * δ)
          (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S) i * ‖(F i).symm b‖ ^ 2) ∧
      Summable (fun i => (dyadicRadialFit hX T u L hbase i b / ‖(F i).symm b‖) ^ 2) ∧
      (∑' i, (dyadicRadialFit hX T u L hbase i b / ‖(F i).symm b‖) ^ 2) ≤
        4 * Z * (radialFitQualitativeConstant (m + 2) Cχ * δ +
          ∑' i, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic S i) := by
  let μ := hausdorff (m + 2) X
  let P := normalizedPoissonDefect μ hX.quadratic S
  let E := dyadicRadialFit hX T u L hbase
  let η := radialFitQualitativeConstant (m + 2) Cχ * δ
  have hη : 0 ≤ η := mul_nonneg (radialFitQualitativeConstant_nonneg (m + 2) hCχ) hδ
  have hδle : δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (radialNormalizationRestrictionConstant_ge_one (m + 2)) hδ
    linarith
  have hrad (i : ℕ) : 2 * distanceSourceRadius r0 i = r0 / (2 : ℝ) ^ i := by
    unfold distanceSourceRadius
    rw [pow_succ]
    ring
  have hfirst' (i : ℕ) : ∃ w : X → Euclidean (m + 2),
      FirstOrderSplittingOn μ hX.quadratic p (r0 / 2 ^ i) δ
        (transformedColumn μ hX.quadratic u (F i)) w := by
    exact ⟨v i, by simpa only [hrad] using hfirst i⟩
  have hgrowth := dyadic_covector_norm_growth (m + 1) hX ha hBG u p S.radius_pos hscale hδ hsmall F
    (fun i => by simpa only [hrad] using hexact i) hfirst'
  obtain ⟨Z, hZ, henv⟩ := radial_fit_forward_envelope hd
    (radialFitStepConstant_nonneg K (m + 2) A B J Cχ d)
  refine ⟨Z, hZ, ?_⟩
  intro b hb
  have hw (i : ℕ) : 0 < ‖(F i).symm b‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hb
    have he := congrArg (F i) hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using he
  have hPN (i : ℕ) : 0 ≤ P i := normalizedPoissonDefect_nonneg μ hX.quadratic S hκ i
  have hqual (i : ℕ) : (E i b) ^ 2 ≤ η * ‖(F i).symm b‖ ^ 2 := by
    apply dyadicRadialFit_smallness hX T u hbase hδ hδ1 hCχ i (F i) (v i)
      (hfirst i) (hmetric i) (χ i)
    intro t ht hts
    exact hquarter t ht (hts.trans (distanceSourceRadius_outer_le S.radius_pos.le i))
  have hstep (i : ℕ) : E (i + d) b ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) ^ d) * E i b +
      radialFitStepConstant K (m + 2) A B J Cχ d * ‖(F i).symm b‖ * Real.sqrt (P i) := by
    have hs := distanceSourceRadius_pos S.radius_pos i
    have hsle : distanceSourceRadius r0 i ≤ r0 := by
      have hh := distanceSourceRadius_outer_le S.radius_pos.le i
      linarith
    have hsub : ball p (distanceSourceRadius r0 i / 4) ⊆ ball p (2 * distanceSourceRadius r0 i) :=
      ball_subset_ball (by linarith)
    have hu1 := (hfirst i).mono_error μ hX.quadratic hδ hδle
    have hann := relative_volume_annulus (show 2 ≤ m + 2 by omega)
      (show 0 < distanceSourceRadius r0 i / 64 by positivity) (euclideanUnitVolume_pos (m + 2))
      (hquarter (distanceSourceRadius r0 i / 64) (by positivity) (by linarith))
      (hquarter (2 * (distanceSourceRadius r0 i / 64)) (by positivity) (by linarith))
    exact dyadicRadialFit_step hX T u hbase (by omega) hhessian hκ hK hB hJ hA hCχ i
      (hsle.trans hr01) (F i) (fun j => (hu1.harmonic j).mono μ hX.quadratic hsub)
      (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hu1.gradient j)) (hf i) (χ i)
      hann.1 hann.2 d (hfit i) (fun t ht hts => hquarter t ht (hts.trans hsle)) b
  have hbound := henv hη hPN (fun i => dyadicRadialFit_nonneg hX T u L hbase i b) hw hqual
    (fun i => hgrowth i d b) hstep
  have hbudget := normalized_squared_fit_budget (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hη hZ.le hPN hP hw hbound
  refine ⟨hbound, hbudget.1, ?_⟩
  simpa only [show (1 - (3 / 4 : ℝ))⁻¹ = 4 by norm_num, mul_comm Z 4] using hbudget.2

end RegularPointCoordinates

end

end OAI
