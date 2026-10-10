import OAI.Geometry.RCD.Coordinates.RegularSharpProjection
import OAI.Geometry.RCD.Harmonic.TwoCenterProjectionBudget

namespace OAI

/-! # The sharp estimate with its actual summable two-center source -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Both radial envelopes and both original Poisson defects are absorbed
by the explicitly constructed positive source; its square sum is controlled
by the same neighborhood tolerances. -/
theorem regular_sharp_projection_actual_sources {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    (hgradient : LocalHarmonicL2GradientInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hmeasured : LocalMeasuredCoordinateInput hX)
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX)
    {κ B J C A Cχ epsilon D : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 *
      (((5 / 3 : ℝ) * (16384 : ℝ) ^ (m + 2)) * epsilon) ≤ 1 / 2) :
    ∃ P tau : ℝ, 0 < P ∧ 0 < tau ∧ ∀ error : ℝ, 0 < error → error ≤ tau →
    ∃ delta : ℝ, 0 < delta ∧
    ∀ {base first center : X} {a enlargement zeta eta Cg Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker},
      0 ≤ a → 0 < zeta → zeta ≤ epsilon → zeta ≤ delta → 0 ≤ eta → eta ≤ tau →
      BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a) →
      ∀ e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta,
      first ∈ ball base (e.heat.radius / 32) → center ∈ ball base (e.heat.radius / 32) →
      ∀ (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
        (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center) (i : ℕ),
      let s := distanceSourceRadius e.heat.radius i
      let uc := centeredColumn (hausdorff (m + 2) X) hX.quadratic
        (transformedColumn (hausdorff (m + 2) X) hX.quadratic e.heat.coordinates (d2.frame i))
        ((d2.frame i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (e.heat.values center))
        e.one.sobolev
      dist center first ≤ s / 4 → -delta / 32 ≤ K * s ^ 2 →
      let sigma := twoCenterProjectionSource
        (radialFitQualitativeConstant (m + 2) Cχ * zeta)
        (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source)
        (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source)
      Summable (fun k => sigma k ^ 2) ∧
      (∑' k, sigma k ^ 2) ≤ 128 * (radialFitQualitativeConstant (m + 2) Cχ * zeta + eta) ∧
                ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball center ((1 / 2048) * s))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (affineResidual (hausdorff (m + 2) X) hX.quadratic
              (radiusScaledColumns (hausdorff (m + 2) X) hX.quadratic s uc)
              (ball center ((1 / 2048) * s)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
              (SobolevSpace.restrictLp (hausdorff (m + 2) X) hX.quadratic
                (ball center ((1 / 2048) * s))
                ((s ^ 2)⁻¹ • (d2.replacement.replacement i - d1.replacement.replacement i))))‖ ≤ P * sigma i := by
  obtain ⟨P, tau, hP, htau, hsharp⟩ := regular_sharp_projection_constants m hX hgradient hmean
    hmeasured hhessian hproduct hpoincare hcompact hκ hK hB hJ hCχ hA hepsilon hsmall
  refine ⟨P, tau, hP, htau, ?_⟩
  intro error herror herrortau
  obtain ⟨delta, hdelta, hbound⟩ := hsharp error herror herrortau
  refine ⟨delta, hdelta, ?_⟩
  intro base first center a enlargement zeta eta Cg Ca ker hk ha hzeta hzetaeps hzetadelta heta hetatau hBG
    e hfirst hcenter d1 d2 i s uc hroom hcurvMeasure
  have hqual : 0 < radialFitQualitativeConstant (m + 2) Cχ := by
    have hN : 0 < radialNormalizationRestrictionConstant (m + 2) :=
      zero_lt_one.trans_le (radialNormalizationRestrictionConstant_ge_one (m + 2))
    unfold radialFitQualitativeConstant
    positivity
  obtain ⟨hsigma, hsum, hbudget⟩ := actual_two_center_projection_budget d1.source d2.source
    hκ (mul_pos hqual hzeta) d1.summable d2.summable
  refine ⟨hsum, ?_, ?_⟩
  · have hb : 2 * (radialFitQualitativeConstant (m + 2) Cχ * zeta) +
        (∑' k, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source k) +
        (∑' k, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source k) ≤
        2 * (radialFitQualitativeConstant (m + 2) Cχ * zeta) + 2 * eta := by
      linarith [d1.budget, d2.budget]
    have hh := hbudget.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64))
    convert hh using 1
    ring
  · exact hbound ha hzeta.le hzetaeps hzetadelta heta hetatau hBG e hfirst hcenter d1 d2 i
      hroom hcurvMeasure _ (hsigma i).1 (hsigma i).2.1 (hsigma i).2.2

end RegularPointCoordinates

end

end OAI
