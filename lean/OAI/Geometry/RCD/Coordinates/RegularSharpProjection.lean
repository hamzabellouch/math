import OAI.Geometry.RCD.Coordinates.RegularProjectionConfiguration
import OAI.Geometry.RCD.Harmonic.ActualProjectionThreshold

namespace OAI

/-! # Sharp projection for the constructed regular-neighborhood data -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual two-center projection has a uniform sharp bound on the
same regular neighborhood, under the explicitly separated metric and
source tolerances. -/
theorem regular_sharp_projection_constants {K : ℝ} (m : ℕ)
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
      0 ≤ a → 0 ≤ zeta → zeta ≤ epsilon → zeta ≤ delta → 0 ≤ eta → eta ≤ tau →
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
      ∀ source : ℝ, 0 < source →
      normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source i +
        normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source i ≤ source ^ 2 →
      pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * zeta)
        (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source) i ≤ source ^ 2 →
          ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball center ((1 / 2048) * s))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (affineResidual (hausdorff (m + 2) X) hX.quadratic
              (radiusScaledColumns (hausdorff (m + 2) X) hX.quadratic s uc)
              (ball center ((1 / 2048) * s)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
              (SobolevSpace.restrictLp (hausdorff (m + 2) X) hX.quadratic
                (ball center ((1 / 2048) * s))
                ((s ^ 2)⁻¹ • (d2.replacement.replacement i - d1.replacement.replacement i))))‖ ≤ P * source := by
  obtain ⟨H, hH, hconfig⟩ := regular_projection_configuration_constants m hX hgradient hmean
    hmeasured hκ hK hB hCχ hepsilon hsmall
  have hD : 0 ≤ ((m + 2 : ℕ) : ℝ) * Real.sqrt (projectionRowConstant (m + 2) B D) := by positivity
  obtain ⟨P, tau, hP, htau, hbound⟩ := actual_sharp_projection_small_data
    (hX := hX) (κ := κ) (B := B) (J := J) (C := C) (A := A) (Cχ := Cχ)
    (epsilon := epsilon) (H := H) (D := ((m + 2 : ℕ) : ℝ) * Real.sqrt (projectionRowConstant (m + 2) B D))
    (L := 1) (M := 1) hhessian hproduct hpoincare hgradient hcompact (by omega)
    hκ hK hB hJ hCχ hA hepsilon hH hD zero_le_one
  refine ⟨P, tau, hP, htau, ?_⟩
  intro error herror herrortau
  obtain ⟨delta, hdelta, hconstruct⟩ := hconfig error herror
  refine ⟨delta, hdelta, ?_⟩
  intro base first center a enlargement zeta eta Cg Ca ker hk ha hzeta hzetaeps hzetadelta heta hetatau hBG
    e hfirst hcenter d1 d2 i s uc hroom hcurvMeasure source hsource hpair henv
  obtain ⟨d, _hradius, hsourceEq, htotal, herr, _huc, _hcenter, hproj⟩ :=
    hconstruct ha hzeta hzetaeps hzetadelta heta hBG e hfirst hcenter d1 d2 i
      hroom hcurvMeasure source hsource hpair henv
  have hh := hbound d (by rwa [herr]) (by rwa [htotal])
  simpa only [hproj, hsourceEq] using hh

end RegularPointCoordinates

end

end OAI
