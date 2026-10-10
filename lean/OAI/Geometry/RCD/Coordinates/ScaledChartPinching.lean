import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Harmonic.ScaledPinchingField
import OAI.Geometry.RCD.Coordinates.RegularInitialChart

namespace OAI

/-! # The initial open chart and full directional pinching for the same map -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The precisely stated published inputs construct one actual open chart
and an arbitrarily small summable pinching field for its coordinate map. -/
theorem exists_scaled_chart_pinching_field {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker) :
    letI : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ c : RegularHeatConstants (m + 2), ∃ B J C A Cχ Cpin : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 0 < Cpin ∧
      ∀ budget : ℝ, 0 < budget → ∃ zeta eta : ℝ, 0 < zeta ∧ 0 < eta ∧
      ∃ e : RegularProjectionEnvironment hX p hk a |K| B J C A Cχ 1 zeta eta,
        c.Matches e.heat ∧ zeta ≤ budget ∧ Nonempty (RegularPinchingField e.heat Cpin budget) ∧
        let Ω := ball p (e.heat.radius / 1024)
        IsOpen (Set.range (fun x : Ω => e.heat.values x)) ∧
          ∃ chart : Ω ≃ₜ Set.range (fun x : Ω => e.heat.values x),
            ∀ x, (chart x).val = e.heat.values x := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨c, B, J, C, A, Cχ, Cpin, hB, hJ, hC, hA, hCχ, hCpin, hconstruct⟩ :=
    exists_scaled_pinching_field m hX ha hcompact hregular hvolume hmeasured hBG hdensity
      hdistance hsobolev hpoisson haction hproduct hpoincare hpoissonCompact hhessian hmean
      hinitial htrans hsplit hrigidity hbochner hcutoff hharmonic hgradient heuclidean
      hmetricmeasure hk hg hdiff
  refine ⟨c, B, J, C, A, Cχ, Cpin, hB, hJ, hC, hA, hCχ, hCpin, ?_⟩
  intro budget hbudget
  let D := (((m + 2 : ℕ) : ℝ) ^ 2) * ((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ (m + 2))⁻¹)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let small := min budget (min (1 / 2048) ((3 / 4) / (D + 1)))
  have hsmall : 0 < small := lt_min hbudget (lt_min (by norm_num) (by positivity))
  obtain ⟨zeta, eta, hzeta, heta, e, hmatch, hzetaBudget, ⟨f⟩⟩ := hconstruct small hsmall
  have hzetaSmall : zeta ≤ 1 / 2048 :=
    hzetaBudget.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzetaGram : D * zeta ≤ 3 / 4 := by
    have hh := hzetaBudget.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hb := (le_div_iff₀ (by positivity : 0 < D + 1)).mp hh
    nlinarith
  refine ⟨zeta, eta, hzeta, heta, e, hmatch, hzetaBudget.trans (min_le_left _ _), ⟨{ f with total := ?_ }⟩, ?_⟩
  · intro q
    exact (f.total q).trans (min_le_left _ _)
  · apply regular_initial_chart hX e hzeta.le hzetaSmall
    simpa only [D, mul_assoc] using hzetaGram

end RegularPointCoordinates

end

end OAI
