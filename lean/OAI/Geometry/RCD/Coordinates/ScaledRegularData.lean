import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularBilinearData
import OAI.Geometry.RCD.Coordinates.ScaledRegularBilinear

namespace OAI

/-! # Fixed heat constants for arbitrarily small regular neighborhoods -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The constants retained before choosing the pinching tolerance. -/
structure RegularHeatConstants (n : ℕ) where
  degree : ℕ
  degree_ge_three : 3 ≤ degree
  shift : ℕ
  envelope : ℝ
  lower : ℝ
  upper : ℝ
  comparison : ℝ
  envelope_pos : 0 < envelope
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  comparison_pos : 0 < comparison

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact heat parameters, dimensionless regularizer, and curvature smallness
for the normalized harmonic data. -/
def RegularHeatConstants.Matches {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [(hausdorff n X).Regular] {p : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (c : RegularHeatConstants n)
    (d : RegularBilinearData hX p hk enlargement zeta) : Prop :=
  d.degree = c.degree ∧ d.shift = c.shift ∧ d.envelopeConstant = c.envelope ∧
  d.lowerConstant = c.lower ∧ d.upperConstant = c.upper ∧
  d.comparisonConstant = c.comparison ∧ d.lambda * d.radius ^ 2 = 8 * (n : ℝ) ^ 2 + 2 ∧
  |K| * d.radius ^ 2 ≤ zeta

/-- The published inputs build one such fixed set of constants and then
supply the actual harmonic data for any positive tolerance and radius cap. -/
theorem exists_scaled_regular_bilinear_data {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    :
    ∀ enlargement : ℝ, 0 ≤ enlargement → ∃ c : RegularHeatConstants (m + 2),
      ∀ {radiusCap zeta : ℝ}, 0 < radiusCap → 0 < zeta →
      ∃ d : RegularBilinearData hX p hk enlargement zeta,
        d.radius ≤ radiusCap ∧ c.Matches d := by
  obtain ⟨degree, hdegree, hconstruct⟩ := scaled_regular_neighborhood_bilinear_heat
    m hX ha hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hhessian hproduct hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  intro enlargement henlargement
  obtain ⟨J, A, B, D, H, hA, hB, hD, hH, hbuild⟩ := hconstruct enlargement henlargement
  let c : RegularHeatConstants (m + 2) := {
    degree := degree, degree_ge_three := hdegree, shift := J
    envelope := A, lower := B, upper := D, comparison := H
    envelope_pos := hA, lower_pos := hB, upper_pos := hD, comparison_pos := hH }
  refine ⟨c, ?_⟩
  intro radiusCap zeta hcap hzeta
  obtain ⟨R, hR, hRcap, lambda, hlambda, u, V, e, M, Ccut, chi, L,
    hR1, hlambdaScale, hcurv, he, he1, hu, hL, henergy, hlocal⟩ := hbuild hcap hzeta
  exact ⟨{
    radius := R, radius_pos := hR, radius_le_one := hR1, lambda := lambda, lambda_pos := hlambda
    coordinates := u, values := V, initialError := e, initialError_pos := he, initialError_le_one := he1
    mass := M, energyBound := L, energyBound_sq := hL
    energy := fun z => Classical.choice (henergy z)
    cutoffConstant := Ccut, cutoff := chi, shift := J, degree := degree, degree_ge_three := hdegree
    envelopeConstant := A, lowerConstant := B, upperConstant := D, comparisonConstant := H
    envelopeConstant_pos := hA, lowerConstant_pos := hB, upperConstant_pos := hD, comparisonConstant_pos := hH
    splitting := hu
    rootLower := fun q hq => (hlocal q hq).1.1
    heatMeanComparison := fun q hq => (hlocal q hq).1.2.1
    heatOrder := fun q hq => (hlocal q hq).1.2.2
    localData := fun q hq => (hlocal q hq).2 }, hRcap, rfl, rfl, rfl, rfl, rfl, rfl, hlambdaScale, hcurv⟩

end RegularPointCoordinates

end

end OAI
