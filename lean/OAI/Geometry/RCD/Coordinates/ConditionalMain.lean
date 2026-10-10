import OAI.Geometry.RCD.Coordinates.ActualRegularFlatness
import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.ScaledChartPinching
import OAI.Geometry.RCD.Coordinates.ScaledPatchIteration
import OAI.Geometry.RCD.Coordinates.RegularLimitChart
import OAI.Geometry.RCD.Coordinates.PatchBudget
import OAI.Geometry.RCD.Coordinates.PatchGeometryMonotone

namespace OAI

/-! # Bi-Lipschitz coordinates from local geometric and analytic estimates

The neighborhood and chart are constructed from harmonic approximation,
heat-kernel bounds, and summable directional pinching.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds_actual {K : ℝ} (m : ℕ)
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
    (hsplit : LocalFlatSplittingInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    (hGevrey : EuclideanGevreyCutoffInput (m + 2)) :
    HasOpenBilipschitzChart (m + 2) p := by
  classical
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨c, B, J, C, A, Cχ, Cpin, hB, hJ, hC, hA, hCχ, hCpin, hconstruct⟩ :=
    exists_scaled_pinching_field m hX ha hcompact hregular hvolume hmeasured hBG hdensity
      hdistance hsobolev hpoisson haction hproduct hpoincare hpoissonCompact hhessian hmean
      hinitial htrans hsplit (hX.uniformRegularFlatnessInput (by omega)) hbochner hcutoff hharmonic hgradient heuclidean
      hmetricmeasure hk hg hdiff
  obtain ⟨psi⟩ := hGevrey
  obtain ⟨Theta, tau, hTheta, htau, hpatch⟩ := exists_scaled_patch_iteration hX hk c
  obtain ⟨epsilon, hepsilon, hepsilon1, hchart⟩ :=
    regular_iteration_limit_chart hX psi hCpin.le hTheta
  let epsilon₀ := min epsilon tau
  have hepsilon₀ : 0 < epsilon₀ := lt_min hepsilon htau
  have hepsilon₀epsilon : epsilon₀ ≤ epsilon := min_le_left _ _
  have hepsilon₀tau : epsilon₀ ≤ tau := min_le_right _ _
  let n := m + 2
  let N := patchOverlapBound n (1 / 2) 2 3
  let g4 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹)
  let g2 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹)
  let g8 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹)
  let g64 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹)
  let Lpair := iterationPairMultiplier Theta
    (patchJetBase N (Real.sqrt (3 * Cpin)) (psi.constant * 536870912)) 64
  let Dmass := 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ
  have hg4 : 0 ≤ g4 := by dsimp only [g4]; positivity
  have hg2 : 0 ≤ g2 := by dsimp only [g2]; positivity
  have hg8 : 0 ≤ g8 := by dsimp only [g8]; positivity
  have hg64 : 0 ≤ g64 := by dsimp only [g64]; positivity
  have hLpair : 0 ≤ Lpair := by
    have hTheta0 : 0 < Theta := lt_of_lt_of_le zero_lt_one hTheta
    have hL : 1 ≤ psi.constant * 536870912 := by nlinarith only [psi.constant_ge_one]
    have hJet := patchJetBase_ge_one (N := (N : ℝ)) (L := Real.sqrt (3 * Cpin)) hL
    dsimp only [Lpair, iterationPairMultiplier, iterationChartRatio]
    positivity
  have hDmass : 0 ≤ Dmass := by
    have homega := euclideanUnitVolume_pos n
    have hCχ0 : 0 ≤ Cχ := zero_le_one.trans hCχ
    dsimp only [Dmass, pinchingMassUnitFactor, regularSmallMassCoefficient]
    positivity
  let P := g4 + g2 + g8 + g64 + Lpair + 2 * Dmass + (N : ℝ) * (2 * Dmass)
  have hND : 0 ≤ (N : ℝ) * (2 * Dmass) := by positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  obtain ⟨budget, hbudget, hbudgetE, hbudgetSmall, hproducts⟩ :=
    exists_uniform_patch_budget hP hepsilon₀
  obtain ⟨zeta, eta, hzeta, heta, e, hmatch, hzetaBudget, ⟨f⟩⟩ := hconstruct budget hbudget
  have hbounded (t : ℝ) (ht : 0 ≤ t) (htP : t ≤ P) :
      t * zeta ≤ min epsilon₀ (1 / 8192) :=
    (mul_le_mul_of_nonneg_left hzetaBudget ht).trans (hproducts t ht htP)
  have hsmallTarget : min epsilon₀ (1 / 8192) ≤ (1 / 4 : ℝ) :=
    (min_le_right _ _).trans (by norm_num)
  have hgram : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4 := by
    have h := hbounded g4 hg4 (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    simpa only [g4, mul_assoc] using h.trans (hsmallTarget.trans (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4))
  have hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4 := by
    have h := hbounded g2 hg2 (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    simpa only [g2, mul_assoc] using h.trans hsmallTarget
  have hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2 := by
    have h := hbounded g8 hg8 (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    simpa only [g8, mul_assoc] using h.trans (hsmallTarget.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
  have hwide : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4 := by
    have h := hbounded g64 hg64 (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    simpa only [g64, mul_assoc] using h.trans hsmallTarget
  have hzetaSmall : zeta ≤ 1 / 2048 :=
    hzetaBudget.trans (hbudgetSmall.trans (by norm_num))
  have hzeta64 : zeta ≤ 1 / 64 := hzetaSmall.trans (by norm_num)
  have hzetaL : zeta * Lpair ≤ 2097152 := by
    have h := hbounded Lpair hLpair (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    simpa only [mul_comm] using h.trans (hsmallTarget.trans (by norm_num : (1 / 4 : ℝ) ≤ 2097152))
  have hcurv : |K| * e.heat.radius ^ 2 ≤ zeta := hmatch.2.2.2.2.2.2.2
  have hlocal (i : ℕ) : zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2 ≤ 2 * zeta := by
    have hr : e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15) ≤ e.heat.radius :=
      div_le_self e.heat.radius_pos.le (one_le_pow₀ (by norm_num))
    have hs : 0 ≤ e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15) :=
      div_nonneg e.heat.radius_pos.le (by positivity)
    have hsq := (sq_le_sq₀ hs e.heat.radius_pos.le).mpr hr
    have hh := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    linarith only [hh, hcurv]
  have hcoef (i : ℕ) : Dmass *
      (zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2) ≤ epsilon₀ := by
    have h := hbounded (2 * Dmass) (by positivity) (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    have hh := mul_le_mul_of_nonneg_left (hlocal i) hDmass
    nlinarith only [hh, h.trans (min_le_left _ _)]
  have hmass (i : ℕ) : (N : ℝ) * (Dmass *
      (zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2)) ≤ epsilon₀ := by
    have h := hbounded ((N : ℝ) * (2 * Dmass)) (by positivity) (by dsimp only [P]; linarith only [hg4, hg2, hg8, hg64, hLpair, hDmass, hND])
    have hh := mul_le_mul_of_nonneg_left (hlocal i)
      (show 0 ≤ (N : ℝ) * Dmass by positivity)
    nlinarith only [hh, h.trans (min_le_left _ _)]
  obtain ⟨hΩ, chart, hchartValues⟩ := regular_working_chart hX e hzeta.le hzetaSmall hgram
  obtain ⟨inverse, hinverse⟩ := exists_working_chart_inverse e.heat chart hchartValues
  let selection := regularPatchSelection hX e hzeta64 psi f hCpin.le
  obtain ⟨g, hg⟩ := hpatch e hmatch hzeta.le hzeta64 (zero_le_one.trans hCχ) (by norm_num)
    hsmall hnear hwide psi f selection epsilon₀ hepsilon₀.le hepsilon₀tau hbudgetE hcoef hmass
    _ inverse hinverse
  exact hchart e hzeta.le hzetaSmall hgram hnear hzetaL _ hΩ chart hchartValues
    inverse hinverse (g.monoError hepsilon₀epsilon) hg

theorem regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds {K : ℝ} (m : ℕ)
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
    (hsplit : LocalFlatSplittingInput hX) (_hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    (hGevrey : EuclideanGevreyCutoffInput (m + 2)) :
    HasOpenBilipschitzChart (m + 2) p := by
  exact regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds_actual m hX ha
    hcompact hregular hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson
    haction hproduct hpoincare hpoissonCompact hhessian hmean hinitial htrans hsplit
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

theorem regular_point_has_open_bilipschitz_chart_conditional {K : ℝ} (m : ℕ)
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
    (hsplit : LocalAlmostSplittingInput hX) (hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasGaussianHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    (hGevrey : EuclideanGevreyCutoffInput (m + 2)) :
    HasOpenBilipschitzChart (m + 2) p  := by
  exact regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit.flatSplittingInput hrigidity hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg.toCoordinate hdiff hGevrey

theorem regular_point_has_open_bilipschitz_chart_of_coordinate_heat_bounds {K : ℝ} (m : ℕ)
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
    (hsplit : LocalAlmostSplittingInput hX) (hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    (hGevrey : EuclideanGevreyCutoffInput (m + 2)) :
    HasOpenBilipschitzChart (m + 2) p := by
  exact regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit.flatSplittingInput hrigidity
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

/-- Regular points in dimension at least two admit charts with two-sided
ambient-distance bounds under the stated local estimates. -/
theorem every_regular_point_has_bilipschitz_coordinates_of_flat_coordinate_heat_bounds {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff n X) n p
      (euclideanUnitVolume n))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff n X) n p)
    (hBG : BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff n X)
      (comparisonModelVolume (n - 1) a) y (euclideanUnitVolume n))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff n X) ker)
    (hGevrey : EuclideanGevreyCutoffInput n) :
    HasOpenBilipschitzChart n p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit hrigidity hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

theorem every_regular_point_has_bilipschitz_coordinates_of_flat_coordinate_heat_bounds_actual {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff n X) n p
      (euclideanUnitVolume n))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff n X) n p)
    (hBG : BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff n X)
      (comparisonModelVolume (n - 1) a) y (euclideanUnitVolume n))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff n X) ker)
    (hGevrey : EuclideanGevreyCutoffInput n) :
    HasOpenBilipschitzChart n p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact regular_point_has_open_bilipschitz_chart_of_flat_coordinate_heat_bounds_actual m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

theorem every_regular_point_has_bilipschitz_coordinates_of_coordinate_heat_bounds {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff n X) n p
      (euclideanUnitVolume n))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff n X) n p)
    (hBG : BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff n X)
      (comparisonModelVolume (n - 1) a) y (euclideanUnitVolume n))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalAlmostSplittingInput hX) (hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff n X) ker)
    (hGevrey : EuclideanGevreyCutoffInput n) :
    HasOpenBilipschitzChart n p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact regular_point_has_open_bilipschitz_chart_of_coordinate_heat_bounds m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit hrigidity hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

/-- Regular points in dimension at least two admit charts with two-sided
ambient-distance bounds under the stated local estimates. -/
theorem every_regular_point_has_bilipschitz_coordinates_conditional {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff n X) n p
      (euclideanUnitVolume n))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff n X) n p)
    (hBG : BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff n X)
      (comparisonModelVolume (n - 1) a) y (euclideanUnitVolume n))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalAlmostSplittingInput hX) (hrigidity : LocalVolumeRigidityInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasGaussianHeatBounds (hausdorff n X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff n X) ker)
    (hGevrey : EuclideanGevreyCutoffInput n) :
    HasOpenBilipschitzChart n p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact regular_point_has_open_bilipschitz_chart_conditional m hX ha hcompact hregular
    hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
    hpoissonCompact hhessian hmean hinitial htrans hsplit hrigidity hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff hGevrey

end RegularPointCoordinates

end

end OAI
