import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularNeighborhoodBilinear

namespace OAI

/-! # The constructed common harmonic and heat data -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A record of the already constructed heat and harmonic objects. No
chart, directional pinching, or metric-iteration conclusion is a field. -/
structure RegularBilinearData {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    [(hausdorff n X).Regular]
    (p : X) {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (enlargement zeta : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1
  lambda : ℝ
  lambda_pos : 0 < lambda
  coordinates : Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  values : X → Euclidean n
  initialError : ℝ
  initialError_pos : 0 < initialError
  initialError_le_one : initialError ≤ 1
  mass : PositiveBilinearMeasure X (Euclidean n)
  energyBound : ℝ≥0
  energyBound_sq : (energyBound : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2
  energy : ∀ z, LocalHarmonicEnergy (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates) mass |K| p
    (4 * radius) energyBound z
  cutoffConstant : ℝ
  cutoff : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * radius / 8) cutoffConstant
  shift : ℕ
  degree : ℕ
  degree_ge_three : 3 ≤ degree
  envelopeConstant : ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  comparisonConstant : ℝ
  envelopeConstant_pos : 0 < envelopeConstant
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  comparisonConstant_pos : 0 < comparisonConstant
  splitting : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (32 * radius)
    initialError coordinates values
  rootLower : ∀ q ∈ ball p (radius / 32), ∀ v,
    ‖v‖ ^ 2 ≤ 2 * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates)
      (ball q radius) measurableSet_ball v⟫_ℝ
  heatMeanComparison : ∀ q ∈ ball p (radius / 32), ∀ i, shift ≤ i → ∀ v,
    let Q := dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates) cutoff q radius_pos lambda_pos
    (1 - 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates)
      (ball q (radius / 2 ^ i)) measurableSet_ball v⟫_ℝ ≤ ⟪v, Q i v⟫_ℝ ∧
    ⟪v, Q i v⟫_ℝ ≤ (1 + 1 / 64 : ℝ) * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates)
      (ball q (radius / 2 ^ i)) measurableSet_ball v⟫_ℝ
  heatOrder : ∀ q ∈ ball p (radius / 32), ∀ i, shift ≤ i → ∀ v,
    let Q := dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates) cutoff q radius_pos lambda_pos
    ⟪v, Q (i + 1) v⟫_ℝ ≤ ⟪v, Q i v⟫_ℝ ∧
    ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ
  localData : ∀ q ∈ ball p (radius / 32),
    let Q := dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates) cutoff q radius_pos lambda_pos
    (∀ (xi : Euclidean n) (k : ℕ),
      let h := ⟪xi, (Q (shift + k)).symm xi⟫_ℝ
      let currentMass := ∑ i ∈ Finset.range k,
        ⟪(Q (shift + i)).symm xi, dyadicBochnerMass mass n q radius (shift + i) ((Q (shift + i)).symm xi)⟫_ℝ
      (∑ i ∈ Finset.range k,
        ⟪(Q (shift + i)).symm xi, dyadicBochnerEnvelope mass n q radius (shift + i) ((Q (shift + i)).symm xi)⟫_ℝ) ≤
          envelopeConstant * h ∧
      ‖xi‖ ^ 2 + currentMass ≤ lowerConstant * h ∧
      h ≤ upperConstant * (‖xi‖ ^ 2 + currentMass)) ∧
    (∀ i, shift ≤ i → ∀ y, dist q y ≤ enlargement * (radius / 2 ^ i) → ∀ b w : Euclidean n,
      ⟪b, (sobolevMeanGram (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates)
        (ball y (radius / 2 ^ i)) measurableSet_ball - (Q i : Euclidean n →L[ℝ] Euclidean n)) w⟫_ℝ ^ 2 ≤
          comparisonConstant * ⟪b, Q i b⟫_ℝ * ⟪w, dyadicBochnerEnvelope mass n q radius i w⟫_ℝ) ∧
    (∀ r : ℝ, 0 < r → r ≤ radius / 16 →
      HasNormalizedAffineImprovement hX coordinates q r ((1 / 2 : ℝ) ^ degree)) ∧
    ∃ F : ℕ → Euclidean n ≃L[ℝ] Euclidean n,
      (∀ i, IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates)
        (ball q (radius / 2 ^ i)) measurableSet_ball (F i)) ∧
      (∀ i, FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (radius / 2 ^ i) zeta
        (transformedColumn (hausdorff n X) hX.quadratic coordinates (F i))
        (fun x => (F i : Euclidean n →L[ℝ] Euclidean n).adjoint (values x))) ∧
      ∀ i, IsPointedApproximation q 0 ((radius / 2 ^ i) / 128) 4 zeta
        (fun x => ((radius / 2 ^ i) / 128)⁻¹ •
          ((F i : Euclidean n →L[ℝ] Euclidean n).adjoint (values x) -
            (F i : Euclidean n →L[ℝ] Euclidean n).adjoint (values q)))

/-- This bundles the proved capped construction, retaining the same
actual coordinate functions, Gram operators and positive measure. -/
theorem exists_regular_bilinear_data_uniform_degree {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    :
    ∃ degree : ℕ, 3 ≤ degree ∧ ∀ {radiusCap enlargement zeta : ℝ},
    0 < radiusCap → 0 ≤ enlargement → 0 < zeta →
    ∃ d : RegularBilinearData hX p hk enlargement zeta,
      d.radius ≤ radiusCap ∧ d.degree = degree := by
  obtain ⟨degree, hdegree, hconstruct⟩ := regular_neighborhood_bilinear_heat_with_energy
    m hX ha hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  refine ⟨degree, hdegree, ?_⟩
  intro radiusCap enlargement zeta hcap henlargement hzeta
  obtain ⟨R, hR, hRcap, lambda, hlambda, u, V, e, M, Ccut, chi, J, A, B, D, H, L,
    hR1, hA, hB, hD, hH, he, he1, hu, hL, henergy, hlocal⟩ :=
    hconstruct hcap henlargement hzeta
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
    localData := fun q hq => (hlocal q hq).2 }, hRcap, rfl⟩

/-- Forget the fixed degree when only a single neighborhood is needed. -/
theorem exists_regular_bilinear_data {K : ℝ} (m : ℕ)
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
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker)
    {radiusCap enlargement zeta : ℝ} (hcap : 0 < radiusCap)
    (henlargement : 0 ≤ enlargement) (hzeta : 0 < zeta) :
    ∃ d : RegularBilinearData hX p hk enlargement zeta, d.radius ≤ radiusCap := by
  obtain ⟨_, _, hconstruct⟩ := exists_regular_bilinear_data_uniform_degree m hX ha hcompact
    hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity hbochner hcutoff
    hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  obtain ⟨d, hcap, _⟩ := hconstruct hcap henlargement hzeta
  exact ⟨d, hcap⟩

end RegularPointCoordinates

end

end OAI
