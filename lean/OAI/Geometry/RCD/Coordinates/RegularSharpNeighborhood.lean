import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularRadialEnvironment
import OAI.Geometry.RCD.Coordinates.RegularPairProjection
import OAI.Geometry.RCD.Sobolev.SharpNeighborhoodParameters

namespace OAI

/-! # A regular neighborhood carrying the actual sharp projection estimate -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- All sources and coordinates are constructed from the cited inputs.
The positive source has any requested square budget and controls the actual
normalized two-center projection at every admissible center and scale. -/
theorem exists_regular_sharp_neighborhood {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a κ : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
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
    ∃ B J C A Cχ Cg D Ca P : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧ 0 < P ∧
      ∀ budget : ℝ, 0 < budget → ∃ zeta eta : ℝ, 0 < zeta ∧ 0 < eta ∧
      ∃ e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ 1 zeta eta,
      128 * (radialFitQualitativeConstant (m + 2) Cχ * zeta + eta) ≤ budget ∧
      ∃ data : ∀ q, q ∈ ball p (e.heat.radius / 32) →
        RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q,
      ∀ first (hfirst : first ∈ ball p (e.heat.radius / 32))
        center (hcenter : center ∈ ball p (e.heat.radius / 32)),
        let d1 := data first hfirst
        let d2 := data center hcenter
        let sigma := twoCenterProjectionSource
          (radialFitQualitativeConstant (m + 2) Cχ * zeta)
          (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source)
          (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source)
        Summable (fun i => sigma i ^ 2) ∧ (∑' i, sigma i ^ 2) ≤ budget ∧
        ∀ i, dist center first ≤ distanceSourceRadius e.heat.radius i / 4 →
          regularPairProjectionSize hX e d1 d2 i ≤ P * sigma i := by
  classical
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨B, J, C, A, Cχ, Cg, D, Ca, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, hconstruct⟩ :=
    exists_regular_radial_environment m hX ha hκ hK hcompact hregular hvolume hmeasured hBG
      hdensity hdistance hsobolev hpoisson hhessian hmean hinitial htrans hsplit hrigidity
      hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  let G := ((m + 2 : ℕ) : ℝ) ^ 2 * ((5 / 3 : ℝ) * (16384 : ℝ) ^ (m + 2))
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  let epsilon := 1 / (2 * (G + 1))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 *
      (((5 / 3 : ℝ) * (16384 : ℝ) ^ (m + 2)) * epsilon) ≤ 1 / 2 := by
    have hh : epsilon * (2 * (G + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp (le_refl epsilon)
    dsimp only [G] at hh
    nlinarith
  obtain ⟨P, tau, hP, htau, hsharp⟩ := regular_sharp_projection_actual_sources m hX
    hgradient hmean hmetricmeasure haction hproduct hpoincare hpoissonCompact
    hκ hK hB.le hJ.le (zero_le_one.trans hCχ) hA.le hepsilon.le hsmall
  obtain ⟨delta, hdelta, hbound⟩ := hsharp (tau / 2) (by positivity) (by linarith)
  refine ⟨B, J, C, A, Cχ, Cg, D, Ca, P, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, hP, ?_⟩
  intro budget hbudget
  let c := radialNormalizationRestrictionConstant (m + 2)
  let g := ((m + 2 : ℕ) : ℝ) ^ 2 * normalizationVolumeRatio (m + 1)
  let a₀ := radialFitQualitativeConstant (m + 2) Cχ
  have hc : 0 ≤ c := zero_le_one.trans (radialNormalizationRestrictionConstant_ge_one (m + 2))
  have hg : 0 ≤ g := by dsimp only [g, normalizationVolumeRatio]; positivity
  have ha₀ : 0 ≤ a₀ := radialFitQualitativeConstant_nonneg _ (zero_le_one.trans hCχ)
  obtain ⟨zeta, eta, cap, hzeta, heta, hcap, hzeps, hzdelta, hzc, hzg, hetatau, hbudgetSmall, hcapK⟩ :=
    sharp_neighborhood_parameters (K := K) hepsilon hdelta htau hc hg ha₀ hbudget
  have hnormalize : ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * zeta) ≤ 1 / 64 := by
    simpa only [g, mul_assoc] using hzg
  obtain ⟨e, hecap, hdata⟩ := hconstruct 1 zeta eta cap (by norm_num) hzeta hzc hnormalize heta hcap
  let data := fun q hq => Classical.choice (hdata q hq)
  refine ⟨zeta, eta, hzeta, heta, e, hbudgetSmall, data, ?_⟩
  intro first hfirst center hcenter
  let d1 := data first hfirst
  let d2 := data center hcenter
  have hqual : 0 < a₀ := by
    have hN : 0 < c := zero_lt_one.trans_le (radialNormalizationRestrictionConstant_ge_one (m + 2))
    dsimp only [a₀, radialFitQualitativeConstant]
    change 0 < ((m + 2 : ℕ) : ℝ) * (1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1)) * c * _
    positivity
  obtain ⟨_hsource, hsum, hsourceBudget⟩ := actual_two_center_projection_budget d1.source d2.source
    hκ (mul_pos hqual hzeta) d1.summable d2.summable
  refine ⟨hsum, ?_, ?_⟩
  · have hb : 2 * (a₀ * zeta) +
        (∑' i, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source i) +
        (∑' i, normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source i) ≤
        2 * (a₀ * zeta) + 2 * eta := by linarith [d1.budget, d2.budget]
    have hh := hsourceBudget.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64))
    exact hh.trans (by nlinarith [hbudgetSmall])
  · intro i hroom
    have hs : 0 < distanceSourceRadius e.heat.radius i := distanceSourceRadius_pos e.heat.radius_pos i
    have hsR : distanceSourceRadius e.heat.radius i ≤ e.heat.radius := by
      have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
      linarith
    have hsCap := hsR.trans hecap
    have hsq : distanceSourceRadius e.heat.radius i ^ 2 ≤ cap ^ 2 := by nlinarith
    have habs := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (distanceSourceRadius e.heat.radius i))
    have hcurv : -delta / 32 ≤ K * distanceSourceRadius e.heat.radius i ^ 2 := by nlinarith
    have hh := hbound ha hzeta hzeps hzdelta heta.le hetatau hBG e hfirst hcenter d1 d2 i hroom hcurv
    exact hh.2.2

end RegularPointCoordinates

end

end OAI
