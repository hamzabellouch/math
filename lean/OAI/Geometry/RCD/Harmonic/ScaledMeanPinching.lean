import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.ScaledSharpNeighborhood
import OAI.Geometry.RCD.Coordinates.RegularSharpNeighborhood
import OAI.Geometry.RCD.Coordinates.RegularMassMatrices

namespace OAI

/-! # The regular neighborhood with actual inverse mean-Gram mass matrices -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The precise published inputs construct one common harmonic/heat family
with an arbitrarily small summable source and the full directional mass
estimate for every nearby pair. No pinching hypothesis is assumed. -/
theorem exists_scaled_mean_pinching_neighborhood {K : ℝ} (m : ℕ)
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
    ∃ c : RegularHeatConstants (m + 2), ∃ B J C A Cχ Cg D Ca Cpin : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧ 0 < Cpin ∧
      ∀ budget : ℝ, 0 < budget → ∃ zeta eta : ℝ, 0 < zeta ∧ 0 < eta ∧
      ∃ e : RegularProjectionEnvironment hX p hk a |K| B J C A Cχ 1 zeta eta,
      c.Matches e.heat ∧
      ∃ data : ∀ q, q ∈ ball p (e.heat.radius / 32) →
        RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca q,
      ∀ first (hfirst : first ∈ ball p (e.heat.radius / 32))
        center (hcenter : center ∈ ball p (e.heat.radius / 32)),
        let d1 := data first hfirst
        let d2 := data center hcenter
        let sigma := twoCenterProjectionSource (radialFitQualitativeConstant (m + 2) Cχ * zeta)
          (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source)
          (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source)
        Summable (fun i => sigma i ^ 2) ∧ (∑' i, sigma i ^ 2) ≤ budget ∧
        ∀ i, let s := distanceSourceRadius e.heat.radius i
          let _U := (centeredSobolevMap (hausdorff (m + 2) X) hX.quadratic e.heat.coordinates
            e.one.sobolev (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
          let _delta := (d2.frame i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint
            (e.heat.values first - e.heat.values center)
          dist first center ≤ s / 512 →
          let D := e.heat.pinchingMassMatrix center hcenter i
          D.IsPositive ∧
            ⟪e.heat.values first - e.heat.values center,
              D (e.heat.values first - e.heat.values center)⟫_ℝ ≤
                Cpin * s ^ 2 * sigma i ^ 2 := by
  classical
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨c, B, J, C, A, Cχ, Cg, D, Ca, P, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, hP, hconstruct⟩ :=
    exists_scaled_sharp_neighborhood m hX ha (abs_nonneg K) (neg_abs_le K) hcompact hregular
      hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare
      hpoissonCompact hhessian hmean hinitial htrans hsplit hrigidity hbochner hcutoff hharmonic
      hgradient heuclidean hmetricmeasure hk hg hdiff
  obtain ⟨Cpin, tau, hCpin, htau, hpinch⟩ := regular_pair_mean_pinching hX hhessian hcutoff haction
    hgradient hmean (by omega) hA.le hB.le hJ.le (zero_le_one.trans hCχ) hP
    (Cg := Cg) (D := D) (Ca := Ca)
  let Q := radialFitQualitativeConstant (m + 2) Cχ
  have hQ : 0 < Q := by
    have hc : 0 < radialNormalizationRestrictionConstant (m + 2) :=
      zero_lt_one.trans_le (radialNormalizationRestrictionConstant_ge_one (m + 2))
    dsimp only [Q, radialFitQualitativeConstant]
    change 0 < ((m + 2 : ℕ) : ℝ) * (1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1)) *
      radialNormalizationRestrictionConstant (m + 2) * _
    positivity
  refine ⟨c, B, J, C, A, Cχ, Cg, D, Ca, Cpin, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, hCpin, ?_⟩
  intro budget hbudget
  let small := min budget (min tau (128 * Q * tau))
  have hsmall : 0 < small := by dsimp only [small]; positivity
  obtain ⟨zeta, eta, hzeta, heta, e, hmatch, hscalar, data, hpairs⟩ := hconstruct small hsmall
  have hzetatau : zeta ≤ tau := by
    have hb : small ≤ 128 * Q * tau := (min_le_right _ _).trans (min_le_right _ _)
    have hh := hscalar.trans hb
    have he := mul_pos (by norm_num : (0 : ℝ) < 128) hQ
    change 128 * (Q * zeta + eta) ≤ _ at hh
    nlinarith only [hh, heta, he]
  refine ⟨zeta, eta, hzeta, heta, e, hmatch, data, ?_⟩
  intro first hfirst center hcenter d1 d2 sigma
  obtain ⟨hsum, hsumBound, hsharp⟩ := hpairs first hfirst center hcenter
  refine ⟨hsum, hsumBound.trans (min_le_left _ _), ?_⟩
  intro i s U delta hroom
  have hsig : sigma i ^ 2 ≤ tau := (hsum.le_tsum i (fun j _ => sq_nonneg (sigma j))).trans
    (hsumBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨R, hR, _hRpos, hDpos, hmass⟩ := hpinch e hfirst hcenter d1 d2 hzeta.le hzetatau
    i hroom hsig (hsharp i (by
      rw [dist_comm]
      have hs := distanceSourceRadius_pos e.heat.radius_pos i
      linarith))
  have hEq := regular_pinching_matrix_identification e.heat center hcenter i R hR
  rw [hEq] at hDpos hmass
  exact ⟨hDpos, hmass⟩

end RegularPointCoordinates

end

end OAI
