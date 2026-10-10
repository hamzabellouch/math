import OAI.Geometry.RCD.Coordinates.RegularUniformDirection
import OAI.Geometry.RCD.Coordinates.RegularPairGradient
import OAI.Geometry.RCD.Coordinates.RegularMassScale

namespace OAI

/-! # Directional pinching for the actual original heat measure -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The sharp projection estimate and the constructed radial fits imply
full directional pinching, with a uniform constant and source tolerance.
The direction is expressed in the actual exact mean-Gram frame on the
mass-test ball. -/
theorem regular_pair_pinching {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hhessian : LocalPoissonHessianInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {A B J Cχ Cg D Ca P : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hP : 0 < P) :
    ∃ Cpin tau : ℝ, 0 < Cpin ∧ 0 < tau ∧
    ∀ {base first center : X} {a C enlargement zeta eta : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
      (e : RegularProjectionEnvironment hX base hk a |K| B J C A Cχ enlargement zeta eta)
      (_hfirst : first ∈ ball base (e.heat.radius / 32))
      (_hcenter : center ∈ ball base (e.heat.radius / 32))
      (d1 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca center),
    0 ≤ zeta → zeta ≤ tau → ∀ i,
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let rho := s / 49152
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let delta := (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let sigma := twoCenterProjectionSource (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d1.source)
      (normalizedPoissonDefect μ hX.quadratic d2.source) i
    dist first center ≤ s / 512 → sigma ^ 2 ≤ tau →
    regularPairProjectionSize hX e d1 d2 i ≤ P * sigma →
    ∃ N : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hX.quadratic U (ball center (3 * rho)) measurableSet_ball N ∧
      ‖N.toContinuousLinearMap‖ ≤ 2 ∧
      let v := d2.frame i (N (N.toContinuousLinearMap.adjoint delta))
      ⟪v, e.heat.mass.massOperator (ball center rho) v⟫_ℝ ≤ Cpin * s ^ n * sigma ^ 2 := by
  obtain ⟨L, t, hL, ht, hdir⟩ := regular_pair_direction_uniform hX haction hgradient hmean hn
    (abs_nonneg K) (neg_abs_le K) hA hB hJ hCχ (Cg := Cg) (D := D) (Ca := Ca)
  obtain ⟨Q, hQ, hgradientPair⟩ := regular_pair_projection_gradient hX hgradient hn hP
  obtain ⟨Ccut, hCcut, hmass⟩ := regular_pair_mass_from_estimates hX hhessian hcutoff hn
  let G := (n : ℝ) ^ 2 * pinchingFrameVolumeRatio n
  have hG : 0 ≤ G := by dsimp only [G, pinchingFrameVolumeRatio]; positivity
  let t2 := 1 / (2 * (G + 1))
  have ht2 : 0 < t2 := by dsimp only [t2]; positivity
  let tau := min t t2
  let Cpin := max (regularPinchingMassConstant n Ccut A B J Cχ Q L) 1
  refine ⟨Cpin, tau, lt_of_lt_of_le zero_lt_one (le_max_right _ _), lt_min ht ht2, ?_⟩
  intro base first center a C enlargement zeta eta ker hk e hfirst hcenter d1 d2 hzeta hzt
    i μ s rho U delta sigma hroom hsigma hsharp
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hz2 : zeta ≤ t2 := hzt.trans (min_le_right _ _)
  have hzbound : zeta * (2 * (G + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hz2
  have hzeta1 : zeta ≤ 1 := by nlinarith [mul_nonneg hG hzeta]
  have hsmall : (n : ℝ) ^ 2 * (pinchingFrameVolumeRatio n * zeta) ≤ 1 / 2 := by
    have hh : G * zeta ≤ 1 / 2 := by nlinarith only [hzbound, hzeta]
    simpa only [G, mul_assoc] using hh
  have hE1 := (radial_fit_pinching_envelope_budget d1.source (abs_nonneg K) hCχ hzeta d1.summable).2.2 i
  have hE2 := (radial_fit_pinching_envelope_budget d2.source (abs_nonneg K) hCχ hzeta d2.summable).2.2 i
  have hsig0 : 0 ≤ sigma := Real.sqrt_nonneg _
  have hsigSq : sigma ^ 2 =
      pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
        (normalizedPoissonDefect μ hX.quadratic d1.source) i +
      pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
        (normalizedPoissonDefect μ hX.quadratic d2.source) i :=
    Real.sq_sqrt (add_nonneg hE1.1 hE2.1)
  obtain ⟨Hpair, hrep, hfit⟩ := hdir e hfirst hcenter d1 d2 hzeta
    (hzt.trans (min_le_left _ _)) i hroom (by rw [← hsigSq]; exact hsigma.trans (min_le_left _ _))
  obtain ⟨c, b, w, hw, _hharm, hgrad⟩ := hgradientPair (abs_nonneg K) e hcenter d1 d2 i
    (by rw [dist_comm]; linarith) sigma hsig0 hsharp
  have hU := centered_transformed_columnMap μ hX.quadratic e.heat.coordinates (d2.frame i)
    e.one.sobolev (e.heat.values center)
  rw [hw, hU] at hgrad
  have hgrad' : ∀ᵐ x ∂μ.restrict (ball center (s / 4096)),
      localGamma μ hX.quadratic
        (d2.replacement.replacement i - d1.replacement.replacement i - (c • e.one.sobolev + U b))
        (d2.replacement.replacement i - d1.replacement.replacement i - (c • e.one.sobolev + U b)) x ≤ Q ^ 2 * s ^ 2 * sigma ^ 2 := by
    have hr : (1 / 4096 : ℝ) * distanceSourceRadius e.heat.radius i = s / 4096 := by
      dsimp only [s]
      ring
    rw [hr] at hgrad
    exact hgrad
  obtain ⟨N, hN, hNnorm, hm⟩ := hmass e hcenter d1 d2 hA hCχ hzeta hzeta1 hsmall i
    (by rw [dist_comm]; linarith) c b Q L sigma hQ.le hL.le hsig0 Hpair hrep hfit hgrad'
  refine ⟨N, hN, hNnorm, hm.trans ?_⟩
  have hsource : normalizedPoissonDefect μ hX.quadratic d1.source i +
      normalizedPoissonDefect μ hX.quadratic d2.source i ≤ sigma ^ 2 := by
    rw [hsigSq]
    exact add_le_add hE1.2 hE2.2
  apply (regular_pair_mass_scaling hX e hcenter d1 d2 (by linarith : 0 ≤ Ccut) hB hJ hCχ i hsource).trans
  dsimp only [Cpin]
  gcongr
  exact le_max_left _ _

end RegularPointCoordinates

end

end OAI
