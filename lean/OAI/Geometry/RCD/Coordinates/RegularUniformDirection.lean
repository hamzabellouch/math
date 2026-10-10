import OAI.Geometry.RCD.Coordinates.RegularPairDirection
import OAI.Geometry.RCD.Harmonic.DirectionSmallness

namespace OAI

/-! # A uniform direction bound for the actual regular-neighborhood family -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- One constant and tolerance work at every center and scale of the
constructed family. Only the original scalar source envelope must be small. -/
theorem regular_pair_direction_uniform {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (haction : LocalPoissonHessianActionInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ A B J Cχ Cg D Ca : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ) :
    ∃ L tau : ℝ, 0 < L ∧ 0 < tau ∧
    ∀ {base first center : X} {a C enlargement zeta eta : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
      (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
      (_hfirst : first ∈ ball base (e.heat.radius / 32))
      (_hcenter : center ∈ ball base (e.heat.radius / 32))
      (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center),
    0 ≤ zeta → zeta ≤ tau → ∀ i,
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let delta := (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let Ω := ball center (s / 2048)
    let E1 := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d1.source) i
    let E2 := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d2.source) i
    dist first center ≤ s / 512 → E1 + E2 ≤ tau →
    ∃ H : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic,
      (∀ b, SobolevSpace.toLp μ hX.quadratic (H b) =ᵐ[μ.restrict Ω]
        localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U b)) ∧
      ∀ b, ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic Ω
          (H b - ⟪delta, b⟫_ℝ • e.one.sobolev))‖ ≤
        L * s * Real.sqrt (E1 + E2) * ‖b‖ := by
  obtain ⟨G, M, hG, hM, hpair⟩ := regular_pair_direction hX haction hgradient hmean hn hκ
  let Vc := regularRadialValueCoefficient n B D
  let Ec := regularRadialEnergyCoefficient K n Cg A B J Cχ D
  let Ccom := ((5 / 3 : ℝ) * ((1 / 32 : ℝ) ^ n)⁻¹) * poissonCommutatorConstant n A 1 B J Cχ
  have hVc : 0 ≤ Vc := by dsimp only [Vc, regularRadialValueCoefficient]; have := euclideanUnitVolume_pos n; positivity
  have hEc : 0 ≤ Ec := by
    have := (radialEnergyConstant_pos (K := K) (n := n) (G := Cg) (ε := 1) (A := A) hB hJ hCχ).le
    dsimp only [Ec, regularRadialEnergyCoefficient]
    have := euclideanUnitVolume_pos n
    positivity
  have hCcom : 0 ≤ Ccom := by
    have := euclideanUnitVolume_pos n
    dsimp only [Ccom, poissonCommutatorConstant]
    positivity
  have hQ : 0 ≤ radialFitQualitativeConstant n Cχ := radialFitQualitativeConstant_nonneg n hCχ
  obtain ⟨tau, htau, htau1, htframe, htgram, hsmall⟩ :=
    direction_smallness_parameters n Ca D (radialFitQualitativeConstant n Cχ) Vc G hQ hVc (by linarith)
  let L := max (directionRecoveryConstant A Vc Ec Ccom G M) 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨L, tau, hL, htau, ?_⟩
  intro base first center a C enlargement zeta eta ker hk e hfirst hcenter d1 d2 hzeta hzt
    i μ s U delta Ω E1 E2 hroom hEt
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have he1 := (radial_fit_pinching_envelope_budget d1.source hκ hCχ hzeta d1.summable).2.2 i
  have he2 := (radial_fit_pinching_envelope_budget d2.source hκ hCχ hzeta d2.summable).2.2 i
  have hE1 : 0 ≤ E1 := he1.1
  have hE2 : 0 ≤ E2 := he2.1
  have hE1t : E1 ≤ tau := by linarith
  have hE2t : E2 ≤ tau := by linarith
  have hframe : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * zeta) ≤ 1 / 3 := by
    apply le_trans _ htframe
    gcongr
  have hgram : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (8192 : ℝ) ^ n) * zeta) ≤ 1 / 2 := by
    apply le_trans _ htgram
    gcongr
  have hxsmall := hsmall zeta E1 hzeta hzt hE1 hE1t
  have hzsmall := hsmall zeta E2 hzeta hzt hE2 hE2t
  have hcurv : -κ ≤ K * (s / 2048) ^ 2 := by
    by_cases hKpos : 0 ≤ K
    · exact (neg_nonpos.mpr hκ).trans (mul_nonneg hKpos (sq_nonneg _))
    · have hsR : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
      have hs1 : s / 2048 ≤ 1 := by linarith [e.heat.radius_le_one]
      have hsq : (s / 2048) ^ 2 ≤ 1 := by nlinarith [hs.le]
      exact hK.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonpos_left hsq (le_of_not_ge hKpos))
  obtain ⟨H, hH, hfit⟩ := hpair e hfirst hcenter d1 d2 hK hB hJ hA hCχ hzeta
    (hzt.trans htau1) hframe hgram i hroom hcurv (hxsmall.1.trans (by norm_num))
    hzsmall.1 (hzsmall.2 s hs)
  refine ⟨H, hH, ?_⟩
  have hP : normalizedPoissonDefect μ hX.quadratic d1.source i +
      normalizedPoissonDefect μ hX.quadratic d2.source i ≤ E1 + E2 := add_le_add he1.2 he2.2
  have hPn : 0 ≤ normalizedPoissonDefect μ hX.quadratic d1.source i +
      normalizedPoissonDefect μ hX.quadratic d2.source i := add_nonneg
      (normalizedPoissonDefect_nonneg μ hX.quadratic d1.source hκ i)
      (normalizedPoissonDefect_nonneg μ hX.quadratic d2.source hκ i)
  have hscale := direction_recovery_scaled_bound hs hA hVc hEc hCcom
    (by linarith : 0 ≤ G) (by linarith : 0 ≤ M) hE1 hE2 hPn hP
  dsimp only at hscale
  intro b
  apply (hfit b).trans
  apply (mul_le_mul_of_nonneg_right hscale (norm_nonneg b)).trans
  dsimp only [L]
  gcongr
  exact le_max_left _ _

end RegularPointCoordinates

end

end OAI
