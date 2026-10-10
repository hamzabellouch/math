import OAI.Geometry.RCD.Sobolev.CenteredPoissonPinching
import OAI.Geometry.RCD.Coordinates.RegularPairBochner

namespace OAI

/-! # Full original heat mass from the actual two-center estimates -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The two estimates already proved for the actual replacements control
an actual direction of the original heat measure, including singular mass. -/
theorem regular_pair_mass_from_estimates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hhessian : LocalPoissonHessianInput hX) (hcutoff : LocalGoodCutoffInput hX) (hn : 2 ≤ n) :
    ∃ Ccut : ℝ, 1 ≤ Ccut ∧
    ∀ {base first center : X} {a B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
      (e : RegularProjectionEnvironment hX base hk a |K| B J C A Cχ enlargement zeta eta)
      (_hcenter : center ∈ ball base (e.heat.radius / 32))
      (d1 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca center),
    0 ≤ A → 0 ≤ Cχ → 0 ≤ zeta → zeta ≤ 1 →
    (n : ℝ) ^ 2 * (pinchingFrameVolumeRatio n * zeta) ≤ 1 / 2 →
    ∀ i,
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let rho := s / 49152
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let delta := (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let Ω := ball center (s / 2048)
    let Rvol := (5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹
    let Praw := 2 * (4096 * Cχ * (J + B / 2) *
      ((d1.source.source i).real (ball first s) + (d2.source.source i).real (ball center s)) +
      |K| * A ^ 2 * s ^ 2 * (μ.real (ball first s) + μ.real (ball center s)))
    let Fcut := ((Ccut / (3 * rho) ^ 2) / 2 + |K|) * μ.real (closedBall center (6 * rho))
    dist center first ≤ s / 4 →
    ∀ (c : ℝ) (b : Euclidean n) (Q L sigma : ℝ), 0 ≤ Q → 0 ≤ L → 0 ≤ sigma →
    ∀ Hpair : Euclidean n →L[ℝ] SobolevSpace μ hX.quadratic,
    (∀ v, SobolevSpace.toLp μ hX.quadratic (Hpair v) =ᵐ[μ.restrict Ω]
      localGamma μ hX.quadratic (d2.replacement.replacement i - d1.replacement.replacement i) (U v)) →
    (∀ v, ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic Ω (Hpair v - ⟪delta, v⟫_ℝ • e.one.sobolev))‖ ≤
        (L * s * sigma) * ‖v‖) →
    (∀ᵐ x ∂μ.restrict (ball center (s / 4096)),
      localGamma μ hX.quadratic
        (d2.replacement.replacement i - d1.replacement.replacement i - (c • e.one.sobolev + U b))
        (d2.replacement.replacement i - d1.replacement.replacement i - (c • e.one.sobolev + U b)) x ≤
          Q ^ 2 * s ^ 2 * sigma ^ 2) →
    ∃ N : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hX.quadratic U (ball center (3 * rho)) measurableSet_ball N ∧
      ‖N.toContinuousLinearMap‖ ≤ 2 ∧
      let v := d2.frame i (N (N.toContinuousLinearMap.adjoint delta))
      ⟪v, e.heat.mass.massOperator (ball center rho) v⟫_ℝ ≤
        4 * (Praw + Fcut * (Q ^ 2 * s ^ 2 * sigma ^ 2)) +
          4 * (Fcut * (16 * (n : ℝ) ^ 2)) *
            ((2 * Real.sqrt Rvol * (L * s * sigma)) ^ 2 + Q ^ 2 * s ^ 2 * sigma ^ 2) := by
  obtain ⟨Ccut, hCcut, hcuts⟩ := hcutoff hn
  obtain ⟨_, _, hpair⟩ := regular_pair_bochner hX hhessian hcutoff hn
  refine ⟨Ccut, hCcut, ?_⟩
  intro base first center a B J C A Cχ enlargement zeta eta Cg D Ca ker hk e hcenter d1 d2
    hA hCχ hzeta hzeta1 hsmall i μ s rho U delta Ω Rvol Praw Fcut hroom c b Q L sigma hQ hL hsigma Hpair hrep hfit hgrad
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
  have hrad : 0 < 3 * rho := by dsimp only [rho]; positivity
  have hcurv : -1 ≤ K * (3 * rho) ^ 2 := by
    have hsq : (3 * rho) ^ 2 ≤ e.heat.radius ^ 2 := by dsimp only [rho]; nlinarith [e.heat.radius_pos]
    have habs := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (3 * rho))
    have hc := e.curvature
    nlinarith [mul_nonneg (abs_nonneg K) (sq_nonneg e.heat.radius)]
  let chi := Classical.choice (hcuts center (3 * rho) hrad hcurv)
  obtain ⟨N, hN, hNnorm, hcoord⟩ := regular_pinching_frame hX e hcenter d2 hzeta hzeta1 hsmall i
  refine ⟨N, hN, hNnorm, ?_⟩
  obtain ⟨Ljoint, M, henergy, hraw, hcompare⟩ := hpair hA hCχ e hcenter d1 d2 i hroom
  let f : Fin 2 → SobolevSpace μ hX.quadratic := ![d1.replacement.replacement i, d2.replacement.replacement i]
  let v1 : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
  let v2 : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (1 : Fin 2)) 1
  have hsub : ball center (3 * rho) ⊆ Ω := ball_subset_ball (by dsimp only [rho]; linarith)
  have hclosed : closedBall center (6 * rho) ⊆ ball center (2 * s) :=
    closedBall_subset_ball (by dsimp only [rho]; linarith)
  have hone := ae_restrict_of_ae_restrict_of_subset hclosed (e.oneRepresentative center hcenter i)
  have honeSmall := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : 3 * rho ≤ 6 * rho))) hone
  have hvolBig := e.volume center hcenter (s / 2048) (by positivity) (by linarith)
  have hvolSmall := e.volume center hcenter (3 * rho) hrad (by dsimp only [rho]; linarith)
  have hpBig : 0 < μ.real Ω := (quarter_volume_bounds (by positivity) (euclideanUnitVolume_pos n) hvolBig).1
  have hpSmall : 0 < μ.real (ball center (3 * rho)) := (quarter_volume_bounds hrad (euclideanUnitVolume_pos n) hvolSmall).1
  have hratio : μ.real Ω ≤ Rvol * μ.real (ball center (3 * rho)) := by
    apply (div_le_iff₀ hpSmall).mp
    exact radial_fraction_volume_ratio (by positivity : 0 < s / 2048)
      (by norm_num : (0 : ℝ) < 1 / 8) (euclideanUnitVolume_pos n) hvolBig
      (by simpa only [rho, show (1 / 8 : ℝ) * (s / 2048) = 3 * (s / 49152) by ring] using hvolSmall)
  have herror := pinching_pairing_restrict μ hX.quadratic hsub
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hpBig hpSmall
    e.one.sobolev honeSmall Hpair delta N hNnorm
    (by dsimp only [Rvol]; positivity) (by positivity : 0 ≤ L * s * sigma) hratio hfit
  have hsmallraw : ⟪v2 - v1, M.massOperator (ball center (3 * rho)) (v2 - v1)⟫_ℝ ≤ Praw := by
    apply le_trans _ hraw
    rw [← M.measure_real _ _ measurableSet_ball, ← M.measure_real _ _ measurableSet_ball]
    exact measureReal_mono (ball_subset_ball (by dsimp only [rho]; linarith)) (measure_ne_top _ _)
  have hsmallgrad := ae_restrict_of_ae_restrict_of_subset
    (closedBall_subset_ball (by dsimp only [rho]; linarith : 6 * rho < s / 4096)) hgrad
  have hsmallrep (v : Euclidean n) := ae_restrict_of_ae_restrict_of_subset hsub (hrep (N v))
  have h2rho : 2 * (3 * rho) = 6 * rho := by ring
  have hm := centered_poisson_directional_mass (beta := Q ^ 2 * s ^ 2 * sigma ^ 2)
    (P := Praw) (H := 16 * (n : ℝ) ^ 2) (D := 2 * Real.sqrt Rvol * (L * s * sigma))
    μ hX.quadratic e.heat.coordinates f e.one.sobolev
    (e.heat.values center) delta b c (d2.frame i) N (Hpair.comp N.toContinuousLinearMap) M chi
    hrad (by dsimp only [rho]; linarith : 3 * rho < s / 32)
    (by linarith : 0 ≤ Ccut) (abs_nonneg K) (by positivity : 0 ≤ 16 * (n : ℝ) ^ 2)
    (by positivity : 0 ≤ 2 * Real.sqrt Rvol * (L * s * sigma)) hpSmall
    (by
      rw [h2rho]
      filter_upwards [hone] with x hx
      exact hx) hN
    (fun v => Classical.choice (henergy v))
    (by simpa [μ, f, U, h2rho] using hsmallgrad)
    (by simpa [μ, rho, s, h2rho] using hcoord) hsmallrep herror hsmallraw
  have htest := hcompare (d2.frame i (N (N.toContinuousLinearMap.adjoint delta)))
  apply htest.trans
  simpa only [Fcut, h2rho] using hm

end RegularPointCoordinates

end

end OAI
