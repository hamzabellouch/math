import OAI.Geometry.RCD.Coordinates.RegularPairCoordinates
import OAI.Geometry.RCD.Sobolev.FiniteColumnEnergy

namespace OAI

/-! # The exact interior frame used to test full directional mass -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The volume loss from the radial normalization ball to the mass-test ball. -/
def pinchingFrameVolumeRatio (n : ℕ) : ℝ :=
  (5 / 3 : ℝ) * ((1 / 32768 : ℝ) ^ n)⁻¹

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same actual harmonic coordinates admit a bounded exact frame on
three times the mass radius, with a gradient bound on the cutoff support. -/
theorem regular_pinching_frame {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center)
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsmall : (n : ℝ) ^ 2 * (pinchingFrameVolumeRatio n * zeta) ≤ 1 / 2)
    (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d.frame i).toContinuousLinearMap
    let rho := s / 49152
    ∃ N : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hX.quadratic U (ball center (3 * rho)) measurableSet_ball N ∧
      ‖N.toContinuousLinearMap‖ ≤ 2 ∧
      ∀ b, ∀ᵐ x ∂μ.restrict (closedBall center (6 * rho)),
        localGamma μ hX.quadratic (U (N b)) (U (N b)) x ≤ 16 * (n : ℝ) ^ 2 * ‖b‖ ^ 2 := by
  intro μ s U rho
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
  let u := centeredColumn μ hX.quadratic
    (transformedColumn μ hX.quadratic e.heat.coordinates (d.frame i))
    ((d.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
  have hU : sobolevColumnMap μ hX.quadratic u = U := centered_transformed_columnMap μ hX.quadratic _ _ _ _
  have hf := (d.splitting i).center μ hX.quadratic
    ((d.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
    (e.oneRepresentative center hcenter i)
  have hsub : ball center (3 * rho) ⊆ ball center (2 * s) := ball_subset_ball (by simp only [rho]; linarith)
  have hvol := e.volume center hcenter (2 * s) (by positivity) (by linarith)
  have hvolSmall := e.volume center hcenter (3 * rho) (by simp only [rho]; positivity) (by simp only [rho]; linarith)
  have hp : 0 < μ.real (ball center (3 * rho)) :=
    (quarter_volume_bounds (by simp only [rho]; positivity) (euclideanUnitVolume_pos n) hvolSmall).1
  have hratio : μ.real (ball center (2 * s)) ≤ pinchingFrameVolumeRatio n * μ.real (ball center (3 * rho)) := by
    apply (div_le_iff₀ hp).mp
    exact radial_fraction_volume_ratio (by positivity : 0 < 2 * s)
      (by norm_num : (0 : ℝ) < 1 / 32768) (euclideanUnitVolume_pos n) hvol
      (by simpa only [rho, show (1 / 32768 : ℝ) * (2 * s) = 3 * (s / 49152) by ring] using hvolSmall)
  have hg := meanGram_sub_id_norm_le_of_subset μ hX.quadratic u measurableSet_ball hsub
    (ne_of_gt (hX.fullSupport _ _ (by simp only [rho]; positivity)))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_gt (hX.fullSupport _ _ (by positivity)))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (by dsimp only [pinchingFrameVolumeRatio]; positivity) hzeta hratio hf.gram
  obtain ⟨N, hN, hnorm⟩ := bounded_exact_mean_normalization μ hX.quadratic
    (sobolevColumnMap μ hX.quadratic u) (ball center (3 * rho)) measurableSet_ball (hg.trans hsmall)
  rw [hU] at hN
  refine ⟨N, hN, hnorm, ?_⟩
  have hclosed : closedBall center (6 * rho) ⊆ ball center (2 * s) :=
    closedBall_subset_ball (by simp only [rho]; linarith)
  have hrows : ∀ᵐ x ∂μ.restrict (closedBall center (6 * rho)), ∀ j : Fin n,
      localGamma μ hX.quadratic (u j) (u j) x ≤ 4 := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hclosed (hf.gradient j)] with x hx
    exact hx.trans (by nlinarith)
  intro b
  have hcol : ∀ᵐ x ∂μ.restrict (closedBall center (6 * rho)),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u (N b))
        (sobolevColumnMap μ hX.quadratic u (N b)) x ≤
        (n : ℝ) * ‖N b‖ ^ 2 * ∑ j, localGamma μ hX.quadratic (u j) (u j) x :=
    ae_restrict_of_ae (localGamma_column_le_diagonal_sum μ hX.quadratic u (N b))
  rw [hU] at hcol
  have hnb : ‖N b‖ ≤ 2 * ‖b‖ :=
    (N.toContinuousLinearMap.le_opNorm b).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg b))
  filter_upwards [hrows, hcol] with x hx hc
  have hsum : (∑ j, localGamma μ hX.quadratic (u j) (u j) x) ≤ (n : ℝ) * 4 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hx j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  calc
    _ ≤ (n : ℝ) * ‖N b‖ ^ 2 * ∑ j, localGamma μ hX.quadratic (u j) (u j) x := hc
    _ ≤ (n : ℝ) * ‖N b‖ ^ 2 * ((n : ℝ) * 4) := by gcongr
    _ ≤ (n : ℝ) * (2 * ‖b‖) ^ 2 * ((n : ℝ) * 4) := by gcongr
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
