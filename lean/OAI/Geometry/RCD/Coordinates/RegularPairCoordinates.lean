import OAI.Geometry.RCD.Coordinates.RegularPairCommutator
import OAI.Geometry.RCD.Coordinates.ProjectionCoordinateValues
import OAI.Geometry.RCD.Coordinates.LinearNormalization
import OAI.Geometry.RCD.Coordinates.NormalizedPairing

namespace OAI

/-! # The actual interior frame and coordinate values for direction recovery -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A half-unit Gram error constructs a bounded exact normalizer. -/
theorem bounded_exact_mean_normalization (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hsmall : ‖sobolevMeanGram μ hQ U Ω hΩ - ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ 1 / 2) :
    ∃ N : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hQ U Ω hΩ N ∧ ‖N.toContinuousLinearMap‖ ≤ 2 := by
  have hl (v : Euclidean n) := inner_lower_of_sub_id_norm _ hsmall v
  obtain ⟨N, hN⟩ := exists_exact_mean_normalization μ hQ U Ω hΩ (by
    intro v hv
    have hp := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    nlinarith only [hl v, hp])
  refine ⟨N, hN, ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_⟩
  intro v
  have hh := hl (N v)
  rw [meanGram_energy_of_exact_normalization μ hQ U Ω hΩ N hN,
    N.symm_apply_apply] at hh
  have hNv := norm_nonneg (N v)
  have hv := norm_nonneg v
  change ‖N v‖ ≤ 2 * ‖v‖
  nlinarith only [hh, hNv, hv, sq_nonneg (‖N v‖ - 2 * ‖v‖)]

/-- The interior normalization and coordinate size are consequences of
the same actual splitting map used for both radial fits. -/
theorem regular_pair_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center)
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (8192 : ℝ) ^ n) * zeta) ≤ 1 / 2)
    (i : ℕ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let u := centeredColumn μ hX.quadratic
      (transformedColumn μ hX.quadratic e.heat.coordinates (d.frame i))
      ((d.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
    let V := fun x => (d.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values x - e.heat.values center)
    FirstOrderSplittingOn μ hX.quadratic center (2 * s) zeta u V ∧
    V center = 0 ∧
    ∃ N : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hX.quadratic (sobolevColumnMap μ hX.quadratic u)
        (ball center ((s / 2048) / 2)) measurableSet_ball N ∧
      ‖N.toContinuousLinearMap‖ ≤ 2 ∧
      ∀ b, ‖normalizeLocalL2 μ (ball center (s / 2048))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball center (s / 2048))
          (sobolevColumnMap μ hX.quadratic u b))‖ ≤ s * ‖b‖ := by
  intro μ s u V
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
  have hone := e.oneRepresentative center hcenter i
  have hf : FirstOrderSplittingOn μ hX.quadratic center (2 * s) zeta u V := by
    simpa only [V, map_sub] using (d.splitting i).center μ hX.quadratic
      ((d.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev hone
  have hzero : V center = 0 := by simp only [V, sub_self, map_zero]
  refine ⟨hf, hzero, ?_⟩
  let Ω := ball center ((s / 2048) / 2)
  have hsub : Ω ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hvol := e.volume center hcenter (2 * s) (by positivity) (by linarith)
  have hvolSmall := e.volume center hcenter ((s / 2048) / 2) (by positivity) (by linarith)
  have hp : 0 < μ.real Ω := (quarter_volume_bounds (by positivity)
    (euclideanUnitVolume_pos n) hvolSmall).1
  have hratio : μ.real (ball center (2 * s)) ≤
      ((5 / 3 : ℝ) * (8192 : ℝ) ^ n) * μ.real Ω := by
    apply (div_le_iff₀ hp).mp
    have hh := radial_fraction_volume_ratio (by positivity : 0 < 2 * s)
      (by norm_num : (0 : ℝ) < 1 / 8192) (euclideanUnitVolume_pos n) hvol
      (by simpa only [show (1 / 8192 : ℝ) * (2 * s) = (s / 2048) / 2 by ring] using hvolSmall)
    have hpow : (((1 / 8192 : ℝ) ^ n)⁻¹) = (8192 : ℝ) ^ n := by simp
    rw [hpow] at hh
    exact hh
  have hg := meanGram_sub_id_norm_le_of_subset μ hX.quadratic u measurableSet_ball hsub
    (ne_of_gt (hX.fullSupport _ _ (by positivity)))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_gt (hX.fullSupport _ _ (by positivity)))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (by positivity : 0 ≤ (5 / 3 : ℝ) * (8192 : ℝ) ^ n) hzeta hratio hf.gram
  obtain ⟨N, hN, hnorm⟩ := bounded_exact_mean_normalization μ hX.quadratic
    (sobolevColumnMap μ hX.quadratic u) Ω measurableSet_ball (hg.trans hsmall)
  refine ⟨N, hN, hnorm, ?_⟩
  have hsub512 : ball center (s / 512) ⊆ ball center (2 * s) := ball_subset_ball (by linarith)
  have hvalues := projection_coordinate_values μ hX.quadratic hs hzeta1 u V
    (ContinuousLinearEquiv.refl ℝ (Euclidean n)) hzero
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub512 (hf.representative j))
    (by simpa only [V, map_sub, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using d.metric i)
  intro b
  apply normalized_norm_le_of_bound μ _ _ _ (by positivity)
  have hb := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 2048 ≤ s / 512)) (hvalues b)
  filter_upwards [hb, SobolevSpace.restrictLp_coe μ hX.quadratic
    (ball center (s / 2048)) (sobolevColumnMap μ hX.quadratic u b)] with x hx hrep
  rw [hrep]
  simpa only [ContinuousLinearEquiv.coe_refl', id_eq] using hx

end RegularPointCoordinates

end

end OAI
