import OAI.Geometry.RCD.Coordinates.RegularProjectionEnvironment
import OAI.Geometry.RCD.Coordinates.NormalizedCoordinateFrames
import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits

namespace OAI

/-! # Actual dyadic coordinate frames and their neighboring-ball bounds -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- Use the same exact dyadic frames already furnished by the construction. -/
def frameAt (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ) :
    Euclidean n ≃L[ℝ] Euclidean n :=
  Classical.choose (d.localData q hq).2.2.2 i

theorem frameAt_exact (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ) :
    IsExactMeanNormalization (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
      (ball q (d.radius / 2 ^ i)) measurableSet_ball (d.frameAt q hq i) :=
  (Classical.choose_spec (d.localData q hq).2.2.2).1 i

theorem frameAt_splitting (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ) :
    FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (d.radius / 2 ^ i) zeta
      (transformedColumn (hausdorff n X) hX.quadratic d.coordinates (d.frameAt q hq i))
      (fun x => (d.frameAt q hq i).toContinuousLinearMap.adjoint (d.values x)) :=
  (Classical.choose_spec (d.localData q hq).2.2.2).2.1 i

theorem frameAt_approximation (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ) :
    IsPointedApproximation q 0 ((d.radius / 2 ^ i) / 128) 4 zeta
      (fun x => ((d.radius / 2 ^ i) / 128)⁻¹ •
        ((d.frameAt q hq i).toContinuousLinearMap.adjoint (d.values x) -
          (d.frameAt q hq i).toContinuousLinearMap.adjoint (d.values q))) :=
  (Classical.choose_spec (d.localData q hq).2.2.2).2.2 i

/-- Every raw mean energy is bounded by the already constructed common
harmonic gradient bound. -/
theorem mean_upper (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ)
    (v : Euclidean n) :
    ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
      (ball q (d.radius / 2 ^ i)) measurableSet_ball v⟫_ℝ ≤ (2 * (n : ℝ)) ^ 2 * ‖v‖ ^ 2 := by
  let μ := hausdorff n X
  let U := sobolevColumnMap μ hX.quadratic d.coordinates
  let r := d.radius / (2 : ℝ) ^ i
  have hr : 0 < r := div_pos d.radius_pos (by positivity)
  have hrR : r ≤ d.radius := div_le_self d.radius_pos.le (one_le_pow₀ (by norm_num))
  have hsub : ball q r ⊆ ball base (2 * (4 * d.radius)) := by
    intro x hx
    have ht := dist_triangle x q base
    have hxq : dist x q < r := hx
    have hqb : dist q base < d.radius / 32 := hq
    change dist x base < 2 * (4 * d.radius)
    linarith [d.radius_pos]
  have hg : ∀ᵐ x ∂μ.restrict (ball q r),
      localGamma μ hX.quadratic (U v) (U v) x ≤ (d.energyBound : ℝ) ^ 2 * ‖v‖ ^ 2 :=
    ae_restrict_of_ae_restrict_of_subset hsub
      (LocalHarmonicEnergy.gamma_bound_on_smaller_ball μ hX.quadratic d.energy le_rfl v)
  have hfin : μ (ball q r) ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  have hpos : 0 < μ.real (ball q r) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport q r hr)) hfin
  have hint := integral_mono_ae
    (localGamma_memL1 μ hX.quadratic (U v) (U v)).integrableOn
    (integrableOn_const hfin) hg
  have hm := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpos.le)
  have hn := mul_le_mul_of_nonneg_right d.energyBound_sq (sq_nonneg ‖v‖)
  change ⟪v, sobolevMeanGram μ hX.quadratic U (ball q r) measurableSet_ball v⟫_ℝ ≤ _
  rw [real_inner_comm, sobolevMeanGram_inner]
  calc
    _ ≤ (d.energyBound : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] using hm
    _ ≤ _ := by nlinarith only [hn]

theorem coordinateFrame_lower (q : X) (hq : q ∈ ball base (d.radius / 32))
    (i : ℕ) (w : Euclidean n) :
    ‖w‖ ≤ 2 * (n : ℝ) * ‖coordinateFrame (d.frameAt q hq i) w‖ :=
  norm_le_coordinateFrame_of_mean_upper (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
    (ball q (d.radius / 2 ^ i)) measurableSet_ball (d.frameAt q hq i)
    (d.frameAt_exact q hq i) (by positivity) (d.mean_upper q hq i) w

end RegularBilinearData

/-- Restricting the actual normalized splitting map to a nearby smaller
ball gives a relative bound with just the Euclidean volume-ratio loss. -/
theorem regular_subball_mean_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (i : ℕ) {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hroom : dist z q + theta * (e.heat.radius / 2 ^ i) ≤ e.heat.radius / 2 ^ i)
    (v : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ i
    let loss := (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (theta ^ n)⁻¹) * zeta)
    (1 - loss) * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
      (ball q r) measurableSet_ball v⟫_ℝ ≤
      ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
        (ball z (theta * r)) measurableSet_ball v⟫_ℝ ∧
    ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
      (ball z (theta * r)) measurableSet_ball v⟫_ℝ ≤
      (1 + loss) * ⟪v, sobolevMeanGram (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
        (ball q r) measurableSet_ball v⟫_ℝ := by
  intro r loss
  let μ := hausdorff n X
  have hr : 0 < r := div_pos e.heat.radius_pos (by positivity)
  have hrR : r ≤ e.heat.radius := div_le_self e.heat.radius_pos.le (one_le_pow₀ (by norm_num))
  have htr : 0 < theta * r := mul_pos htheta hr
  have htrR : theta * r ≤ 2 * e.heat.radius := by
    have h := mul_le_mul_of_nonneg_right htheta1 hr.le
    linarith [e.heat.radius_pos]
  have hsub : ball z (theta * r) ⊆ ball q r := by
    intro x hx
    have hh := dist_triangle x z q
    have hxz : dist x z < theta * r := hx
    change dist x q < r
    linarith
  have hvq := e.volume q hq r hr (by linarith [e.heat.radius_pos])
  have hvz := e.volume z hz (theta * r) htr htrR
  have hpos := (quarter_volume_bounds htr (euclideanUnitVolume_pos n) hvz).1
  have hratio : μ.real (ball q r) ≤ ((5 / 3 : ℝ) * (theta ^ n)⁻¹) * μ.real (ball z (theta * r)) :=
    (div_le_iff₀ hpos).mp (radial_fraction_volume_ratio hr htheta (euclideanUnitVolume_pos n) hvq hvz)
  exact exact_normalization_subball_bounds μ hX.quadratic e.heat.coordinates
    (e.heat.frameAt q hq i) (e.heat.frameAt_splitting q hq i) (e.heat.frameAt_exact q hq i)
    _ measurableSet_ball hsub (ne_of_gt (hX.fullSupport _ _ htr))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (ne_of_gt (hX.fullSupport _ _ hr))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (by positivity) hzeta hratio v

end RegularPointCoordinates

end

end OAI
