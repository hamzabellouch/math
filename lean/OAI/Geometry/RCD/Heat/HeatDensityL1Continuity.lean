import OAI.Geometry.RCD.Heat.HeatBoundedMeasurableTest

namespace OAI

/-! # Spatial L¹ continuity of the actual heat densities -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- Duality against the measurable sign of a density difference gives
quantitative L¹ continuity without assuming any pointwise density bound. -/
theorem heatRadonDensity_integral_abs_sub_le (t : ℝ) (ht : 0 < t) (x y : X) :
    (∫ z, |hX.heatRadonDensity hn p t ht x z - hX.heatRadonDensity hn p t ht y z|
      ∂hausdorff n X) ≤
      Real.sqrt (1 / (2 * t * Real.exp (-2 * |K| * t))) * dist x y := by
  let μ := hausdorff n X
  let d (z : X) := hX.heatRadonDensity hn p t ht x z - hX.heatRadonDensity hn p t ht y z
  have hd : Measurable d := (hX.heatRadonDensity_measurable hn p t ht x).sub
    (hX.heatRadonDensity_measurable hn p t ht y)
  let f (z : X) : ℝ := if 0 ≤ d z then 1 else -1
  have hf : Measurable f := measurable_const.ite (measurableSet_le measurable_const hd)
    measurable_const
  have hb (z : X) : |f z| ≤ (1 : ℝ≥0) := by simp only [f]; split_ifs <;> norm_num
  have he (z : X) : d z * f z = |d z| := by
    dsimp only [f]
    split_ifs with hz
    · rw [mul_one, abs_of_nonneg hz]
    · rw [mul_neg_one, abs_of_neg (lt_of_not_ge hz)]
  have hi (a : X) : Integrable (fun z => hX.heatRadonDensity hn p t ht a z * f z) μ :=
    (hX.heatRadonDensity_integrable hn p t ht a).mul_bdd hf.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hrep (a : X) : (∫ z, f z ∂hX.heatRadonMeasure hn p t ht a) =
      ∫ z, hX.heatRadonDensity hn p t ht a z * f z ∂μ :=
    (integral_toReal_rnDeriv_mul (hX.heatRadonMeasure_absolutelyContinuous hn p t ht a)).symm
  have hdiff : (∫ z, f z ∂hX.heatRadonMeasure hn p t ht x) -
      (∫ z, f z ∂hX.heatRadonMeasure hn p t ht y) = ∫ z, |d z| ∂μ := by
    rw [hrep, hrep, ← integral_sub (hi x) (hi y)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simpa only [sub_mul, d] using he z
  have hl := (hX.heatRadonMeasure_integral_measurable_lipschitz hn p t ht f hf 1 hb).dist_le_mul x y
  rw [Real.dist_eq, hdiff, abs_of_nonneg (integral_nonneg fun z => abs_nonneg (d z))] at hl
  simpa only [NNReal.coe_one, one_pow, NNReal.coe_mk, d, μ] using! hl

/-- The density as an element of the actual L¹ space. -/
def heatL1Density (t : ℝ) (ht : 0 < t) (x : X) : Lp ℝ 1 (hausdorff n X) :=
  (hX.heatRadonDensity_integrable hn p t ht x).toL1 (hX.heatRadonDensity hn p t ht x)

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatL1Density_coe (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatL1Density hn p t ht x =ᵐ[hausdorff n X] hX.heatRadonDensity hn p t ht x :=
  Integrable.coeFn_toL1 _

theorem heatL1Density_lipschitz (t : ℝ) (ht : 0 < t) :
    LipschitzWith ⟨Real.sqrt (1 / (2 * t * Real.exp (-2 * |K| * t))), Real.sqrt_nonneg _⟩
      (hX.heatL1Density hn p t ht) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  have he : (∫ z, ‖(hX.heatL1Density hn p t ht x - hX.heatL1Density hn p t ht y) z‖
      ∂hausdorff n X) =
      ∫ z, |hX.heatRadonDensity hn p t ht x z - hX.heatRadonDensity hn p t ht y z|
        ∂hausdorff n X := by
    apply integral_congr_ae
    filter_upwards [hX.heatL1Density_coe hn p t ht x, hX.heatL1Density_coe hn p t ht y,
      Lp.coeFn_sub (hX.heatL1Density hn p t ht x) (hX.heatL1Density hn p t ht y)] with z hx hy hs
    simp only [hs, Pi.sub_apply, hx, hy, Real.norm_eq_abs]
  rw [he]
  exact hX.heatRadonDensity_integral_abs_sub_le hn p t ht x y

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
