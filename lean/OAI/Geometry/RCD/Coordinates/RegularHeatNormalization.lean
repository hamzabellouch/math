import OAI.Geometry.RCD.Coordinates.RegularMassMatrices
import OAI.Geometry.RCD.Coordinates.RegularFrameGeometry
import OAI.Geometry.RCD.Coordinates.NormalizationCumulative

namespace OAI

/-! # Changing actual mean frames in the cumulative heat estimates -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- The same positive heat Gram used in the neighborhood construction. -/
def heatAt (q : X) (i : ℕ) : Euclidean n ≃L[ℝ] Euclidean n :=
  dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
    (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
    d.cutoff q d.radius_pos d.lambda_pos i

theorem heatAt_isPositive (q : X) (i : ℕ) : (d.heatAt q i).toContinuousLinearMap.IsPositive :=
  dyadicHeatGramAt_isPositive (hausdorff n X) hX.quadratic hk _ d.cutoff q d.radius_pos d.lambda_pos i

end RegularBilinearData

/-- A nearby mean dominates one quarter of the central heat metric.
Both means are compared inside a single larger normalized ball. -/
theorem regular_nearby_mean_heat_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 1)
    (hroom : dist z q ≤ e.heat.radius / (2 : ℝ) ^ (i + 1)) (v : Euclidean n) :
    (1 / 4 : ℝ) * ⟪v, e.heat.heatAt q (i + 1) v⟫_ℝ ≤
      ⟪v, e.heat.meanAt z hz (i + 1) v⟫_ℝ := by
  have hr : 0 < e.heat.radius / (2 : ℝ) ^ i := div_pos e.heat.radius_pos (by positivity)
  have heq : (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) =
      e.heat.radius / (2 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
  have hqroom : dist q q + (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) ≤
      e.heat.radius / (2 : ℝ) ^ i := by rw [dist_self]; linarith
  have hzroom : dist z q + (1 / 2 : ℝ) * (e.heat.radius / (2 : ℝ) ^ i) ≤
      e.heat.radius / (2 : ℝ) ^ i := by rw [heq]; rw [← heq] at hroom; linarith
  have hbq := (regular_subball_mean_comparison hX e hq hq hzeta i
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hqroom v).2
  have hbz := (regular_subball_mean_comparison hX e hq hz hzeta i
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hzroom v).1
  rw [heq] at hbq hbz
  have hheat := (e.heat.heatMeanComparison q hq (i + 1) hi v).2
  have hnonneg := (sobolevMeanGram_isPositive (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    (ball q (e.heat.radius / (2 : ℝ) ^ i)) measurableSet_ball).inner_nonneg_right v
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  change (1 / 4 : ℝ) * ⟪v, e.heat.heatAt q (i + 1) v⟫_ℝ ≤
    ⟪v, (e.heat.meanAt z hz (i + 1)).toContinuousLinearMap v⟫_ℝ
  rw [e.heat.meanAt_toContinuousLinearMap]
  change (1 / 4 : ℝ) * ⟪v, dyadicHeatGramAt (hausdorff n X) hX.quadratic hk
    (sobolevColumnMap (hausdorff n X) hX.quadratic e.heat.coordinates)
    e.heat.cutoff q e.heat.radius_pos e.heat.lambda_pos (i + 1) v⟫_ℝ ≤ _
  nlinarith

/-- The actual inverse-frame discrepancy has the weighted envelope bound
needed for summing over patch centers. -/
theorem regular_inverse_mean_heat_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) (hi : e.heat.shift ≤ i + 1)
    (hroom : dist z q ≤ e.heat.radius / (2 : ℝ) ^ (i + 1))
    (henlargement : dist q z ≤ enlargement * (e.heat.radius / (2 : ℝ) ^ (i + 1)))
    (xi : Euclidean n) :
    let Q := e.heat.heatAt q (i + 1)
    let R := e.heat.meanAt z hz (i + 1)
    let F := dyadicBochnerEnvelope e.heat.mass n q e.heat.radius (i + 1)
    ⟪R.symm xi - Q.symm xi, Q (R.symm xi - Q.symm xi)⟫_ℝ ≤
      16 * e.heat.comparisonConstant * ⟪Q.symm xi, F (Q.symm xi)⟫_ℝ := by
  intro Q R F
  have hbilinear (u v : Euclidean n) :
      ⟪v, (R.toContinuousLinearMap - Q.toContinuousLinearMap) u⟫_ℝ ^ 2 ≤
        (e.heat.comparisonConstant * ⟪u, F u⟫_ℝ) * ⟪v, Q v⟫_ℝ := by
    have h := (e.heat.localData q hq).2.1 (i + 1) hi z henlargement v u
    dsimp only [R, Q, F, RegularBilinearData.heatAt]
    rw [e.heat.meanAt_toContinuousLinearMap]
    convert h using 1
    ring
  have h := inverse_normalization_error_le Q R (e.heat.heatAt_isPositive q (i + 1))
    (e.heat.meanAt_isPositive z hz (i + 1)) F
    (dyadicBochnerEnvelope_isPositive e.heat.mass n q e.heat.radius_pos.le (i + 1))
    (by norm_num : (0 : ℝ) < 1 / 4) e.heat.comparisonConstant_pos.le
    (regular_nearby_mean_heat_lower hX e hq hz hzeta hsmall i hi hroom) hbilinear xi
  norm_num at h ⊢
  nlinarith

end RegularPointCoordinates

end

end OAI
