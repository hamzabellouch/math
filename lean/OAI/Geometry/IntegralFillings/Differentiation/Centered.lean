import Mathlib
import OAI.Geometry.IntegralFillings.Currents.DenseTests
import OAI.Geometry.IntegralFillings.Differentiation.Seminorm

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}
noncomputable def metricQuotient (f : E → X) (x : E) (t : ℝ) (v : E) : ℝ :=
  dist (f (x+t • v)) (f x) / |t|

lemma metricQuotient_lipschitz (hf : LipschitzWith K f) (x : E) (t : ℝ) :
    LipschitzWith K (metricQuotient f x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  by_cases ht : t = 0
  · simp only [metricQuotient, ht, abs_zero, div_zero, dist_self]
    positivity
  have ht' : 0 < |t| := abs_pos.mpr ht
  simp only [metricQuotient, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  calc |dist (f (x+t • v)) (f x) - dist (f (x+t • w)) (f x)|/|t| ≤
        dist (f (x+t • v)) (f (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _) ht'.le
    _ ≤ ((K : ℝ) * dist (x+t • v) (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (hf.dist_le_mul _ _) ht'.le
    _ = (K : ℝ) * dist v w := by
      rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, dist_eq_norm]
      field_simp

def HasCenteredMetricDifferential (f : E → X) (p : Seminorm ℝ E) (x : E) : Prop :=
  (fun y => dist (f y) (f x) - p (y-x)) =o[𝓝 x] (fun y => y-x)

lemma hasCenteredMetricDifferential_of_dense_directions [FiniteDimensional ℝ E]
    (hf : LipschitzWith K f) (x : E) (p : Seminorm ℝ E)
    (hp : LipschitzWith K p) {ι : Type*} {D : ι → E} (hD : DenseRange D)
    (hdir : ∀ j, Tendsto (fun t => metricQuotient f x t (D j)) (𝓝[≠] 0) (𝓝 (p (D j)))) :
    HasCenteredMetricDifferential f p x := by
  have hall (v : E) : Tendsto (fun t => metricQuotient f x t v) (𝓝[≠] 0) (𝓝 (p v)) :=
    tendsto_of_lipschitz_dense (metricQuotient_lipschitz hf x) hp hD hdir v
  apply IsLittleO.of_bound
  intro ε hε
  have hU := uniformly_tendsto_of_lipschitz (metricQuotient_lipschitz hf x) hp
    (isCompact_sphere (0 : E) 1) (fun v _ => hall v) hε
  obtain ⟨δ, hδ, hUδ⟩ := Metric.mem_nhdsWithin_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  let r : ℝ := ‖y-x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let v : E := r⁻¹ • (y-x)
  have hv : v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hrv : r • v = y-x := by dsimp [v]; exact smul_inv_smul₀ hr.ne' _
  have hry : x+r • v = y := by rw [hrv]; abel
  have hrδ : r ∈ ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · change |r-0| < δ
      rw [sub_zero, abs_of_pos hr]
      simpa only [mem_ball, dist_eq_norm, r] using hy
    · exact hr.ne'
  have hh := hUδ hrδ v hv
  change dist (dist (f (x+r • v)) (f x)/|r|) (p v) < ε at hh
  rw [hry, abs_of_pos hr, Real.dist_eq] at hh
  have hpv : p (y-x) = r * p v := by
    rw [← hrv, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hpv, Real.norm_eq_abs]
  change |dist (f y) (f x)-r*p v| ≤ ε*r
  have heq : dist (f y) (f x)-r*p v = r*(dist (f y) (f x)/r-p v) := by field_simp
  rw [heq, abs_mul, abs_of_pos hr]
  exact (mul_lt_mul_of_pos_left hh hr).le.trans_eq (mul_comm r ε)

variable [SeparableSpace X] [Nonempty X] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem ae_hasCenteredMetricDifferential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, HasCenteredMetricDifferential f (metricSeminorm f x) x := by
  filter_upwards [ae_dense_directionalSeminorm μ hf] with x hx
  exact hasCenteredMetricDifferential_of_dense_directions hf x _ (metricSeminorm_lipschitz hf x)
    (denseRange_denseSeq E) hx

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
