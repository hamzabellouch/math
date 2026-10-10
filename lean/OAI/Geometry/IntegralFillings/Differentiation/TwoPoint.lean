import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.ErrorModulus

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seminorm_sub_bound_of_sphere {p q : Seminorm ℝ E} {ε : ℝ} (_hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ = 1 → |p v-q v| ≤ ε) (v : E) :
    |p v-q v| ≤ ε*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,hv0.ne']
  have he : ‖v‖ • u = v := by simp [u,hv0.ne']
  have hpv : p v = ‖v‖ * p u := by
    calc p v = p (‖v‖ • u) := congrArg p he.symm
      _ = ‖v‖ * p u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  have hqv : q v = ‖v‖ * q u := by
    calc q v = q (‖v‖ • u) := congrArg q he.symm
      _ = ‖v‖ * q u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  calc |p v-q v| = ‖v‖ * |p u-q u| := by
        rw [hpv,hqv,←mul_sub,abs_mul,abs_of_pos hv0]
    _ ≤ ‖v‖*ε := mul_le_mul_of_nonneg_left (H u hu) hv0.le
    _ = ε*‖v‖ := mul_comm _ _

variable [FiniteDimensional ℝ E]
lemma eventually_seminorm_bound_of_dense
    {ι κ : Type*} {l : Filter ι} {p : ι → Seminorm ℝ E} {q : Seminorm ℝ E}
    {K : ℝ≥0} (hp : ∀ i, LipschitzWith K (p i)) (hq : LipschitzWith K q)
    {D : κ → E} (hD : DenseRange D)
    (hc : ∀ j, Tendsto (fun i => p i (D j)) l (𝓝 (q (D j))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ v : E, |p i v-q v| ≤ ε*‖v‖ := by
  have hlim := tendsto_of_lipschitz_dense hp hq hD hc
  have h := uniformly_tendsto_of_lipschitz hp hq (isCompact_sphere (0 : E) 1)
    (fun v _ => hlim v) hε
  filter_upwards [h] with i hi v
  apply seminorm_sub_bound_of_sphere hε.le _ v
  intro w hw
  exact (hi w (by simpa only [mem_sphere,dist_zero_right] using hw)).le

variable {X : Type*} [MetricSpace X]

def HasTwoPointMetricDifferential (f : E → X) (p : Seminorm ℝ E)
    (s : Set E) (x : E) : Prop :=
  (fun q : E × E => dist (f q.1) (f q.2) - p (q.1 - q.2)) =o[𝓝[s ×ˢ s] (x, x)]
    (fun q : E × E => ‖q.1 - x‖ + ‖q.2 - x‖)

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma hasTwoPointMetricDifferential_of_uniformModulus
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s) :
    HasTwoPointMetricDifferential f (metricSeminorm f x) s x := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨N,hN⟩ := (eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) (ε/2) (half_pos hε)))
  have hNN (y : E) (hy : y ∈ s) : metricErrorModulus f (r N) y < ε/2 := by
    have h := hN N le_rfl y hy
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using h
  have hfst : Tendsto (fun q : E × E => q.1) (𝓝[s ×ˢ s] (x,x)) (𝓝[s] x) :=
    continuous_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hq => hq.1)
  have hnear : ∀ᶠ q : E × E in 𝓝[s ×ˢ s] (x,x), ‖q.2-q.1‖ < r N := by
    have ht : Tendsto (fun q : E × E => ‖q.2-q.1‖) (𝓝[s ×ˢ s] (x,x)) (𝓝 0) := by
      simpa using ((continuous_snd.sub continuous_fst).norm.continuousWithinAt.tendsto (s := s ×ˢ s) (x := (x,x)))
    exact (tendsto_order.1 ht).2 _ (hr N)
  filter_upwards [hfst.eventually hp,hnear,self_mem_nhdsWithin] with q hqp hqr hqs
  have he₁ := metricErrorModulus_bound hf q.1 (q.2-q.1) hqr
  have he₂ := hqp (q.2-q.1)
  have hm := hNN q.1 hqs.1
  have ht : ‖q.2-q.1‖ ≤ ‖q.1-x‖+‖q.2-x‖ := by
    calc ‖q.2-q.1‖ = ‖(q.2-x)-(q.1-x)‖ := by congr 1; abel
      _ ≤ ‖q.2-x‖+‖q.1-x‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have he : |dist (f q.1) (f q.2)-metricSeminorm f x (q.1-q.2)| ≤
      ε*(‖q.1-x‖+‖q.2-x‖) := by
    have hpneg : metricSeminorm f x (q.1-q.2) = metricSeminorm f x (q.2-q.1) := by
      rw [←neg_sub q.2 q.1,map_neg_eq_map]
    rw [hpneg,dist_comm]
    calc |dist (f q.2) (f q.1)-metricSeminorm f x (q.2-q.1)| ≤
          |dist (f q.2) (f q.1)-metricSeminorm f q.1 (q.2-q.1)| +
            |metricSeminorm f q.1 (q.2-q.1)-metricSeminorm f x (q.2-q.1)| := abs_sub_le _ _ _
      _ ≤ metricErrorModulus f (r N) q.1 * ‖q.2-q.1‖ + ε/2*‖q.2-q.1‖ := by
        apply add_le_add _ he₂
        simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
      _ ≤ ε*‖q.2-q.1‖ := by nlinarith [norm_nonneg (q.2-q.1)]
      _ ≤ ε*(‖q.1-x‖+‖q.2-x‖) := mul_le_mul_of_nonneg_left ht hε.le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using he

end SharpIntegralFillings.MetricDifferentiation

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
