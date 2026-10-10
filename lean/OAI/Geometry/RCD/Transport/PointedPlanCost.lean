import OAI.Geometry.RCD.Coordinates.QuadraticMetricError
import OAI.Analysis.RCDHeat.DynamicalPlan
import OAI.Geometry.RCD.Metric.EuclideanPairCost

namespace OAI

/-! # Exact quadratic-cost transfer through the prescribed approximation maps -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem pointed_plan_cost_error {n : ℕ} {p : X} {r S ρ ε : ℝ}
    (hr : 0<r) (_hρ : 0≤ρ) (hρS : ρ≤S) (hε : 0≤ε)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v) (hm : Measurable v)
    (P : ProbabilityMeasure C(Time,X))
    (h0 : ∀ᵐ γ ∂(P : Measure C(Time,X)), dist (γ 0) p≤ρ*r)
    (h1 : ∀ᵐ γ ∂(P : Measure C(Time,X)), dist (γ 1) p≤ρ*r) :
    |(∫ γ : C(Time,X), dist (v (γ 0)) (v (γ 1))^2 ∂(P : Measure C(Time,X)))-
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r)^2 ∂(P : Measure C(Time,X)))|≤ε*(4*ρ+ε) := by
  have hd : ∀ᵐ γ ∂(P : Measure C(Time,X)), dist (γ 0) (γ 1)/r≤2*ρ := by
    filter_upwards [h0,h1] with γ hg0 hg1
    apply (div_le_iff₀ hr).mpr
    have hh := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hh
    linarith
  have hsmall (γ : C(Time,X)) (j : Time) (hj : dist (γ j) p≤ρ*r) : dist (γ j) p≤S*r :=
    hj.trans (mul_le_mul_of_nonneg_right hρS hr.le)
  have he : ∀ᵐ γ ∂(P : Measure C(Time,X)),
      |dist (v (γ 0)) (v (γ 1))^2-(dist (γ 0) (γ 1)/r)^2|≤ε*(4*ρ+ε) := by
    filter_upwards [h0,h1,hd] with γ hg0 hg1 hg
    have hh := pointed_square_distance_error hr hε hv (hsmall γ 0 hg0) (hsmall γ 1 hg1) hg
    have heq : 2*(2*ρ)=4*ρ := by ring
    simpa only [heq] using hh
  have ht : ∀ᵐ γ ∂(P : Measure C(Time,X)), dist (v (γ 0)) (v (γ 1))≤2*ρ+ε := by
    filter_upwards [h0,h1,hd] with γ hg0 hg1 hg
    have hh := (abs_le.mp (hv.2.1 _ _ (hsmall γ 0 hg0) (hsmall γ 1 hg1))).2
    linarith
  have his : Integrable (fun γ : C(Time,X) => (dist (γ 0) (γ 1)/r)^2) (P : Measure C(Time,X)) :=
    (integrable_const ((2*ρ)^2)).mono'
      (((((continuous_eval_const 0).dist (continuous_eval_const 1)).measurable).div_const r).pow_const 2).aestronglyMeasurable
      (hd.mono fun γ hg => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (dist (γ 0) (γ 1)/r))] using
          pow_le_pow_left₀ (div_nonneg dist_nonneg hr.le) hg 2)
  have hit : Integrable (fun γ : C(Time,X) => dist (v (γ 0)) (v (γ 1))^2) (P : Measure C(Time,X)) :=
    (integrable_const ((2*ρ+ε)^2)).mono'
      ((((hm.comp (measurable_path_eval 0)).dist (hm.comp (measurable_path_eval 1))).pow_const 2).aestronglyMeasurable)
      (ht.mono fun γ hg => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (dist (v (γ 0)) (v (γ 1))))] using
          pow_le_pow_left₀ dist_nonneg hg 2)
  rw [← integral_sub hit his]
  have hh := norm_integral_le_of_norm_le_const (μ := (P : Measure C(Time,X)))
    (f := fun γ => dist (v (γ 0)) (v (γ 1))^2-(dist (γ 0) (γ 1)/r)^2)
    (by simpa only [Real.norm_eq_abs] using he)
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using hh

/-- The actual rescaled source costs converge to the cost of the same limiting
endpoint law; no optimality or continuity of the approximation maps is needed. -/
theorem pointed_plan_cost_tendsto {n : ℕ} {S ρ B : ℝ}
    (hρ : 0≤ρ) (hρS : ρ≤S) (hB : 0≤B)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k)
    {Q : ProbabilityMeasure (Euclidean n × Euclidean n)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q))
    (hbs : ∀ k, ∀ᵐ z ∂((P k).map (fun γ => (v k (γ 0),v k (γ 1))) :
        Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B)
    (hb : ∀ᵐ z ∂(Q : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
    Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r k)^2
      ∂(P k : Measure C(Time,X))) atTop
      (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))) := by
  have ht := bounded_pair_cost_tendsto hB _ Q hpair hbs hb
  have heq (k : ℕ) :
      (∫ z, dist z.1 z.2^2 ∂((P k).map (fun γ => (v k (γ 0),v k (γ 1))) :
        Measure (Euclidean n × Euclidean n)))=
      ∫ γ, dist (v k (γ 0)) (v k (γ 1))^2 ∂(P k : Measure C(Time,X)) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map]
    · exact (((hm k).comp (measurable_path_eval 0)).prodMk
        ((hm k).comp (measurable_path_eval 1))).aemeasurable
    · exact ((continuous_fst.dist continuous_snd).pow 2).aestronglyMeasurable
  simp_rw [heq] at ht
  apply ht.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun k => by simpa only [Real.dist_eq] using
      pointed_plan_cost_error (hr k) hρ hρS (hε k) (hv k) (hm k) (P k) (h0 k) (h1 k))
  simpa only [zero_mul] using hεlim.mul (hεlim.const_add (4*ρ))

end RegularPointCoordinates

end

end OAI
