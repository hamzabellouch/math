import OAI.Geometry.RCD.Coordinates.IterationLimit
import OAI.Geometry.RCD.Coordinates.OpenLimitChart

namespace OAI

/-! # Direct openness of the analytic coordinate limit

The frozen metrics increase, and the zeroth iterate is the identity.
Consequently every finite iterate has the same lower differential bound.
The uniform tail bound then passes the open-image property to the limit.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {n : ℕ}

/-- The lower bound on the derivative is uniform in the iteration index. -/
theorem FiniteIterationControl.inverse_differential_bound
    {Ω : Set (Euclidean n)} {r0 T F B epsilon : ℝ}
    {d : AnalyticIterationData Ω r0 T F B epsilon}
    (hc : FiniteIterationControl d) (hT : 1 ≤ T)
    (i : ℕ) (x : Euclidean n) (hx : x ∈ Ω) (v : Euclidean n) :
    ‖v‖ ≤ (4*T)*‖fderiv ℝ (metricIterate d.correction i) x v‖ := by
  have hA : 0 < 4*T := by linarith
  have hzero := (hc.metric 0 x hx v).2
  simp only [metricIterate_zero, fderiv_id, ContinuousLinearMap.id_apply] at hzero
  have hmono : ‖d.frozen 0 x v‖ ≤ ‖d.frozen i x v‖ :=
    monotone_nat_of_le_succ (fun j => d.frozen_mono j x hx v) (Nat.zero_le i)
  have hlower := (hc.metric i x hx v).1
  have hmul := mul_le_mul_of_nonneg_left hlower hA.le
  rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at hmul
  have hs : ‖v‖^2 ≤ ((4*T)*‖fderiv ℝ (metricIterate d.correction i) x v‖)^2 := by
    calc
      _ ≤ (4*T)*‖d.frozen 0 x v‖^2 := hzero
      _ ≤ (4*T)*‖d.frozen i x v‖^2 := by gcongr
      _ ≤ (4*T)*((4*T)*‖fderiv ℝ (metricIterate d.correction i) x v‖^2) :=
        mul_le_mul_of_nonneg_left hmul hA.le
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA.le (norm_nonneg _))).mp hs

/-- The analytic iteration produces an open limit without a separate
invariance-of-domain premise. -/
theorem exists_analytic_iteration_open_limit_chart
    {X : Type*} [MetricSpace X] {T F B G : ℝ}
    (hT : 1 ≤ T) (hF : 1 ≤ F) (hB : 1 ≤ B) (hG : 1 ≤ G) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (p : X) (Ω : Set (Euclidean n)), IsOpen Ω →
      ∀ (U : Set X), IsOpen U → p ∈ U →
      ∀ (O : Set (Euclidean n)), IsOpen O → O ⊆ Ω → ∀ u : U ≃ₜ O,
      ∀ (r0 : ℝ), 0 < r0 → ∀ d : AnalyticIterationData Ω r0 T F B epsilon,
      IterationPairGeometry (fun x : U => (u x : Euclidean n)) Ω d.frozen r0 T B G →
      HasOpenBilipschitzChart n p := by
  obtain ⟨delta, hdelta, hdelta1, hcontrol⟩ :=
    exists_analytic_metric_iteration (E := Euclidean n) hT hF hB
  let q := iterationChartRatio T G
  let L := iterationPairMultiplier T B G
  have hq : 1 ≤ q := by dsimp [q, iterationChartRatio]; nlinarith
  have hq0 : 0 < q := by linarith
  have hA0 : 0 < 4*T := by linarith
  have hF0 : 0 < F := by linarith
  have hL0 : 0 < L := by dsimp [L, iterationPairMultiplier, iterationChartRatio]; positivity
  let epsilon := min delta (64*q*(4*T)*F*L)⁻¹
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hed : epsilon ≤ delta := min_le_left _ _
  have hes : epsilon ≤ (64*q*(4*T)*F*L)⁻¹ := min_le_right _ _
  have hsmall : 8*(4*T)*F*epsilon*L ≤ (8*q)⁻¹ := by
    calc
      _ ≤ 8*(4*T)*F*(64*q*(4*T)*F*L)⁻¹*L := by gcongr
      _ = _ := by field_simp; ring
  refine ⟨epsilon, hepsilon, hed.trans hdelta1, ?_⟩
  intro p Ω hΩ U hU hp O hO hOΩ u r0 hr0 d hgeometry
  let d' := d.withLargerParameter hr0 (by linarith : 0 ≤ F) (by linarith : 0 < B) hed
  have hc : FiniteIterationControl d := by
    constructor
    · intro i x hx m
      exact (hcontrol Ω hΩ r0 hr0 d' i x hx).1 m
    · intro i x hx xi
      exact (hcontrol Ω hΩ r0 hr0 d' i x hx).2.1 xi
    · intro i x hx
      have hh := (hcontrol Ω hΩ r0 hr0 d' i x hx).2.2 2 (by norm_num)
      change ‖iteratedFDeriv ℝ 2 (normalizedCoordinates (iterationRadius r0 i)
        (d.frozen i x) x (metricIterate d.correction i)) 0‖ ≤
          B^(2-1)*((2:ℕ).factorial:ℝ)^3 at hh
      norm_num at hh
      nlinarith
  obtain ⟨H,hlim,hbound⟩ := exists_limit_dist_bounds_of_analytic_iteration d hT hF hB hG
    hr0 hepsilon.le hc (fun x : U => (u x : Euclidean n)) (fun x => hOΩ (u x).property)
    hgeometry hsmall
  let C := (4*T)*F*epsilon*r0
  have hstep (i : ℕ) (x : U) :
      dist (metricIterate d.correction i (u x))
        (metricIterate d.correction (i+1) (u x)) ≤ C*(1/2:ℝ)^i := by
    have hh := metricIterate_step_le d hT (by linarith) hepsilon.le hr0 hc i
      (u x) (hOΩ (u x).property)
    convert hh using 1
    dsimp [C, iterationRadius]
    rw [one_div_pow]
    ring
  apply hasOpenBilipschitzChart_of_coercive_limit hU hp hO u hA0
    (show 1 ≤ 4*iterationChartRatio T G by change 1≤4*q; linarith)
    (f := metricIterate d.correction) (H := H)
    (e := fun i => C*(1/2:ℝ)^i/(1-1/2))
  · intro i z hz
    exact (hc.smooth i z (hOΩ hz) 1).differentiableAt (by norm_num)
  · intro i z hz v
    exact hc.inverse_differential_bound hT i z (hOΩ hz) v
  · have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).const_mul C
    simpa using hh.div_const (1-1/2)
  · intro i x
    exact dist_le_of_le_geometric_of_tendsto (1/2:ℝ) C (by norm_num)
      (fun j => hstep j x) (hlim x) i
  · exact hbound

end RegularPointCoordinates

end

end OAI
