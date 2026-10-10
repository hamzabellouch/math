import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Differentiability
import OAI.Geometry.IntegralFillings.Differentiation.HilbertCharts

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma scalar_derivative_bound_of_metric_differential
    {s : Set E} {x : E} {F r : E → ℝ} {p : Seminorm ℝ E} {ℓ : E →L[ℝ] ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hF : HasFDerivWithinAt F ℓ s x)
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {K : ℝ} (hbound : ∀ y ∈ s, |F y-F x| ≤ K*r y) (v : E) :
    |ℓ v| ≤ K*p v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hl : Tendsto (fun j => ‖c j‖ * |F (x+d j)-F x|) atTop (𝓝 |ℓ v|) := by
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_mul] using (hF.lim hd₀ hd hcd).norm
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  apply le_of_tendsto_of_tendsto hl (hlim.const_mul K)
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [mul_left_comm] using hh

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.scalar_bound
    {s : Set E} {f : s → X} {p : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun t => μ (s ∩ closedBall (x : E) t) / μ (closedBall (x : E) t))
      (𝓝[>] 0) (𝓝 1))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F : E → ℝ} (hF : ∀ y : s, F y = u (f y))
    {ℓ : E →L[ℝ] ℝ} (hD : HasFDerivWithinAt F ℓ s x) (v : E) :
    |ℓ v| ≤ (K : ℝ)*p v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property, Asymptotics.isLittleO_map]
    change (fun y : s => dist (f y) (f x)-p ((y : E)-(x : E))) =o[𝓝 x]
      (fun y : s => (y : E)-(x : E)) at h
    convert h using 1
    · ext y
      simp only [Function.comp_apply,r,dite_eq_left y.property,Subtype.coe_eta]
    · rfl
  apply scalar_derivative_bound_of_metric_differential μ hx hD hr (v := v)
  intro y hy
  have hh := hu.dist_le_mul (f ⟨y,hy⟩) (f x)
  rw [Real.dist_eq, ←hF ⟨y,hy⟩, ←hF x] at hh
  simpa only [r,dite_eq_left hy] using hh

noncomputable def scalarOn {s : Set E} (f : s → X) (u : X → ℝ) (z : E) : ℝ :=
  by classical exact if hz : z ∈ s then u (f ⟨z,hz⟩) else 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scalarOn_lipschitzOn {s : Set E} {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith J f) {u : X → ℝ} (hu : LipschitzWith K u) :
    LipschitzOnWith (K*J) (scalarOn f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simpa only [scalarOn,dite_eq_left ha,dite_eq_left hb,Function.comp_apply,Subtype.dist_eq] using
    (hu.comp hf).dist_le_mul ⟨a,ha⟩ ⟨b,hb⟩

lemma ae_scalarOn_derivative_bound {s : Set E} (hs : MeasurableSet s) {f : s → X}
    {J : ℝ≥0} (hf : LipschitzWith J f) {p : E → Seminorm ℝ E}
    (hd : ∀ᵐ x ∂μ.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ x ∂μ.restrict s, ∀ v,
      |fderivWithin ℝ (scalarOn f u) s x v| ≤ (K : ℝ)*p x v := by
  obtain ⟨F,hF,heq⟩ := (scalarOn_lipschitzOn hf hu).extend_real
  have haediff := hF.ae_differentiableAt (μ := μ)
  filter_upwards [hd,ae_restrict_mem hs,Besicovitch.ae_tendsto_measure_inter_div μ s,
    haediff.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxs hxd hFx
  have hD : HasFDerivWithinAt (scalarOn f u) (fderivWithin ℝ (scalarOn f u) s x) s x := by
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact hFx.differentiableWithinAt.congr heq (heq hxs)
  intro v
  apply (hx hxs).scalar_bound μ hxd hu _ hD v
  intro y
  simp only [scalarOn,dite_eq_left y.property,Subtype.coe_eta]
end SharpIntegralFillings.MetricDifferentiation

open Set MeasureTheory
open scoped RealInnerProductSpace

end

end OAI
