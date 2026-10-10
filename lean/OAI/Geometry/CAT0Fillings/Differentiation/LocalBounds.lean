import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertCharts

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
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma seminorm_le_of_centered_bound {s : Set E} {x : E}
    {r : E → ℝ} {p q : Seminorm ℝ E} {B : ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (hbound : ∀ y ∈ s, r y ≤ B*q (y-x)) (v : E) : p v ≤ B*q v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
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
  have hq : Tendsto (fun j => B*(‖c j‖*q (d j))) atTop (𝓝 (B*q v)) := by
    simpa only [Function.comp_apply,map_smul_eq_mul] using
      (((seminorm_continuous_finiteDimensional q).tendsto v).comp hcd).const_mul B
  apply le_of_tendsto_of_tendsto hlim hq
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [add_sub_cancel_left,mul_left_comm] using hh

end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.seminorm_le_on_piece
    {s t : Set E} (hts : t ⊆ s) {f : s → X} {p q : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun r => μ (t ∩ closedBall (x : E) r) / μ (closedBall (x : E) r))
      (𝓝[>] 0) (𝓝 1)) {B : ℝ}
    (hb : ∀ y (hy : y ∈ t), dist (f ⟨y,hts hy⟩) (f x) ≤ B*q (y-(x : E))) :
    ∀ v : E, p v ≤ B*q v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property,Asymptotics.isLittleO_map]
    simpa only [HasCenteredMetricDifferentialWithin,Function.comp_def,r,
      dite_eq_left (Subtype.coe_prop _),Subtype.coe_eta] using h
  apply seminorm_le_of_centered_bound μ hx (hr.mono (nhdsWithin_mono _ hts))
  intro y hy
  simpa only [r,dite_eq_left (hts hy)] using hb y hy

end CAT0Fillings.MetricDifferentiation

end

end OAI
