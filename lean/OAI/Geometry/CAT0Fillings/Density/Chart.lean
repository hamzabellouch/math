import Mathlib
import OAI.Geometry.CAT0Fillings.Density.RadialEstimate

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma cutoff_mass_upper (o : X) {ε ell : ℝ} (hε : 0 < ε) (hell : 0 < ell)
    (hμ : MassMeasure.currentMassMeasure hT {x | dist o x = ε} = 0)
    (hrad : ell*q.radialVariation o (fun x => inverseSquareCutoff ε (dist o x)) ≤
      q.sweptMass o (fun x => inverseSquareCutoff ε (dist o x))) :
    (2*ell-ε)*(MassMeasure.currentMassMeasure hT).real (Metric.ball o ε) ≤
      ε^2/(8*ell)*mass T := by
  classical
  let g : X → ℝ := fun x => inverseSquareCutoff ε (dist o x)
  have hg : LipschitzWith ((2/ε).toNNReal*1) g :=
    (inverseSquareCutoff_lipschitz hε).comp (LipschitzWith.dist_right o)
  have hg0 : ∀ x, 0 ≤ g x := fun x => inverseSquareCutoff_nonneg _
  let w : X → ℝ := fun x => (if dist o x < ε then 2*ell-ε else 0)-ε^2/(8*ell)
  have hw : Measurable w :=
    ((measurable_const.piecewise (measurableSet_lt (continuous_const.dist continuous_id).measurable
      measurable_const) measurable_const).sub measurable_const)
  have hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B := by
    refine ⟨|2*ell-ε|+|ε^2/(8*ell)|,fun x => ?_⟩
    dsimp only [w]
    split_ifs
    · exact abs_sub _ _
    · simpa only [zero_sub,abs_neg] using le_add_of_nonneg_left (abs_nonneg (2*ell-ε))
  let V (i : ℕ) := q.radialVariationChart o g i
  let W (i : ℕ) := ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).sweptWeight (q.field i) o g z ∂volume.restrict (q.chart i).domain
  have hW := q.swept_integrable_summable o hg hg0
  have hV := (q.spatialMass_first_variation o hg).1
  have hchart (i : ℕ) : (∫ z, q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) ≤ ell*V i-W i := by
    dsimp only [V,W]
    rw [q.radialVariationChart_cutoff o i hε hμ,←integral_const_mul,←integral_sub
      ((q.cutoff_weight_integrable o i hε).const_mul ell) (hW.1 i)]
    apply integral_mono_ae (q.weighted_density_integrable_borel i hw hwb)
      (((q.cutoff_weight_integrable o i hε).const_mul ell).sub (hW.1 i))
    filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_radialNormSq_bounds o i] with z hz ha
    have hin := cutoff_pointwise_estimate hε hell (dist_nonneg (x := o)
      (y := (q.chart i).paramExtended z)) ha
    have h := mul_le_mul_of_nonneg_left hin (q.density_nonneg i z)
    have hs (f : X → ℝ) : (q.chart i).scalar f z = f ((q.chart i).paramExtended z) := by
      rw [IntegerChart.scalar_eq _ hz]
      simp only [IntegerChart.paramExtended,dite_eq_left hz]
    dsimp only [w,g] at h ⊢
    simp only [Pi.sub_apply,IntegerChart.sweptWeight,hs,density,gram,radialNormSq] at h ⊢
    convert h using 1
    ring
  have hint : (∫ x, w x ∂MassMeasure.currentMassMeasure hT) ≤ 0 := by
    rw [q.integral_massMeasure_borel hw hwb]
    calc
      _ ≤ ∑' i, (ell*V i-W i) := (q.weighted_density_summable_borel hw hwb).tsum_le_tsum
        hchart ((hV.mul_left ell).sub hW.2)
      _ = ell*q.radialVariation o g-q.sweptMass o g := by
        rw [(hV.mul_left ell).tsum_sub hW.2,tsum_mul_left]
        rfl
      _ ≤ 0 := sub_nonpos.mpr hrad
  have heq : w = fun x => (Metric.ball o ε).indicator (fun _ => 2*ell-ε) x-ε^2/(8*ell) := by
    funext x
    simp only [w,indicator,Metric.mem_ball,dist_comm]
  rw [heq,integral_sub ((integrable_const (2*ell-ε)).indicator measurableSet_ball)
    (integrable_const _),integral_indicator measurableSet_ball,integral_const,integral_const] at hint
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at hint
  change (MassMeasure.currentMassMeasure hT).real (Metric.ball o ε)*(2*ell-ε)-
    (MassMeasure.currentMassMeasure hT).real univ*(ε^2/(8*ell)) ≤ 0 at hint
  rw [MassMeasure.currentMassMeasure_total hT] at hint
  nlinarith

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma exists_euclidean_density_point_two {s : Set (Euc 2)} (hs : MeasurableSet s)
    (hs0 : volume s ≠ 0) :
    ∃ u ∈ s, Tendsto (fun r : ℝ => volume.real (s ∩ closedBall u r)/r^2)
      (𝓝[>] 0) (𝓝 Real.pi) := by
  obtain ⟨u,hu,hd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hs0
    (ae_restrict_of_ae (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hs))
  simp only [indicator_of_mem hu,Pi.one_apply] at hd
  refine ⟨u,hu,?_⟩
  have hreal := (ENNReal.continuousAt_toReal (by norm_num : (1:ℝ≥0∞) ≠ ∞)).tendsto.comp hd
  simp only [ENNReal.toReal_one] at hreal
  have hlim := hreal.mul_const Real.pi
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Function.comp_apply,ENNReal.toReal_div,measureReal_def,EuclideanSpace.volume_closedBall_fin_two,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofReal Real.pi_pos.le]
  field_simp [ne_of_gt (show (0:ℝ) < r from hr),Real.pi_ne_zero]

lemma exists_lipschitz_chart_density {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set (Euc 2)} (hs : MeasurableSet s) (hs0 : volume s ≠ 0)
    {f : Euc 2 → X} (hf : Measurable f) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hLip : ∀ y ∈ s, ∀ z ∈ s, dist (f y) (f z) ≤ b*dist y z)
    (hdom : Measure.map f (volume.restrict s) ≤ ENNReal.ofReal a • μ) :
    ∃ o : X, ∀ v : ℝ, b < v → ∀ d : ℝ, d < Real.pi →
      ∀ᶠ r in 𝓝[>] (0:ℝ), d*(r/v)^2 ≤ a*μ.real (ball o r) := by
  obtain ⟨u,hu,hd⟩ := exists_euclidean_density_point_two hs hs0
  refine ⟨f u,fun v hv d hdπ => ?_⟩
  have hv0 : 0 < v := hb.trans_lt hv
  have ht : Tendsto (fun r : ℝ => r/v) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using ((tendsto_id.div_const v : Tendsto (fun r : ℝ => r/v) (𝓝 0) (𝓝 (0/v))).mono_left nhdsWithin_le_nhds),?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr using div_pos hr hv0
  have hlimit := hd.comp ht
  have hevent := hlimit.eventually (eventually_gt_nhds hdπ)
  filter_upwards [self_mem_nhdsWithin,hevent] with r hr hrd
  have hr0 : 0 < r/v := div_pos hr hv0
  have hincl : s ∩ closedBall u (r/v) ⊆ f ⁻¹' ball (f u) r ∩ s := by
    intro z hz
    refine ⟨?_,hz.1⟩
    change dist (f z) (f u) < r
    have hh := (hLip z hz.1 u hu).trans (mul_le_mul_of_nonneg_left hz.2 hb)
    exact hh.trans_lt (by have := mul_lt_mul_of_pos_right hv hr0; nlinarith [div_mul_cancel₀ r hv0.ne'])
  have hbnd : volume (s ∩ closedBall u (r/v)) ≤ ENNReal.ofReal a*μ (ball (f u) r) := by
    calc
      _ ≤ (volume.restrict s) (f ⁻¹' ball (f u) r) := by
        rw [Measure.restrict_apply (hf measurableSet_ball)]
        exact measure_mono hincl
      _ = (Measure.map f (volume.restrict s)) (ball (f u) r) :=
        (Measure.map_apply hf measurableSet_ball).symm
      _ ≤ _ := hdom _
  have hfin : ENNReal.ofReal a*μ (ball (f u) r) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hrb := ENNReal.toReal_mono hfin hbnd
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha.le] at hrb
  change volume.real (s ∩ closedBall u (r/v)) ≤ a*μ.real (ball (f u) r) at hrb
  exact ((lt_div_iff₀ (sq_pos_of_pos hr0)).mp hrd).le.trans hrb

end CAT0Fillings
end

end OAI
