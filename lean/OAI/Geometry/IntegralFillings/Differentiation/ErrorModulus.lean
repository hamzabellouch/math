import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.Centered

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
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
omit [FiniteDimensional ℝ E] in
lemma measurable_metricSeminorm_apply (hf : LipschitzWith K f) (v : E) :
    Measurable (fun x => metricSeminorm f x v) := by
  simp only [metricSeminorm_apply hf]
  exact Measurable.iSup (fun q => (measurable_fderiv_apply_const ℝ (scalarCoordinate f q) v).abs)

noncomputable def metricErrorTerm (f : E → X) (r : ℝ) (q : ℕ) (x : E) : ℝ :=
  if 0 < ‖denseSeq E q‖ ∧ ‖denseSeq E q‖ ≤ r then
    |dist (f (x + denseSeq E q)) (f x) - metricSeminorm f x (denseSeq E q)| / ‖denseSeq E q‖
  else 0

noncomputable def metricErrorModulus (f : E → X) (r : ℝ) (x : E) : ℝ :=
  ⨆ q : ℕ, metricErrorTerm f r q x

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_nonneg (r : ℝ) (q : ℕ) (x : E) :
    0 ≤ metricErrorTerm f r q x := by
  dsimp [metricErrorTerm]
  split_ifs
  · positivity
  · rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_le (hf : LipschitzWith K f) (r : ℝ) (q : ℕ) (x : E) :
    metricErrorTerm f r q x ≤ 2*(K : ℝ) := by
  dsimp [metricErrorTerm]
  split_ifs with h
  · apply (div_le_iff₀ h.1).mpr
    have hd : dist (f (x+denseSeq E q)) (f x) ≤ (K : ℝ)*‖denseSeq E q‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le_mul (x+denseSeq E q) x
    have hp := metricSeminorm_le hf x (denseSeq E q)
    have hp0 := apply_nonneg (metricSeminorm f x) (denseSeq E q)
    have hd0 := dist_nonneg (x := f (x+denseSeq E q)) (y := f x)
    rw [abs_le]
    constructor <;> nlinarith
  · positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma bddAbove_metricErrorTerm (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    BddAbove (range (fun q => metricErrorTerm f r q x)) :=
  ⟨2*(K : ℝ), by rintro _ ⟨q,rfl⟩; exact metricErrorTerm_le hf r q x⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_nonneg (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    0 ≤ metricErrorModulus f r x :=
  (metricErrorTerm_nonneg r 0 x).trans (le_ciSup (bddAbove_metricErrorTerm hf r x) 0)

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    metricErrorModulus f r x ≤ 2*(K : ℝ) :=
  ciSup_le (fun q => metricErrorTerm_le hf r q x)

lemma measurable_metricErrorModulus (hf : LipschitzWith K f) (r : ℝ) :
    Measurable (metricErrorModulus f r) := by
  change Measurable (fun x => ⨆ q : ℕ, metricErrorTerm f r q x)
  apply Measurable.iSup
  intro q
  change Measurable (fun x => metricErrorTerm f r q x)
  unfold metricErrorTerm
  split_ifs
  · exact (((hf.continuous.comp (continuous_id.add continuous_const)).dist hf.continuous).measurable.sub
      (measurable_metricSeminorm_apply hf _)).abs.div_const _
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le_of_bound (_hf : LipschitzWith K f) {r ε : ℝ} {x : E}
    (hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ ≤ r → |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ ε*‖v‖) :
    metricErrorModulus f r x ≤ ε := by
  apply ciSup_le
  intro q
  dsimp [metricErrorTerm]
  split_ifs with h
  · exact (div_le_iff₀ h.1).mpr (H _ h.2)
  · exact hε

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_tendsto_zero (hf : LipschitzWith K f) {x : E}
    (hx : HasCenteredMetricDifferential f (metricSeminorm f x) x)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (metricErrorModulus_nonneg hf _ _))
  · intro ε hε
    have hxε := hx.bound (half_pos hε)
    obtain ⟨δ,hδ,hδx⟩ := Metric.mem_nhds_iff.mp hxε
    have hδr := (tendsto_order.1 hr).2 δ hδ
    filter_upwards [hδr] with n hn
    apply lt_of_le_of_lt (metricErrorModulus_le_of_bound hf (half_pos hε).le ?_)
      (half_lt_self hε)
    intro v hv
    have hvδ : x+v ∈ ball x δ := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hv.trans_lt hn
    simpa only [mem_ofPred_eq, add_sub_cancel_left, Real.norm_eq_abs] using hδx hvδ

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_bound (hf : LipschitzWith K f) {r : ℝ} (x v : E)
    (hv : ‖v‖ < r) :
    |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ metricErrorModulus f r x * ‖v‖ := by
  let A : Set E := {w | |dist (f (x+w)) (f x)-metricSeminorm f x w| ≤
    metricErrorModulus f r x * ‖w‖}
  have hA : IsClosed A := isClosed_le
    (((hf.continuous.comp (continuous_const.add continuous_id)).dist continuous_const).sub
      (metricSeminorm_lipschitz hf x).continuous).abs
    (continuous_const.mul continuous_norm)
  have hsub : ball (0 : E) r ∩ range (denseSeq E) ⊆ A := by
    rintro w ⟨hq,⟨q,rfl⟩⟩
    by_cases hw : denseSeq E q = 0
    · simp [A,hw]
    have hqw : 0 < ‖denseSeq E q‖ := norm_pos_iff.mpr hw
    have hqr : ‖denseSeq E q‖ ≤ r := (by simpa only [mem_ball, dist_zero_right] using hq :
      ‖denseSeq E q‖ < r).le
    have hle := le_ciSup (bddAbove_metricErrorTerm hf r x) q
    rw [metricErrorTerm, ite_eq_left ⟨hqw,hqr⟩] at hle
    exact (div_le_iff₀ hqw).mp hle
  have hvcl := (denseRange_denseSeq E).open_subset_closure_inter isOpen_ball
    (by simpa only [mem_ball, dist_zero_right] using hv : v ∈ ball (0 : E) r)
  exact hA.closure_subset_iff.mpr hsub hvcl

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
