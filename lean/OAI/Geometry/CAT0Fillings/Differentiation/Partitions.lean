import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.LargePieces

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

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
lemma exists_radius_uniform_metric_error
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤ ε*‖y-z‖ := by
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨a,ha,hap⟩ := Metric.mem_nhdsWithin_iff.1 hp
  obtain ⟨N,hN⟩ := (eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (ε/2) (half_pos hε)))
  have hNN := hN N le_rfl
  refine ⟨min a (r N/3), lt_min ha (div_pos (hr N) (by norm_num)), ?_⟩
  intro y hy z hz
  have hyp : ∀ v : E, |metricSeminorm f y v-metricSeminorm f x v| ≤ ε/2*‖v‖ :=
    hap ⟨show dist y x < a from lt_of_lt_of_le hy.2 (min_le_left _ _),hy.1⟩
  have hyz : ‖z-y‖ < r N := by
    have h₁ : ‖y-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hy.2) (min_le_right _ _)
    have h₂ : ‖z-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hz.2) (min_le_right _ _)
    have h₃ : ‖z-y‖ ≤ ‖z-x‖+‖y-x‖ := by
      calc ‖z-y‖ = ‖(z-x)-(y-x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [hr N]
  have he₁ := metricErrorModulus_bound hf y (z-y) hyz
  have he₂ := hyp (z-y)
  have hm : metricErrorModulus f (r N) y < ε/2 := by
    have hm := hNN y hy.1
    simpa only [dist_zero_left,Real.norm_eq_abs,
      abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using hm
  have hpneg : metricSeminorm f x (y-z) = metricSeminorm f x (z-y) := by
    rw [←neg_sub z y,map_neg_eq_map]
  rw [hpneg,dist_comm,norm_sub_rev]
  calc |dist (f z) (f y)-metricSeminorm f x (z-y)| ≤
        |dist (f z) (f y)-metricSeminorm f y (z-y)| +
          |metricSeminorm f y (z-y)-metricSeminorm f x (z-y)| := abs_sub_le _ _ _
    _ ≤ metricErrorModulus f (r N) y*‖z-y‖+ε/2*‖z-y‖ := by
      apply add_le_add _ he₂
      simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
    _ ≤ ε*‖z-y‖ := by nlinarith [norm_nonneg (z-y)]

lemma exists_radius_nearIsometric
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      (1-ε)*metricSeminorm f x (y-z) ≤ dist (f y) (f z) ∧
      dist (f y) (f z) ≤ (1+ε)*metricSeminorm f x (y-z) := by
  obtain ⟨δ,hδ,H⟩ := exists_radius_uniform_metric_error hf hc hr hu (div_pos hε hA)
  refine ⟨δ,hδ,?_⟩
  intro y hy z hz
  have he : |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤
      ε*metricSeminorm f x (y-z) := by
    apply (H y hy z hz).trans
    calc (ε/A)*‖y-z‖ ≤ (ε/A)*(A*metricSeminorm f x (y-z)) :=
          mul_le_mul_of_nonneg_left (hbound _) (div_pos hε hA).le
      _ = ε*metricSeminorm f x (y-z) := by field_simp
  obtain ⟨hl,hr⟩ := abs_le.1 he
  constructor <;> linarith

lemma exists_nearIsometric_partition
    [MeasurableSpace E] [BorelSpace E] {s : Set E} [Nonempty s]
    (hs : MeasurableSet s) (hf : LipschitzWith K f)
    (hc : ∀ x ∈ s, ∀ j : ℕ, ContinuousWithinAt
      (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → s) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (⋃ i, t i) = s ∧ ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  choose δ hδ hlocal using fun x : s =>
    exists_radius_nearIsometric hf (hc x x.property) hr hu hA (hbound x x.property) hε
  obtain ⟨c,hcvr⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    (fun x : s => ball (x : E) (δ x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x,hx⟩,mem_ball_self (hδ ⟨x,hx⟩)⟩)
  let t : ℕ → Set E := fun i => s ∩ ball (c i : E) (δ (c i))
  refine ⟨c,disjointed t, fun i => MeasurableSet.disjointed
    (fun j => hs.inter isOpen_ball.measurableSet) i,disjoint_disjointed t,?_,?_⟩
  · rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset (fun i => inter_subset_left)
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.1 (hcvr hx)
      exact mem_iUnion.2 ⟨i,hx,hi⟩
  · intro i y hy z hz
    exact hlocal (c i) y (disjointed_le t i hy) z (disjointed_le t i hz)

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_nearIsometric_partition
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  let r : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  have H (j : ℕ) := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x i => metricSeminorm f x (denseSeq E i)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun i => measurable_metricErrorModulus hf (r i)) hc (hr j)
  choose u hus hum hμu hcu huu using H
  have HP (j : ℕ) : ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (⋃ i, t i) = u j ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
    by_cases hne : (u j).Nonempty
    · let _ : Nonempty (u j) := hne.to_subtype
      obtain ⟨c,t,ht,_,htu,hineq⟩ := exists_nearIsometric_partition (hum j) hf
        (fun x hx i => (continuousOn_pi.1 (hcu j) i) x hx) hr (huu j) hA
        (fun x hx => hbound x (hus j hx)) hε
      exact ⟨fun i => c i,t,ht,htu,fun i _ => hus j (c i).property,hineq⟩
    · refine ⟨fun _ => 0,fun _ => ∅,fun _ => MeasurableSet.empty,?_,?_,?_⟩
      · simp [not_nonempty_iff_eq_empty.mp hne]
      · simp
      · simp
  choose c t htm htunion hcs htineq using HP
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let T : ℕ → Set E := fun i => t (e i).1 (e i).2
  have hTunion : (⋃ i, T i) = ⋃ j, u j := by
    ext x
    simp only [T,mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,htunion (e i).1 ▸ mem_iUnion.2 ⟨(e i).2,hi⟩⟩
    · rintro ⟨j,hj⟩
      obtain ⟨i,hi⟩ := mem_iUnion.1 ((htunion j).symm ▸ hj)
      refine ⟨e.symm (j,i),?_⟩
      simpa using hi
  have hu0 : μ (s \ ⋃ j, u j) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (by simpa using ENNReal.tendsto_ofReal hr0)
    filter_upwards [] with j
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion u j))).trans (hμu j)
  refine ⟨fun i => c (e i).1 (e i).2,disjointed T,
    fun i => MeasurableSet.disjointed (fun k => htm (e k).1 (e k).2) i,
    ?_,disjoint_disjointed T,?_,?_,?_⟩
  · intro i x hx
    apply hus (e i).1
    rw [←htunion (e i).1]
    exact mem_iUnion.2 ⟨(e i).2,disjointed_le T i hx⟩
  · rw [iUnion_disjointed,hTunion]
    exact hu0
  · intro i hi
    exact hcs _ _ (hi.mono (disjointed_le T i))
  · intro i y hy z hz
    exact htineq _ _ y (disjointed_le T i hy) z (disjointed_le T i hz)

end CAT0Fillings.MetricDifferentiation
end

end OAI
