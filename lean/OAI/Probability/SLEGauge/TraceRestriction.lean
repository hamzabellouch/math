import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.LoewnerScaling
import OAI.Probability.SLEGauge.FiniteProductLimit

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical NNReal ENNReal symmDiff
namespace SLEExactGauge.TraceRestriction

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]

 
def visited (ι : X → Y) (γ : ℝ≥0 → Y) (t : ℝ≥0) : Set X :=
  ι ⁻¹' (γ '' Icc 0 t)

omit [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma visited_mono (ι : X → Y) (γ : ℝ≥0 → Y) : Monotone (visited ι γ) := by
  intro s t hst
  exact preimage_mono (image_mono (Icc_subset_Icc_right hst))

lemma measurableSet_visited (ι : X → Y) (hι : Measurable ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) (t : ℝ≥0) :
    MeasurableSet (visited ι γ t) :=
  ((isCompact_Icc.image hγ).isClosed.measurableSet).preimage hι

 

omit [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma visited_symmDiff_subset (ι : X → Y) (γ : ℝ≥0 → Y) (s t : ℝ≥0) :
    visited ι γ s ∆ visited ι γ t ⊆ ι ⁻¹' (γ '' uIcc s t) := by
  intro x hx
  rcases hx with ⟨hxs,hxt⟩ | ⟨hxt,hxs⟩
  · rcases hxs with ⟨u,hu,he⟩
    have htu : t<u := lt_of_not_ge (fun hut => hxt ⟨u,⟨hu.1,hut⟩,he⟩)
    exact ⟨u,⟨(min_le_right s t).trans htu.le,hu.2.trans (le_max_left s t)⟩,he⟩
  · rcases hxt with ⟨u,hu,he⟩
    have hsu : s<u := lt_of_not_ge (fun hus => hxs ⟨u,⟨hu.1,hus⟩,he⟩)
    exact ⟨u,⟨(min_le_left s t).trans hsu.le,hu.2.trans (le_max_right s t)⟩,he⟩

lemma nnreal_dist_right_le {s t u : ℝ≥0} (hu : u∈uIcc s t) :
    dist u t≤dist s t := by
  apply Real.dist_right_le_of_mem_uIcc
  change min (s : ℝ) (t : ℝ)≤(u : ℝ) ∧ (u : ℝ) ≤ max (s : ℝ) (t : ℝ)
  exact ⟨hu.1,hu.2⟩

 

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma eventually_not_mem_visited_symmDiff (ι : X → Y)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) (t : ℝ≥0) (x : X)
    (hx : ι x≠γ t) : ∀ᶠ s in 𝓝 t, x∉visited ι γ s ∆ visited ι γ t := by
  have hr : 0<dist (ι x) (γ t) := dist_pos.mpr hx
  obtain ⟨δ,hδ,hδγ⟩ := Metric.continuousAt_iff.mp (hγ.continuousAt (x := t)) _ hr
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs hxs
  obtain ⟨u,hu,he⟩ := visited_symmDiff_subset ι γ s t hxs
  have hud : dist u t<δ := (nnreal_dist_right_le hu).trans_lt hs
  have hlt := hδγ hud
  rw [he] at hlt
  exact lt_irrefl _ hlt

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma eventually_visited_iff (ι : X → Y)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) (t : ℝ≥0) (x : X)
    (hx : ι x≠γ t) : ∀ᶠ s in 𝓝 t, (x∈visited ι γ s ↔ x∈visited ι γ t) := by
  filter_upwards [eventually_not_mem_visited_symmDiff ι γ hγ t x hx] with s hs
  constructor
  · intro hx
    by_contra ht
    exact hs (Or.inl ⟨hx,ht⟩)
  · intro hx
    by_contra ht
    exact hs (Or.inr ⟨hx,ht⟩)

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma preimage_singleton_null_of_injective (ν : Measure X) [NullSingletonClass ν]
    (ι : X → Y) (hinj : Function.Injective ι) (y : Y) : ν (ι ⁻¹' {y})=0 := by
  by_cases h : ∃ x, ι x=y
  · obtain ⟨x,hx⟩ := h
    have he : ι ⁻¹' {y}={x} := by
      ext z
      simp only [mem_preimage,mem_singleton_iff,← hx,hinj.eq_iff]
    rw [he,measure_singleton]
  · have he : ι ⁻¹' {y}=∅ := by
      ext x
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      exact fun hx => h ⟨x,hx⟩
    rw [he,measure_empty]

 

lemma tendsto_measure_visited_symmDiff (ν : Measure X)
    (ι : X → Y) (hι : Measurable ι) (γ : ℝ≥0 → Y) (hγ : Continuous γ)
    (t : ℝ≥0) (hpoint : ν (ι ⁻¹' {γ t})=0)
    (K : Set X) (_hK : MeasurableSet K) (hfin : ν K≠∞) :
    Tendsto (fun s => ν (K∩(visited ι γ s ∆ visited ι γ t))) (𝓝 t) (𝓝 0) := by
  let μ := ν.restrict K
  have : IsFiniteMeasure μ := ⟨by simpa only [μ,Measure.restrict_apply_univ] using hfin.lt_top⟩
  let F : ℝ≥0 → X → ℝ≥0∞ := fun s => (visited ι γ s ∆ visited ι γ t).indicator 1
  have hF (s : ℝ≥0) : Measurable (F s) :=
    measurable_const.indicator
      ((measurableSet_visited ι hι γ hγ s).symmDiff (measurableSet_visited ι hι γ hγ t))
  have hbound (s : ℝ≥0) : ∀ᵐ x ∂μ, F s x≤1 := Eventually.of_forall (fun x => by
    by_cases hx : x∈visited ι γ s ∆ visited ι γ t <;> simp [F,hx])
  have hzero : μ (ι ⁻¹' {γ t})=0 := by
    change (ν.restrict K) (ι ⁻¹' {γ t})=0
    rw [Measure.restrict_apply ((measurableSet_singleton (γ t)).preimage hι)]
    exact measure_mono_null inter_subset_left hpoint
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun s => F s x) (𝓝 t) (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with x hx
    have hxt : ι x≠γ t := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_not_mem_visited_symmDiff ι γ hγ t x hxt] with s hs
    simp only [F,indicator_of_notMem hs]
  have ht := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ≥0∞))
    (Eventually.of_forall hF) (Eventually.of_forall hbound)
    (by simp : (∫⁻ x, (1 : ℝ≥0∞) ∂μ)≠∞) hlim
  have he (s : ℝ≥0) : (∫⁻x, F s x ∂μ)=ν (K∩(visited ι γ s ∆ visited ι γ t)) := by
    have hs := (measurableSet_visited ι hι γ hγ s).symmDiff (measurableSet_visited ι hι γ hγ t)
    change (∫⁻x, (visited ι γ s ∆ visited ι γ t).indicator 1 x ∂(ν.restrict K))=_
    rw [lintegral_indicator_one hs,Measure.restrict_apply hs,inter_comm]
  simpa only [he,lintegral_zero] using ht

 
lemma continuous_integral_visited (ν : Measure X) [NullSingletonClass ν]
    (ι : X → Y) (hι : Measurable ι) (hinj : Function.Injective ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) (f : X → ℝ) (hf : Integrable f ν) :
    Continuous (fun t => ∫x in visited ι γ t, f x ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro t
  simp_rw [← integral_indicator (measurableSet_visited ι hι γ hγ _)]
  apply continuousAt_of_dominated (bound := fun x => ‖f x‖)
  · exact Eventually.of_forall (fun s => hf.aestronglyMeasurable.indicator
      (measurableSet_visited ι hι γ hγ s))
  · exact Eventually.of_forall (fun s => Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _))
  · exact hf.norm
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (preimage_singleton_null_of_injective ν ι hinj (γ t))] with x hx
    have hxt : ι x≠γ t := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_visited_iff ι γ hγ t x hxt] with s hs
    by_cases ht : x∈visited ι γ t
    · simp only [indicator_of_mem ht,indicator_of_mem (hs.mpr ht)]
    · simp only [indicator_of_notMem ht,indicator_of_notMem (mt hs.mp ht)]

 

def firstVisit (ι : X → Y) (γ : ℝ≥0 → Y) (x : X) : ℝ≥0∞ :=
  if _h : ({u : ℝ≥0 | γ u=ι x}).Nonempty then
    (sInf {u : ℝ≥0 | γ u=ι x} : ℝ≥0) else ∞

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma firstVisit_le_iff (ι : X → Y) (γ : ℝ≥0 → Y) (hγ : Continuous γ)
    (x : X) (t : ℝ≥0) : firstVisit ι γ x≤(t : ℝ≥0∞) ↔ x∈visited ι γ t := by
  classical
  by_cases h : ({u : ℝ≥0 | γ u=ι x}).Nonempty
  · have hclosed : IsClosed {u : ℝ≥0 | γ u=ι x} := isClosed_eq hγ continuous_const
    have hmem := hclosed.csInf_mem h ⟨0,fun _ _ => bot_le⟩
    simp only [firstVisit,dite_eq_left h,ENNReal.coe_le_coe]
    constructor
    · intro ht
      exact ⟨_,⟨bot_le,ht⟩,hmem⟩
    · rintro ⟨u,hu,he⟩
      exact (csInf_le (s := {u : ℝ≥0 | γ u=ι x}) ⟨0,fun _ _ => bot_le⟩ he).trans hu.2
  · simp only [firstVisit,dite_eq_right h,top_le_iff,ENNReal.coe_ne_top,false_iff]
    rintro ⟨u,hu,he⟩
    exact h ⟨u,he⟩

omit [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma firstVisit_lt_top_iff (ι : X → Y) (γ : ℝ≥0 → Y) (x : X) :
    firstVisit ι γ x<∞ ↔ ι x∈range γ := by
  classical
  by_cases h : ({u : ℝ≥0 | γ u=ι x}).Nonempty
  · simp only [firstVisit,dite_eq_left h,ENNReal.coe_lt_top,true_iff]
    exact h
  · simp only [firstVisit,dite_eq_right h,lt_self_iff_false,false_iff]
    exact h

lemma measurable_firstVisit (ι : X → Y) (hι : Measurable ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) : Measurable (firstVisit ι γ) := by
  apply measurable_of_Iic
  intro t
  induction t using ENNReal.recTopCoe with
  | top => simp only [Iic_top,preimage_univ,MeasurableSet.univ]
  | coe t =>
    have he : (firstVisit ι γ) ⁻¹' Iic (t : ℝ≥0∞)=visited ι γ t := by
      ext x
      exact firstVisit_le_iff ι γ hγ x t
    rw [he]
    exact measurableSet_visited ι hι γ hγ t

 

omit [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma iUnion_visited_nat (ι : X → Y) (γ : ℝ≥0 → Y) :
    (⋃ n : ℕ, visited ι γ n)=ι ⁻¹' range γ := by
  ext x
  constructor
  · rintro ⟨_,⟨n,rfl⟩,u,hu,he⟩
    exact ⟨u,he⟩
  · rintro ⟨u,he⟩
    obtain ⟨n,hn⟩ := exists_nat_ge u
    exact mem_iUnion.mpr ⟨n,u,⟨bot_le,hn⟩,he⟩

 

lemma restrict_sub_restrict (ν : Measure X) (S T : Set X) (hS : MeasurableSet S) :
    ν.restrict T-ν.restrict S=ν.restrict (T\S) := by
  have hp : (ν.restrict T-ν.restrict S).restrict S=0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hS,
      Measure.restrict_restrict hS,Measure.restrict_restrict hS,inter_self]
    exact Measure.sub_eq_zero_of_le (Measure.restrict_mono inter_subset_left le_rfl)
  have hf : (ν.restrict T-ν.restrict S).restrict Sᶜ=ν.restrict (T\S) := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.compl,
      Measure.restrict_restrict hS.compl,Measure.restrict_restrict hS.compl,
      compl_inter_self,Measure.restrict_empty,Measure.sub_zero]
    rw [sdiff_eq,inter_comm]
  have hi := Measure.restrict_add_restrict_compl (μ := ν.restrict T-ν.restrict S) hS
  rw [hp,hf,zero_add] at hi
  exact hi.symm

omit [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma visited_diff_subset (ι : X → Y) (γ : ℝ≥0 → Y) {s t : ℝ≥0} (_hst : s≤t) :
    visited ι γ t\visited ι γ s⊆ι ⁻¹' (γ '' Icc s t) := by
  rintro x ⟨⟨u,hu,he⟩,hn⟩
  have hsu : s<u := lt_of_not_ge (fun hus => hn ⟨u,⟨hu.1,hus⟩,he⟩)
  exact ⟨u,⟨hsu.le,hu.2⟩,he⟩

 

lemma increment_carried_by_segment (ν : Measure X) (ι : X → Y) (hι : Measurable ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ) {s t : ℝ≥0} (hst : s≤t) :
    (ν.restrict (visited ι γ t)-ν.restrict (visited ι γ s))
        (ι ⁻¹' (γ '' Icc s t))ᶜ=0 := by
  rw [restrict_sub_restrict ν _ _ (measurableSet_visited ι hι γ hγ s),
    Measure.restrict_apply (((isCompact_Icc.image hγ).isClosed.measurableSet).preimage hι).compl]
  have he : (ι ⁻¹' (γ '' Icc s t))ᶜ∩(visited ι γ t\visited ι γ s)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hn,hx⟩
    exact hn (visited_diff_subset ι γ hst hx)
  rw [he,measure_empty]

end SLEExactGauge.TraceRestriction
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.DenseTimeSqueeze

 

lemma tendsto_of_dense {I : Type*} {l : Filter I}
    (f : I → ℝ≥0 → ℝ) (F : ℝ≥0 → ℝ) (D : Set ℝ≥0)
    (hD : Dense D) (h0 : 0 ∈ D) (hmono : ∀ i, Monotone (f i))
    (hF : Continuous F)
    (hc : ∀ q ∈ D, Tendsto (fun i => f i q) l (𝓝 (F q)))
    (t : ℝ≥0) : Tendsto (fun i => f i t) l (𝓝 (F t)) := by
  by_cases ht : t = 0
  · subst t
    exact hc 0 h0
  rw [tendsto_order]
  constructor
  · intro a ha
    have he : ∀ᶠ q in 𝓝 t, a < F q := hF.continuousAt.tendsto.eventually (lt_mem_nhds ha)
    obtain ⟨u, hut, hu⟩ := exists_Ioc_subset_of_mem_nhds he (⟨0, bot_lt_iff_ne_bot.mpr ht⟩)
    obtain ⟨q, hq, huq, hqt⟩ := hD.exists_between hut
    have haq : a < F q := hu ⟨huq, hqt.le⟩
    filter_upwards [(hc q hq).eventually (lt_mem_nhds haq)] with i hi
    exact hi.trans_le (hmono i hqt.le)
  · intro a ha
    have he : ∀ᶠ q in 𝓝 t, F q < a := hF.continuousAt.tendsto.eventually (gt_mem_nhds ha)
    obtain ⟨u, htu, hu⟩ := exists_Ico_subset_of_mem_nhds he (exists_gt t)
    obtain ⟨q, hq, htq, hqu⟩ := hD.exists_between htu
    have hqa : F q < a := hu ⟨htq.le, hqu⟩
    filter_upwards [(hc q hq).eventually (gt_mem_nhds hqa)] with i hi
    exact (hmono i htq.le).trans_lt hi

end SLEExactGauge.DenseTimeSqueeze

namespace SLEExactGauge.DenseTimeSqueeze

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]

 

omit [T2Space X] in
lemma tendsto_integral_of_dense {I : Type*} {l : Filter I}
    (μ : I → ℝ≥0 → Measure X) (ν : ℝ≥0 → Measure X)
    [∀ i t, IsFiniteMeasureOnCompacts (μ i t)]
    [∀ t, IsFiniteMeasureOnCompacts (ν t)]
    (D : Set ℝ≥0) (hD : Dense D) (h0 : 0 ∈ D)
    (hmono : ∀ i, Monotone (μ i))
    (hν : ∀ f : C_c(X, ℝ), Continuous (fun t => ∫ x, f x ∂ν t))
    (hc : ∀ q ∈ D, ∀ f : C_c(X, ℝ),
      Tendsto (fun i => ∫ x, f x ∂μ i q) l (𝓝 (∫ x, f x ∂ν q)))
    (t : ℝ≥0) (f : C_c(X, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂μ i t) l (𝓝 (∫ x, f x ∂ν t)) := by
  have hp (g : C_c(X, ℝ)) (hg : 0 ≤ g) :
      Tendsto (fun i => ∫ x, g x ∂μ i t) l (𝓝 (∫ x, g x ∂ν t)) := by
    apply tendsto_of_dense (fun i q => ∫ x, g x ∂μ i q)
      (fun q => ∫ x, g x ∂ν q) D hD h0 _ _ _ t
    · intro i s t hst
      exact integral_mono_measure (hmono i hst) (Eventually.of_forall hg) g.integrable
    · exact hν g
    · exact fun q hq => hc q hq g
  have hplus := hp (f ⊔ 0) le_sup_right
  have hminus := hp ((-f) ⊔ 0) le_sup_right
  have he : ∀ x, f x = (f ⊔ 0) x - ((-f) ⊔ 0) x := by
    intro x
    change f x = max (f x) 0 - max (-f x) 0
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
  have hi (ρ : Measure X) [IsFiniteMeasureOnCompacts ρ] :
      (∫ x, f x ∂ρ) = (∫ x, (f ⊔ 0) x ∂ρ) - ∫ x, ((-f) ⊔ 0) x ∂ρ := by
    simp_rw [he]
    exact integral_sub (f ⊔ 0).integrable ((-f) ⊔ 0).integrable
  simpa only [hi] using hplus.sub hminus

end SLEExactGauge.DenseTimeSqueeze
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.FirstVisitReconstruction
open TraceRestriction DenseTimeSqueeze MassVersions

variable {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tendsto_all_times (μ : ℕ → ℝ≥0 → Measure X)
    [∀ n t, IsFiniteMeasureOnCompacts (μ n t)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [NullSingletonClass ν]
    (ι : X → Y) (hι : Measurable ι) (hinj : Function.Injective ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ)
    (D : Set ℝ≥0) (hD : Dense D) (h0 : 0 ∈ D)
    (hmono : ∀ n, Monotone (μ n))
    (hc : ∀ q ∈ D, ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n q)
      atTop (𝓝 (∫ x in visited ι γ q, f x ∂ν))) :
    ∀ t : ℝ≥0, ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n t)
      atTop (𝓝 (∫ x in visited ι γ t, f x ∂ν)) := by
  apply tendsto_integral_of_dense μ (fun t => ν.restrict (visited ι γ t)) D hD h0 hmono
  · intro f
    exact continuous_integral_visited ν ι hι hinj γ hγ f f.integrable
  · exact hc

 

lemma radonLimit_all_times (μ : ℕ → ℝ≥0 → Measure X)
    [∀ n t, IsFiniteMeasureOnCompacts (μ n t)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [NullSingletonClass ν]
    (ι : X → Y) (hι : Measurable ι) (hinj : Function.Injective ι)
    (γ : ℝ≥0 → Y) (hγ : Continuous γ)
    (D : Set ℝ≥0) (hD : Dense D) (h0 : 0 ∈ D)
    (hmono : ∀ n, Monotone (μ n))
    (hc : ∀ q ∈ D, ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂μ n q)
      atTop (𝓝 (∫ x in visited ι γ q, f x ∂ν))) :
    ∀ t : ℝ≥0,
      radonLimit (fun n => CompactlySupportedContinuousMap.integralPositiveLinearMap (μ n t)) =
        ν.restrict (visited ι γ t) := by
  intro t
  apply radonLimit_eq
  exact tendsto_all_times μ ν ι hι hinj γ hγ D hD h0 hmono hc t

end SLEExactGauge.FirstVisitReconstruction
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal symmDiff
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma actualConvexMass_mono_time (a : ℝ) (s : Finset ℕ) (c : ℕ→ℝ)
    (b : ExactSLEGenerator.Driver) : Monotone (fun t => actualConvexMass a s c t b) := by
  intro u v huv
  apply Measure.le_iff'.mpr
  intro A
  simp only [actualConvexMass,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul' le_rfl
    (Measure.le_iff'.mp (actualUpperMass_mono_time a _ b huv) A))

end ExactSLEGreen

namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen
open TraceRestriction MassVersions

 
def internalTrace (κ : ℝ) (b : TDriver) (u : ℝ≥0) : ℂ :=
  Target.trace κ b ((u:ℝ)/κ)

lemma continuous_internalTrace {κ : ℝ} (hκ : 0<κ) (b : TDriver)
    (hb : ContinuousOn (Target.trace κ b) (Ici 0)) : Continuous (internalTrace κ b) :=
  hb.comp_continuous (continuous_subtype_val.div_const κ) (fun u => div_nonneg u.2 hκ.le)

lemma internalTrace_image {κ : ℝ} (hκ : 0<κ) (b : TDriver) (u v : ℝ≥0) :
    internalTrace κ b '' Icc u v = Target.trace κ b '' Icc ((u:ℝ)/κ) ((v:ℝ)/κ) := by
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨_,⟨div_le_div_of_nonneg_right ht.1 hκ.le,
      div_le_div_of_nonneg_right ht.2 hκ.le⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    have ht0 : 0≤t := (div_nonneg u.2 hκ.le).trans ht.1
    refine ⟨⟨κ*t,mul_nonneg hκ.le ht0⟩,⟨?_,?_⟩,?_⟩
    · change (u:ℝ)≤κ*t
      nlinarith [(div_le_iff₀ hκ).mp ht.1]
    · change κ*t≤v
      nlinarith [(le_div_iff₀ hκ).mp ht.2]
    · change Target.trace κ b ((κ*t)/κ)=Target.trace κ b t
      rw [mul_div_cancel_left₀ _ hκ.ne']

lemma visited_internalTrace {κ : ℝ} (hκ : 0<κ) (b : TDriver) (t : ℝ≥0) :
    visited (fun z : UpperPlane => z.1) (internalTrace κ b) t =
      {z : UpperPlane | z.1∈Target.trace κ b '' Icc 0 ((t:ℝ)/κ)} := by
  simp only [visited,internalTrace_image hκ,NNReal.coe_zero,zero_div]
  rfl

 
lemma actualMass_tendsto_all_times (κ : ℝ) (hκ : 0<κ) (ha : 1/4<Target.a κ)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (b : TDriver) (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (ν : Measure UpperPlane) [IsFiniteMeasureOnCompacts ν] [NullSingletonClass ν]
    (D : Set ℝ≥0) (hD : Dense D) (h0 : 0∈D)
    (hconv : ∀q∈D, ∀ f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) q (driverHomeomorph b))
      atTop (𝓝 (∫z in visited (fun z : UpperPlane => z.1) (internalTrace κ b) q,f z∂ν))) :
    ∀t : ℝ≥0, ∀ f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) t (driverHomeomorph b))
      atTop (𝓝 (∫z in visited (fun z : UpperPlane => z.1) (internalTrace κ b) t,f z∂ν)) := by
  let M (k : ℕ) (t : ℝ≥0) :=
    actualConvexMass (Target.a κ) (s k) (c k) t (driverHomeomorph b)
  let (k : ℕ) (t : ℝ≥0) : IsFiniteMeasureOnCompacts (M k t) :=
    actualConvexMass_finiteOnCompacts (Target.a κ) ha (s k) (c k) t (driverHomeomorph b)
  have hv := FirstVisitReconstruction.tendsto_all_times M ν
    (fun z : UpperPlane => z.1) measurable_subtype_coe Subtype.val_injective
    (internalTrace κ b) (continuous_internalTrace hκ b hcont) D hD h0
    (fun k u v huv => actualConvexMass_mono_time (Target.a κ) (s k) (c k)
      (driverHomeomorph b) (ENNReal.coe_le_coe.mpr huv))
    (by
      intro q hq f
      simpa only [M,actualConvexMass_integral (Target.a κ) ha _ _ (hc _)] using hconv q hq f)
  intro t f
  simpa only [M,actualConvexMass_integral (Target.a κ) ha _ _ (hc _)] using hv t f

 

lemma recoveredMass_all_times (κ : ℝ) (hκ : 0<κ) (ha : 1/4<Target.a κ)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (b : TDriver) (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (ν : Measure UpperPlane) [IsFiniteMeasureOnCompacts ν] [NullSingletonClass ν]
    (D : Set ℝ≥0) (hD : Dense D) (h0 : 0∈D)
    (hconv : ∀q∈D, ∀ f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) q (driverHomeomorph b))
      atTop (𝓝 (∫z in visited (fun z : UpperPlane => z.1) (internalTrace κ b) q,f z∂ν))) :
    ∀t : ℝ≥0,
      recoveredMass (Target.a κ) ha s c hc t (driverHomeomorph b)=
        ν.restrict (visited (fun z : UpperPlane => z.1) (internalTrace κ b) t) := by
  intro t
  apply radonLimit_eq
  intro f
  simpa only [actualMassFunctionals_apply] using
    actualMass_tendsto_all_times κ hκ ha s c hc b hcont ν D hD h0 hconv t f

 

lemma local_variation_visited (ν : Measure UpperPlane) [NullSingletonClass ν]
    {κ : ℝ} (hκ : 0<κ) (b : TDriver)
    (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (K : Set UpperPlane) (hK : MeasurableSet K) (hfin : ν K≠∞) (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 =>
      ((ν.restrict (visited (fun z : UpperPlane => z.1) (internalTrace κ b) u)-
        ν.restrict (visited (fun z : UpperPlane => z.1) (internalTrace κ b) t))+
       (ν.restrict (visited (fun z : UpperPlane => z.1) (internalTrace κ b) t)-
        ν.restrict (visited (fun z : UpperPlane => z.1) (internalTrace κ b) u))) K)
        (𝓝 t) (𝓝 0) := by
  let V := visited (fun z : UpperPlane => z.1) (internalTrace κ b)
  have hV (u : ℝ≥0) : MeasurableSet (V u) :=
    measurableSet_visited _ measurable_subtype_coe _ (continuous_internalTrace hκ b hcont) u
  have he (u : ℝ≥0) :
      ((ν.restrict (V u)-ν.restrict (V t))+(ν.restrict (V t)-ν.restrict (V u))) K=
        ν (K∩(V u ∆ V t)) := by
    rw [restrict_sub_restrict ν _ _ (hV t),restrict_sub_restrict ν _ _ (hV u),
      ←Measure.restrict_union (disjoint_sdiff_sdiff (x := V u) (y := V t)) ((hV t).diff (hV u)),
      Measure.restrict_apply hK]
    rfl
  change Tendsto (fun u : ℝ≥0 =>
    ((ν.restrict (V u)-ν.restrict (V t))+(ν.restrict (V t)-ν.restrict (V u))) K) (𝓝 t) (𝓝 0)
  simp_rw [he]
  exact tendsto_measure_visited_symmDiff ν _ measurable_subtype_coe _
    (continuous_internalTrace hκ b hcont) t
    (preimage_singleton_null_of_injective ν _ Subtype.val_injective _) K hK hfin

end SLEExactGauge.TraceMassContinuity
end
end

end OAI
