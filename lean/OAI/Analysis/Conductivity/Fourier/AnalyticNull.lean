import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section LocalNull
variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] (μ : Measure E)

lemma measure_inter_zero_of_local {U Z : Set E}
    (h : ∀ x ∈ U, ∃ V : Set E, x ∈ V ∧ IsOpen V ∧ μ (V ∩ Z) = 0) :
    μ (U ∩ Z) = 0 := by
  choose V hmem hopen hnull using (fun x : U => h x x.property)
  obtain ⟨I,hIc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hopen (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩)
  apply measure_mono_null (t := ⋃ x ∈ I, V x ∩ Z)
  · intro x hx
    rcases mem_iUnion₂.mp (hcov hx.1) with ⟨y,hy,hxy⟩
    exact mem_iUnion₂.mpr ⟨y,hy,hxy,hx.2⟩
  · exact (measure_biUnion_null_iff hIc).mpr (fun x _ => hnull x)
end LocalNull

def AnalyticNullProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ (U : Set E) (f : E → ℝ), IsOpen U → IsPreconnected U → AnalyticOnNhd ℝ f U →
    (∃ x ∈ U, f x ≠ 0) → μ (U ∩ f ⁻¹' {0}) = 0

lemma analyticNull_real : AnalyticNullProperty ℝ volume := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  have hd : IsDiscrete (f ⁻¹' {0} ∩ U) := isDiscrete_of_codiscreteWithin
    (by simpa only [preimage_compl] using
      hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x,hx⟩,hc⟩)
  rw [inter_comm]
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [SecondCountableTopology E] in
lemma analytic_zero_measurable {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U) :
    MeasurableSet (U ∩ f ⁻¹' {0}) := by
  have ho := hf.continuousOn.isOpen_inter_preimage hU (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set ℝ))
  convert hU.measurableSet.diff ho.measurableSet using 1
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Set.mem_sdiff,mem_compl_iff]
  tauto

omit [SecondCountableTopology E] in
lemma analytic_null_rectangle (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν)
    {U : Set E} {V : Set F} {f : E × F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hcU : IsPreconnected U) (hcV : IsPreconnected V)
    (hf : AnalyticOnNhd ℝ f (U ×ˢ V)) (hx : ∃ x ∈ U ×ˢ V, f x ≠ 0) :
    μ.prod ν ((U ×ˢ V) ∩ f ⁻¹' {0}) = 0 := by
  obtain ⟨⟨x₀,y₀⟩,hxy,hfxy⟩ := hx
  have ha : AnalyticOnNhd ℝ (fun x => f (x,y₀)) U := by
    intro x hx
    have hg : AnalyticAt ℝ (fun t : E => (t,y₀)) x := analyticAt_id.prod analyticAt_const
    exact (hf (x,y₀) ⟨hx,hxy.2⟩).comp (f := fun t : E => (t,y₀)) hg
  have hn := hE U (fun x => f (x,y₀)) hU hcU ha ⟨x₀,hxy.1,hfxy⟩
  apply Measure.measure_prod_null_of_ae_null (analytic_zero_measurable (hU.prod hV) hf)
  filter_upwards [compl_mem_ae_iff.mpr hn] with x hx
  by_cases hxU : x ∈ U
  · have hfx : f (x,y₀) ≠ 0 := by simpa [hxU] using hx
    have hb : AnalyticOnNhd ℝ (fun y => f (x,y)) V := by
      intro y hy
      have hg : AnalyticAt ℝ (fun t : F => (x,t)) y := analyticAt_const.prod analyticAt_id
      exact (hf (x,y) ⟨hxU,hy⟩).comp (f := fun t : F => (x,t)) hg
    change ν (Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0})) = 0
    have he : Prod.mk x ⁻¹' ((U ×ˢ V) ∩ f ⁻¹' {0}) =
        V ∩ (fun y => f (x,y)) ⁻¹' {0} := by ext y; simp [hxU]
    rw [he]
    exact hF V (fun y => f (x,y)) hV hcV hb ⟨y₀,hxy.2,hfx⟩
  · simp [hxU]

lemma analyticNull_prod (μ : Measure E) (ν : Measure F) [SFinite ν]
    (hE : AnalyticNullProperty E μ) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty (E × F) (μ.prod ν) := by
  intro U f hU hc hf ⟨x₀,hx₀,hfx₀⟩
  apply measure_inter_zero_of_local
  intro p hp
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp hU p hp
  let V := Metric.ball p.1 ε ×ˢ Metric.ball p.2 ε
  have hVm : p ∈ V := ⟨Metric.mem_ball_self hε,Metric.mem_ball_self hε⟩
  have hVo : IsOpen V := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro q hq
    apply hsub
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt hq.1 hq.2
  have hne : ∃ x ∈ V, f x ≠ 0 := by
    by_contra! hn
    have he : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hVo.mem_nhds hVm] with x hx
      exact hn x hx
    exact hfx₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hp he hx₀)
  refine ⟨V,hVm,hVo,?_⟩
  exact analytic_null_rectangle μ ν hE hF Metric.isOpen_ball Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected (hf.mono hVU) hne

end ScalarConductivity



namespace ScalarConductivity
open Set Filter MeasureTheory Topology

section Transfer
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

omit [BorelSpace E] [SecondCountableTopology E] [SecondCountableTopology F] in
lemma analyticNull_of_equiv (μ : Measure E) (ν : Measure F) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e μ ν) (hF : AnalyticNullProperty F ν) :
    AnalyticNullProperty E μ := by
  intro U f hU hc hf ⟨x,hx,hfx⟩
  let V := e '' U
  have hVo : IsOpen V := e.toHomeomorph.isOpenMap _ hU
  have hg : AnalyticOnNhd ℝ (fun y => f (e.symm y)) V := by
    rintro y ⟨z,hz,rfl⟩
    apply (hf z hz).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z)
  have hn := hF V (fun y => f (e.symm y)) hVo
    (hc.image e e.continuous.continuousOn) hg ⟨e x,mem_image_of_mem _ hx,by simpa using hfx⟩
  rw [←he.measure_preimage (analytic_zero_measurable hVo hg).nullMeasurableSet] at hn
  have hs : U ∩ f ⁻¹' {0} = e ⁻¹' (V ∩ (fun y => f (e.symm y)) ⁻¹' {0}) := by
    ext z
    simp [V]
  rw [hs]
  exact hn
end Transfer

def splitFinCLE (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.insertNthEquiv (fun _ : Fin (n+1) => ℝ) 0).symm
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

lemma splitFinCLE_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFinCLE n) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0

theorem analyticNull_fin (n : ℕ) : AnalyticNullProperty (Fin n → ℝ) volume := by
  induction n with
  | zero =>
    intro U f hU hc hf ⟨x,hx,hfx⟩
    have h : U ∩ f ⁻¹' {0} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro y hy
      exact hfx (by simpa only [Subsingleton.elim y x, mem_preimage, mem_singleton_iff] using hy.2)
    rw [h,measure_empty]
  | succ n ih =>
    exact analyticNull_of_equiv volume volume (splitFinCLE n) (splitFinCLE_measurePreserving n)
      (analyticNull_prod volume volume analyticNull_real ih)

lemma analytic_zero_volume {n : ℕ} {U : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hn : ∃ x ∈ U, f x ≠ 0) : volume (U ∩ f ⁻¹' {0}) = 0 :=
  analyticNull_fin n U f hU hc hf hn

end ScalarConductivity

end

end OAI
