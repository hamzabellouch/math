import Mathlib

namespace OAI

open MeasureTheory Set Filter

open scoped Topology

namespace CompactControls

variable {Z U : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

lemma ci {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) :
    Integrable f μ := hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

omit [BorelSpace Z] [SecondCountableTopology Z] [BorelSpace U]
  [SecondCountableTopology U] in
lemma support_prod (μ : Measure Z) (ν : Measure U) [SFinite μ] [SFinite ν]
    {z : Z} {u : U} (hz : z∈μ.support) (hu : u∈ν.support) : (z,u)∈(μ.prod ν).support := by
  rw [Measure.mem_support_iff_forall]
  intro S hS
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hS
  have ha := (Measure.mem_support_iff_forall z).mp hz A hA
  have hb := (Measure.mem_support_iff_forall u).mp hu B hB
  apply lt_of_lt_of_le _ (measure_mono hAB)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos ha.ne' hb.ne'

lemma support_map {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (T : X → Y) (hT : Continuous T) {x : X} (hx : x∈μ.support) :
    T x∈(Measure.map T μ).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro O hxO hO
  rw [Measure.map_apply hT.measurable hO.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _ (hT.continuousAt.preimage_mem_nhds (hO.mem_nhds hxO))

noncomputable def step (ν : Measure U) [IsProbabilityMeasure ν]
    (T : Z×U → Z) (hT : Continuous T) (μ : ProbabilityMeasure Z) : ProbabilityMeasure Z :=
  ⟨Measure.map T ((μ:Measure Z).prod ν),
    (Measure.isProbabilityMeasure_map_iff hT.measurable.aemeasurable).mpr inferInstance⟩

omit [SecondCountableTopology Z] in
lemma step_integral (ν : Measure U) [IsProbabilityMeasure ν] (T : Z×U → Z) (hT : Continuous T)
    (μ : ProbabilityMeasure Z) (f : Z → ℝ) (hf : Continuous f) :
    (∫ z,f z ∂(step ν T hT μ))=∫ z,f (T z) ∂((μ:Measure Z).prod ν) := by
  exact integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable

omit [BorelSpace Z] [BorelSpace U] in
lemma integral_fst (ν : Measure U) [IsProbabilityMeasure ν] (μ : ProbabilityMeasure Z)
    (f : Z → ℝ) (_hf : Continuous f) :
    (∫ z : Z×U,f z.1 ∂((μ:Measure Z).prod ν))=∫ z,f z ∂μ := by
  simpa using integral_fun_fst (μ := (μ:Measure Z)) (ν := ν) f

variable [CompactSpace Z] [CompactSpace U]

theorem exists_zero {I : Type*} (ν : Measure U) [IsProbabilityMeasure ν]
    (hν : ∀ u : U,u∈ν.support) (u₀ : U)
    (T : I → Z×U → Z) (hT : ∀ i,Continuous (T i))
    (K : Set (ProbabilityMeasure Z)) (hK : IsCompact K) (hne : K.Nonempty)
    (hpres : ∀ μ∈K,∀ i,step ν (T i) (hT i) μ∈K)
    (d H : Z → ℝ) (hd : Continuous d) (hH : Continuous H)
    (hdec : ∀ i z u,d (T i (z,u))≤d z)
    (hdown : ∀ i z,H (T i (z,u₀))≤H z)
    (hfixed : ∀ z,(∀ i,H (T i (z,u₀))=H z) → d z=0) :
    ∃ μ∈K,∀ᵐ z∂(μ:Measure Z),d z=0 := by
  classical
  let cost : ProbabilityMeasure Z → ℝ := fun μ => ∫ z,d z ∂μ
  have hcost : Continuous cost := ProbabilityMeasure.continuous_integral_continuousMap (⟨d,hd⟩ : C(Z,ℝ))
  obtain ⟨μ₀,hμ₀,hmin⟩ := hK.exists_isMinOn hne hcost.continuousOn
  let A : Set Z := {z | ∃ μ : ProbabilityMeasure Z,μ∈K ∧ cost μ=cost μ₀ ∧ z∈(μ:Measure Z).support}
  let S : Set Z := closure A
  have hopt (μ : ProbabilityMeasure Z) (hμ : μ∈K) (he : cost μ=cost μ₀) (i : I) :
      cost (step ν (T i) (hT i) μ)=cost μ₀ ∧
      ∀ z∈(μ:Measure Z).support,∀ u,d (T i (z,u))=d z := by
    have hf := ci ((μ:Measure Z).prod ν) (hd.comp (hT i))
    have hg := ci ((μ:Measure Z).prod ν) (hd.comp continuous_fst)
    have hl : cost (step ν (T i) (hT i) μ)≤cost μ := by
      rw [show cost (step ν (T i) (hT i) μ)=∫ z,d (T i z) ∂((μ:Measure Z).prod ν) from step_integral ν _ _ μ d hd,
        show cost μ=∫ z,d z ∂μ from rfl, ← integral_fst ν μ d hd]
      exact integral_mono hf hg (fun z => hdec i z.1 z.2)
    have he' : cost (step ν (T i) (hT i) μ)=cost μ₀ := le_antisymm (hl.trans_eq he) (hmin (hpres μ hμ i))
    refine ⟨he',?_⟩
    have heq : (fun z : Z×U => d (T i z))=ᵐ[(μ:Measure Z).prod ν] (fun z => d z.1) := by
      apply (integral_eq_iff_of_ae_le hf hg (Eventually.of_forall (fun z => hdec i z.1 z.2))).mp
      change (∫ z,d (T i z) ∂((μ:Measure Z).prod ν))=∫ z,d z.1 ∂((μ:Measure Z).prod ν)
      rw [← step_integral ν (T i) (hT i) μ d hd,integral_fst ν μ d hd]
      exact he'.trans he.symm
    have hsub := Measure.support_subset_of_isClosed (μ := (μ:Measure Z).prod ν)
      (isClosed_eq (hd.comp (hT i)) (hd.comp continuous_fst)) heq
    intro z hz u
    exact hsub (support_prod _ _ hz (hν u))
  have hA (i : I) (u : U) (z : Z) (hz : z∈A) : T i (z,u)∈A ∧ d (T i (z,u))=d z := by
    obtain ⟨μ,hμ,he,hz⟩ := hz
    obtain ⟨he',hd'⟩ := hopt μ hμ he i
    exact ⟨⟨step ν (T i) (hT i) μ,hpres μ hμ i,he',support_map _ _ (hT i) (support_prod _ _ hz (hν u))⟩,hd' z hz u⟩
  have hS (i : I) (u : U) (z : Z) (hz : z∈S) : T i (z,u)∈S ∧ d (T i (z,u))=d z := by
    have ht : Continuous (fun z => T i (z,u)) := (hT i).comp (continuous_id.prodMk continuous_const)
    constructor
    · exact closure_minimal (s := A) (t := (fun z => T i (z,u)) ⁻¹' S)
        (fun z hz => subset_closure (hA i u z hz).1) (isClosed_closure.preimage ht) hz
    · exact closure_minimal (fun z hz => (hA i u z hz).2) (isClosed_eq (hd.comp ht) hd) hz
  have hz0 (z : Z) (hz : z∈S) : d z=0 := by
    let L : Set Z := S∩{w | d w=d z}
    have hlc : IsCompact L := (isClosed_closure.inter (isClosed_eq hd continuous_const)).isCompact
    obtain ⟨w,hw,hwm⟩ := hlc.exists_isMinOn ⟨z,hz,rfl⟩ hH.continuousOn
    have hw0 : d w=0 := hfixed w (fun i => le_antisymm (hdown i w)
      (hwm ⟨(hS i u₀ w hw.1).1,(hS i u₀ w hw.1).2.trans hw.2⟩))
    exact hw.2.symm.trans hw0
  refine ⟨μ₀,hμ₀,?_⟩
  filter_upwards [Measure.support_mem_ae (μ := (μ₀:Measure Z))] with z hz
  exact hz0 z (subset_closure ⟨μ₀,hμ₀,rfl,hz⟩)

end CompactControls

end OAI
