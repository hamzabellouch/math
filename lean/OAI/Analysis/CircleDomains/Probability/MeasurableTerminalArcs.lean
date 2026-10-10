import OAI.Analysis.CircleDomains.Topology.PathSelectionInput
import OAI.Analysis.CircleDomains.Topology.SimpleSubarcRelation
import OAI.Analysis.CircleDomains.Topology.TerminalSimpleArc

namespace OAI

/-! Apply the published measurable selection theorem to the actual Borel
relation of simple subarcs of the last-entry terminal path. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_measurable_terminal_arc_selector
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (hV : IsOpen V) :
    ∃ f : C(PathTime, Sphere) → C(PathTime, Sphere), AEMeasurable f (μ : Measure _) ∧
      ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
        (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation := by
  let δ (γ : C(PathTime, Sphere)) := terminalPath γ (lastEntryTime γ V)
  have hδ : Measurable δ := measurable_lastEntryPath V hV
  let R : Set (C(PathTime, Sphere) × C(PathTime, Sphere)) :=
    {p | (δ p.1) ⊥ = (δ p.1) ⊤} ∪ {p | (δ p.1, p.2) ∈ simpleSubarcRelation}
  have hR : MeasurableSet R := by
    apply MeasurableSet.union
    · exact measurableSet_eq_fun
        ((continuous_eval_const ⊥).measurable.comp (hδ.comp measurable_fst))
        ((continuous_eval_const ⊤).measurable.comp (hδ.comp measurable_fst))
    · exact measurableSet_simpleSubarcRelation.preimage
        ((hδ.comp measurable_fst).prodMk measurable_snd)
  have hnon (γ : C(PathTime, Sphere)) : ∃ α, (γ, α) ∈ R := by
    by_cases he : δ γ ⊥ = δ γ ⊤
    · exact ⟨γ, Or.inl he⟩
    · obtain ⟨α, ha, h0, h1, hr⟩ := exists_simple_subarc harcs (δ γ) he
      exact ⟨α, Or.inr ⟨ha, h0, h1, hr⟩⟩
  obtain ⟨f, hfm, hf⟩ := hselect μ R hR hnon
  refine ⟨f, hfm.aemeasurable, ?_⟩
  intro γ hstart hend
  rcases hf γ with he | he
  · have hfront := lastEntry_frontier γ hV hstart hend
    change δ γ ⊥ = δ γ ⊤ at he
    have he' : γ (lastEntryTime γ V) = γ ⊤ := by
      simpa only [δ, terminalPath, ContinuousMap.comp_apply,
        affinePathTime_zero, affinePathTime_one] using he
    exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hV)
      (he' ▸ hfront) hend).elim
  · exact he

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem terminal_arc_selector_properties
    {f : C(PathTime, Sphere) → C(PathTime, Sphere)} {V : Set Sphere} (hV : IsOpen V)
    (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
      (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
    (γ : C(PathTime, Sphere)) (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    Injective (f γ) ∧ (f γ) ⊥ = γ (lastEntryTime γ V) ∧ (f γ) ⊤ = γ ⊤ ∧
      range (f γ) ⊆ lastEntryTail γ V ∧ (f γ) ⊥ ∈ frontier V ∧
      ∀ t ∈ Ioo (⊥ : PathTime) ⊤, (f γ) t ∈ V \ {γ ⊤} := by
  obtain ⟨hinj, h0, h1, hsub⟩ := hf γ hstart hend
  have h0' : (f γ) ⊥ = γ (lastEntryTime γ V) := by
    simpa only [terminalPath, ContinuousMap.comp_apply, affinePathTime_zero] using h0
  have h1' : (f γ) ⊤ = γ ⊤ := by
    simpa only [terminalPath, ContinuousMap.comp_apply, affinePathTime_one] using h1
  have htail : range (f γ) ⊆ lastEntryTail γ V := by
    intro x hx
    obtain ⟨t, rfl⟩ := hsub hx
    exact ⟨affinePathTime (lastEntryTime γ V) ⊤ t,
      (affinePathTime_mem_Icc le_top t).1, rfl⟩
  refine ⟨hinj, h0', h1', htail, ?_, ?_⟩
  · simpa only [h0'] using lastEntry_frontier γ hV hstart hend
  · intro t ht
    constructor
    · by_contra hn
      have he := lastEntryTail_outside γ V (htail (mem_range_self t)) hn
      exact ht.1.ne' (hinj (he.trans h0'.symm))
    · intro he
      exact ht.2.ne (hinj (he.trans h1'.symm))

end CircleDomainRigidity

end

end OAI
