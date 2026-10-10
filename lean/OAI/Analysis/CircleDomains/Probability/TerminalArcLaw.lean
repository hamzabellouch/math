import OAI.Analysis.CircleDomains.Probability.MeasurableTerminalArcs
import OAI.Analysis.CircleDomains.Probability.LastEntryLaw

namespace OAI

/-! The measurable simple-arc reduction preserves the last-entry distribution
and cannot increase any point-hit probability. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

variable (μ : ProbabilityMeasure C(PathTime, Sphere))
  (V : Set Sphere) (hV : IsOpen V)
  (f : C(PathTime, Sphere) → C(PathTime, Sphere))
  (hfm : AEMeasurable f (μ : Measure C(PathTime, Sphere)))
  (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
    (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
  (hends : ∀ᵐ γ ∂(μ : Measure C(PathTime, Sphere)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V)

include hV hfm hf hends

theorem terminalArcLaw_hit_le (x : Sphere) :
    pathHitProbability (μ.map f) x ≤ pathHitProbability μ x := by
  rw [pathHitProbability, ProbabilityMeasure.map_apply' μ hfm
    (isClosed_paths_hitting x).measurableSet]
  apply measure_mono_ae
  filter_upwards [hends] with γ hγ
  rintro ⟨t, ht⟩
  have hs := (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.2.2.1
  obtain ⟨s, _, he⟩ := hs (ht ▸ mem_range_self (f := f γ) t)
  exact ⟨s, he⟩

theorem terminalArcLaw_hit_eq_zero {x : Sphere} (hx : x ∉ closure V) :
    pathHitProbability (μ.map f) x = 0 := by
  rw [pathHitProbability, ProbabilityMeasure.map_apply' μ hfm
    (isClosed_paths_hitting x).measurableSet]
  apply measure_mono_null (t := {γ | ¬ (γ ⊥ ∉ V ∧ γ ⊤ ∈ V)})
  · intro γ hhit hγ
    obtain ⟨t, ht⟩ := hhit
    have hs := (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.2.2.1
    exact hx (lastEntryTail_subset_closure γ hV hγ.1 hγ.2
      (hs (ht ▸ mem_range_self (f := f γ) t)))
  · exact ae_iff.mp hends

theorem terminalArcLaw_injective :
    ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map f : Measure C(PathTime, Sphere)), Injective α := by
  rw [ProbabilityMeasure.toMeasure_map μ]
  apply (ae_map_iff hfm measurableSet_injective_paths).mpr
  filter_upwards [hends] with γ hγ
  exact (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).1

theorem terminalArcLaw_start_distribution :
    (μ.map f).map (fun α => α ⊥) = lastEntryLaw μ V := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun α : C(PathTime, Sphere) => α ⊥) (μ.map f : Measure C(PathTime, Sphere)) = _
  rw [ProbabilityMeasure.toMeasure_map μ, AEMeasurable.map_map_of_aemeasurable
    ((continuous_eval_const ⊥).measurable.aemeasurable) hfm]
  change (μ : Measure C(PathTime, Sphere)).map ((fun α : C(PathTime, Sphere) => α ⊥) ∘ f) = _
  rw [lastEntryLaw, ProbabilityMeasure.toMeasure_map μ]
  apply Measure.map_congr
  filter_upwards [hends] with γ hγ
  exact (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.1

theorem terminalArcLaw_endpoint_distribution :
    (μ.map f).map (fun α => α ⊤) = μ.map (fun γ => γ ⊤) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map μ,
    AEMeasurable.map_map_of_aemeasurable (continuous_eval_const ⊤).measurable.aemeasurable hfm,
    ProbabilityMeasure.toMeasure_map μ]
  apply Measure.map_congr
  filter_upwards [hends] with γ hγ
  exact (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.2.1

end CircleDomainRigidity

end

end OAI
