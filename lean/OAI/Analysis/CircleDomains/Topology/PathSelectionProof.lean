import OAI.Analysis.CircleDomains.Selection.BaireRightInverse
import OAI.Analysis.CircleDomains.Topology.PathSelectionInput

namespace OAI

/-! Discharge the published completed-measure path-selection input by
parametrizing the Borel relation with Baire space and selecting a branch. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem borelPathRelationSelection : BorelPathRelationSelection := by
  intro μ R hR hfull
  have ha : AnalyticSet R := hR.analyticSet
  rw [AnalyticSet] at ha
  rcases ha with hempty | ⟨q,hq,hqR⟩
  · obtain ⟨α,hα⟩ := hfull (ContinuousMap.const PathTime OnePoint.infty)
    rw [hempty] at hα
    exact hα.elim
  · let g : (ℕ → ℕ) → C(PathTime, Sphere) := fun b => (q b).1
    have hsurj : Surjective g := by
      intro γ
      obtain ⟨α,hα⟩ := hfull γ
      rw [← hqR] at hα
      obtain ⟨b,hb⟩ := hα
      exact ⟨b,congrArg Prod.fst hb⟩
    obtain ⟨b,hb,hinv⟩ := exists_nullMeasurable_baire_rightInverse
      (μ : Measure C(PathTime, Sphere)) g hq.fst hsurj
    refine ⟨fun γ => (q (b γ)).2,hq.snd.measurable.comp_nullMeasurable hb,?_⟩
    intro γ
    have hmem : q (b γ) ∈ R := hqR ▸ mem_range_self (b γ)
    have he : q (b γ) = (γ,(q (b γ)).2) := Prod.ext (hinv γ) rfl
    rwa [he] at hmem

end CircleDomainRigidity

end

end OAI
