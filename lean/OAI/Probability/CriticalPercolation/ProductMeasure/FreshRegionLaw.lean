import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma trim_law_eq (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e) :
    (law q).map (forceOn Sᶜ ∅)=(law r).map (forceOn Sᶜ ∅) := by
  rw [forceOn_map_law,forceOn_map_law]
  congr 1
  funext e
  by_cases he : e∈S
  · simp [pinnedParameters,he,h e he]
  · simp [pinnedParameters,he]

lemma fresh_region_lower (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e)
    (B : Set (Set E)) (hm : MeasurableSet B) (hu : IsUpperSet B) :
    (law r).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ (law q).real B := by
  have he : (law r) ((forceOn Sᶜ ∅) ⁻¹' B)=(law q) ((forceOn Sᶜ ∅) ⁻¹' B) := by
    rw [← Measure.map_apply (measurable_forceOn _ _) hm,
      ← Measure.map_apply (measurable_forceOn _ _) hm,trim_law_eq q r S h]
  rw [measureReal_def,he]
  change (law q).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ _
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  apply hu (a := forceOn Sᶜ ∅ ω) (b := ω) ?_ hω
  intro e he
  by_cases hes : e∈S
  · simpa [forceOn,hes] using he
  · simp [hes] at he

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
