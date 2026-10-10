import OAI.Probability.DirectionalWalk.ThreeChunks

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section EntropyLawTransforms
variable {Ω Ξ α β γ : Type*} [Countable Ω] [Countable Ξ] [Countable α] [Countable β]
  [Countable γ] [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass Ω]
  [MeasurableSingletonClass Ξ] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]

omit [Countable α] [MeasurableSingletonClass α] in
lemma informationOf_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) :
    informationOf (μ.map F) X ∘ F = informationOf μ (X ∘ F) := by
  funext ω
  simp only [informationOf,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Function.comp_apply]

omit [Countable α] [MeasurableSingletonClass α] in
lemma entropyOf_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) :
    entropyOf (μ.map F) X = entropyOf μ (X ∘ F) := by
  unfold entropyOf
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  exact congrArg (fun f => ∫ ω, f ω ∂μ) (informationOf_map μ F X)

omit [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma conditionedEntropy_map (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → α) (Y : Ξ → β) :
    conditionedEntropy (μ.map F) X Y = conditionedEntropy μ (X ∘ F) (Y ∘ F) := by
  unfold conditionedEntropy conditionedInformation
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with ω
  change (informationOf (μ.map F) (fun ξ => (Y ξ,X ξ)) ∘ F) ω -
    (informationOf (μ.map F) Y ∘ F) ω = _
  rw [informationOf_map,informationOf_map]
  rfl

omit [Countable α] [Countable β] in
lemma informationOf_same_fibers (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (h : ∀ ω ξ, X ω = X ξ ↔ Y ω = Y ξ) : informationOf μ X = informationOf μ Y := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  exact h ξ ω

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_same_conditioner (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) (h : ∀ ω ξ, Y ω = Y ξ ↔ Z ω = Z ξ) :
    conditionedInformation μ X Y = conditionedInformation μ X Z := by
  have hp := informationOf_same_fibers μ (fun ω => (Y ω,X ω)) (fun ω => (Z ω,X ω))
    (fun ω ξ => by simp only [Prod.mk.injEq,h ω ξ])
  funext ω
  simp only [conditionedInformation,hp,informationOf_same_fibers μ Y Z h]

lemma conditionedEntropy_monotone_function (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Nonempty α] (X : Ω → α) (Y : Ω → β) (f : β → γ)
    (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X Y ≤ conditionedEntropy μ X (f ∘ Y) := by
  have hh := conditionedEntropy_le_conditionedEntropy μ X (f ∘ Y) Y hi
  have he : conditionedInformation μ X (fun ω => ((f ∘ Y) ω,Y ω)) =
      conditionedInformation μ X Y := by
    apply conditionedInformation_same_conditioner
    intro ω ξ
    simp only [Function.comp_apply,Prod.mk.injEq]
    exact ⟨And.right,fun h => ⟨congrArg f h,h⟩⟩
  simpa only [conditionedEntropy,he] using hh

omit [Countable α] [MeasurableSingletonClass α] in
lemma entropyOf_prod_fst (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → α) : entropyOf (μ.prod ν) (X ∘ Prod.fst) = entropyOf μ X := by
  rw [← entropyOf_map,Measure.map_fst_prod,measure_univ,one_smul]

omit [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma conditionedEntropy_prod_fst (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → α) (Y : Ω → β) :
    conditionedEntropy (μ.prod ν) (X ∘ Prod.fst) (Y ∘ Prod.fst) = conditionedEntropy μ X Y := by
  rw [← conditionedEntropy_map,Measure.map_fst_prod,measure_univ,one_smul]
end EntropyLawTransforms

end DirectionalZeroOne

end OAI
