import OAI.Probability.DirectionalWalk.Entropy

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def informationOf {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : Ω → α) (ω : Ω) : ℝ := atomInfo (μ.map X) (X ω)

noncomputable def entropyOf {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : Ω → α) : ℝ := ∫ ω, informationOf μ X ω ∂μ

noncomputable def conditionedInformation {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : Ω → ℝ :=
  fun ω => informationOf μ (fun ξ => (Y ξ,X ξ)) ω - informationOf μ Y ω

noncomputable def conditionedEntropy {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  ∫ ω, conditionedInformation μ X Y ω ∂μ

section DiscreteEntropyVariables
variable {Ω α β γ : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [Countable α] in
lemma informationOf_fiber (μ : Measure Ω) (X : Ω → α) (ω : Ω) :
    informationOf μ X ω = -Real.log (μ.real {ξ | X ξ = X ω}) := by
  simp only [informationOf,atomInfo,measureReal_def,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  rfl

omit [Countable α] [Countable β] in
lemma informationOf_pair_comm (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) :
    informationOf μ (fun ω => (X ω,Y ω)) = informationOf μ (fun ω => (Y ω,X ω)) := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [and_comm]

omit [Countable α] [Countable β] [Countable γ] in
lemma informationOf_pair_assoc (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    informationOf μ (fun ω => ((X ω,Y ω),Z ω)) = informationOf μ (fun ω => (X ω,Y ω,Z ω)) := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [and_assoc]

omit [Countable α] [Countable β] in
lemma informationOf_function (μ : Measure Ω) (X : Ω → α) (f : α → β) (hf : Function.Injective f) :
    informationOf μ (f ∘ X) = informationOf μ X := by
  funext ω
  rw [informationOf_fiber,informationOf_fiber]
  congr 3
  ext ξ
  simp [hf.eq_iff]

lemma entropyOf_eq_discreteEntropy (μ : Measure Ω) (X : Ω → α) :
    entropyOf μ X = discreteEntropy (μ.map X) := by
  dsimp [entropyOf,discreteEntropy,informationOf]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]

lemma integrable_informationOf_iff (μ : Measure Ω) (X : Ω → α) :
    Integrable (informationOf μ X) μ ↔ Integrable (atomInfo (μ.map X)) (μ.map X) := by
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).symm

lemma conditionedInformation_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    conditionedInformation μ X Y =ᵐ[μ] fun ω => conditionalInfo (μ.map (fun ξ => (Y ξ,X ξ))) (Y ω,X ω) := by
  let F := fun ξ => (Y ξ,X ξ)
  have hmap : MeasurePreserving F μ (μ.map F) := ⟨measurable_of_countable _,rfl⟩
  have hmarg : (μ.map F).fst = μ.map Y := by
    simp only [Measure.fst,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  filter_upwards [hmap.quasiMeasurePreserving.ae (conditionalInfo_log (μ.map F))] with ω hω
  rw [hω,hmarg]
  simp only [conditionedInformation,informationOf,atomInfo,F]
  ring

lemma conditionedInformation_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    ∀ᵐ ω ∂μ, 0 ≤ conditionedInformation μ X Y ω := by
  filter_upwards [conditionedInformation_eq μ X Y] with ω hω
  rw [hω]
  exact conditionalInfo_nonneg _ _

lemma integrable_conditionedInformation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hi : Integrable (informationOf μ X) μ) :
    Integrable (conditionedInformation μ X Y) μ := by
  let F := fun ξ => (Y ξ,X ξ)
  let ρ := μ.map F
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hsnd : ρ.snd = μ.map X := by
    dsimp [ρ,Measure.snd]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have hmap : MeasurePreserving Prod.snd ρ ρ.snd := ⟨measurable_snd,rfl⟩
  have hi' : Integrable (atomInfo ρ.snd) ρ.snd := by
    rw [hsnd]
    exact (integrable_informationOf_iff μ X).mp hi
  have hc : Integrable (conditionalInfo ρ) ρ := integrable_conditionalInfo ρ (Kernel.const β ρ.snd)
    (by simpa only [Measure.compProd_const] using joint_ac_marginal_product ρ)
    (hmap.integrable_comp_of_integrable hi')
  have hF : MeasurePreserving F μ ρ := ⟨measurable_of_countable _,rfl⟩
  exact (hF.integrable_comp_of_integrable hc).congr (conditionedInformation_eq μ X Y).symm

lemma conditionedEntropy_le_entropyOf (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X Y ≤ entropyOf μ X := by
  let F := fun ξ => (Y ξ,X ξ)
  let ρ := μ.map F
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hsnd : ρ.snd = μ.map X := by
    dsimp [ρ,Measure.snd]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have he : conditionedEntropy μ X Y = conditionalEntropy ρ := by
    dsimp [conditionedEntropy,conditionalEntropy,ρ]
    rw [integral_congr_ae (conditionedInformation_eq μ X Y),
      integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  rw [he,entropyOf_eq_discreteEntropy,← hsnd]
  apply conditionalEntropy_le_entropy_snd
  rw [hsnd]
  exact (integrable_informationOf_iff μ X).mp hi

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    conditionedInformation μ (fun ω => (X ω,Y ω)) Z =
      fun ω => conditionedInformation μ X Z ω + conditionedInformation μ Y (fun ξ => (Z ξ,X ξ)) ω := by
  funext ω
  simp only [conditionedInformation,informationOf_pair_assoc]
  ring

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedEntropy_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (hX : Integrable (conditionedInformation μ X Z) μ)
    (hY : Integrable (conditionedInformation μ Y (fun ξ => (Z ξ,X ξ))) μ) :
    conditionedEntropy μ (fun ω => (X ω,Y ω)) Z =
      conditionedEntropy μ X Z + conditionedEntropy μ Y (fun ξ => (Z ξ,X ξ)) := by
  simp only [conditionedEntropy,conditionedInformation_chain]
  exact integral_add hX hY

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma informationOf_pair_chain (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) :
    informationOf μ (fun ω => (X ω,Y ω)) = fun ω => informationOf μ X ω + conditionedInformation μ Y X ω := by
  funext ω
  simp only [conditionedInformation]
  ring

lemma integrable_informationOf_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Integrable (informationOf μ X) μ)
    (hY : Integrable (informationOf μ Y) μ) :
    Integrable (informationOf μ (fun ω => (X ω,Y ω))) μ := by
  rw [informationOf_pair_chain]
  exact hX.add (integrable_conditionedInformation μ Y X hY)

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma entropyOf_pair_chain (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hX : Integrable (informationOf μ X) μ)
    (hY : Integrable (conditionedInformation μ Y X) μ) :
    entropyOf μ (fun ω => (X ω,Y ω)) = entropyOf μ X + conditionedEntropy μ Y X := by
  dsimp [entropyOf,conditionedEntropy]
  rw [informationOf_pair_chain,integral_add hX hY]

end DiscreteEntropyVariables

end DirectionalZeroOne

end OAI
