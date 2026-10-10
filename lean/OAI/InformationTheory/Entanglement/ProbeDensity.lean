import OAI.InformationTheory.Entanglement.ConditionalUpdate
import OAI.InformationTheory.Entanglement.MatrixFamilyDensity
import OAI.InformationTheory.Entanglement.ProbePOVM

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators MeasureTheory ProbabilityTheory
namespace SecretKey
variable {Ω T : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace T]
variable {ν : Measure Ω} [IsFiniteMeasure ν] {t : Ω → T} (ht : Measurable t)
include ht in

lemma transcript_density_condExp {a : Set Ω} (ha : MeasurableSet a)
    {f : T → ℝ} (hfm : Measurable f) (hfi : Integrable f ((@Measure.map Ω T mΩ _ t ν)))
    (hf : ∀ s, MeasurableSet s → (∫ u in s, f u ∂(@Measure.map Ω T mΩ _ t ν))=ν.real (a∩t⁻¹' s)) :
    (fun x => f (t x)) =ᵐ[ν] (ν⟦a | MeasurableSpace.comap t inferInstance⟧) := by
  have hsub : MeasurableSpace.comap t inferInstance ≤ mΩ := ht.comap_le
  have hcomp : Integrable (fun x => f (t x)) ν := (integrable_map_measure hfm.aestronglyMeasurable ht.aemeasurable).mp hfi
  apply ae_eq_condExp_of_forall_setIntegral_eq hsub ((integrable_const (1 : ℝ)).indicator ha)
  · intro s hs _
    exact hcomp.integrableOn
  · intro s hs _
    obtain ⟨u,hu,rfl⟩ := hs
    rw [← setIntegral_map hu hfm.aestronglyMeasurable ht.aemeasurable,hf u hu]
    simp [integral_indicator ha, measureReal_def, Measure.restrict_apply ha,Set.inter_comm]
  · exact (hfm.comp (comap_measurable t)).stronglyMeasurable.aestronglyMeasurable

lemma independent_transcript_densities [StandardBorelSpace Ω]
    {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hind : CondIndep (MeasurableSpace.comap t inferInstance) A B ht.comap_le ν)
    {a b : Set Ω} (ha : MeasurableSet[A] a) (hb : MeasurableSet[B] b)
    {f g h : T → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hfi : Integrable f ((@Measure.map Ω T mΩ _ t ν))) (hgi : Integrable g ((@Measure.map Ω T mΩ _ t ν)))
    (hhi : Integrable h ((@Measure.map Ω T mΩ _ t ν)))
    (hf : ∀ s, MeasurableSet s → (∫ u in s, f u ∂(@Measure.map Ω T mΩ _ t ν))=ν.real (a∩t⁻¹' s))
    (hg : ∀ s, MeasurableSet s → (∫ u in s, g u ∂(@Measure.map Ω T mΩ _ t ν))=ν.real (b∩t⁻¹' s))
    (hh : ∀ s, MeasurableSet s → (∫ u in s, h u ∂(@Measure.map Ω T mΩ _ t ν))=ν.real ((a∩b)∩t⁻¹' s)) :
    h =ᵐ[(@Measure.map Ω T mΩ _ t ν)] f*g := by
  have he := (condIndep_iff _ _ _ ht.comap_le hA hB ν).mp hind a b ha hb
  have hf' := transcript_density_condExp ht (hA a ha) hfm hfi hf
  have hg' := transcript_density_condExp ht (hB b hb) hgm hgi hg
  have hh' := transcript_density_condExp ht ((hA a ha).inter (hB b hb)) hhm hhi hh
  apply (ae_map_iff ht.aemeasurable (measurableSet_eq_fun hhm (hfm.mul hgm))).mpr
  exact hh'.trans (he.trans (hf'.mul hg').symm)
end SecretKey

end

end OAI
