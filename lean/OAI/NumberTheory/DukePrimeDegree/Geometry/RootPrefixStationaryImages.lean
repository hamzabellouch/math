import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixSupport
import OAI.NumberTheory.DukePrimeDegree.Geometry.StationaryRestrictions

namespace OAI

/-! # Transferring local stationarity through actual quotient boxes

The image restriction is the pushforward of the coordinate restriction.
Consequently a local integral identity for one ambient Markov kernel gives
a stationary restriction of the original ambient measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates n P V} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem measurableSet_param_image
    (B : RootPrefixBox C c hP hf g)
    (S : Set ((UpperRootTransverse n × V) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain) :
    MeasurableSet (C.timeParam c hP hf g '' S) := by
  have he : B.param '' (Subtype.val ⁻¹' S) = C.timeParam c hP hf g '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSB hz⟩,hz,rfl⟩
  rw [←he]
  exact B.embedding.measurableEmbedding.measurableSet_image.mpr
    (hS.preimage measurable_subtype_coe)

theorem stationary_image_of_local_integrals
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (κ : Kernel (X n) (X n)) [IsMarkovKernel κ]
    (S : Set ((UpperRootTransverse n × V) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain)
    (h : ∀ A, MeasurableSet A →
      (∫ z in S, (κ (C.timeParam c hP hf g z)).real A ∂B.coordinateMeasure μ) =
        (B.coordinateMeasure μ).real ((C.timeParam c hP hf g ⁻¹' A) ∩ S)) :
    (μ.restrict (C.timeParam c hP hf g '' S)).bind κ =
      μ.restrict (C.timeParam c hP hf g '' S) := by
  let F := C.timeParam c hP hf g
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hm := B.map_restricted_coordinates μ S hS hSB
  apply bind_eq_of_real_integrals κ
  intro A hA
  rw [← hm]
  change (∫ y, (κ y).real A ∂((B.coordinateMeasure μ).restrict S).map F) = _
  rw [integral_map hF.aemeasurable (f := fun y => (κ y).real A)
    (κ.measurable_coe hA).ennreal_toReal.aestronglyMeasurable]
  change (∫ z in S, (κ (F z)).real A ∂B.coordinateMeasure μ) = _
  rw [h A hA]
  exact congrArg ENNReal.toReal
    (Measure.map_apply hF hA |>.trans (Measure.restrict_apply (hA.preimage hF))).symm

theorem stationary_image_of_local_event
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (κ : Kernel (X n) (X n)) [IsMarkovKernel κ]
    (E : Set ((UpperRootTransverse n × V) × c.Time)) (hE : MeasurableSet E)
    (h : ∀ A, MeasurableSet A →
      (∫ z in E, (κ (C.timeParam c hP hf g z)).real A ∂B.coordinateMeasure μ) =
        (B.coordinateMeasure μ).real ((C.timeParam c hP hf g ⁻¹' A) ∩ E)) :
    (μ.restrict (C.timeParam c hP hf g '' (E ∩ B.domain))).bind κ =
      μ.restrict (C.timeParam c hP hf g '' (E ∩ B.domain)) := by
  have hdom := B.coordinateMeasure_ae_domain μ
  have heq : (B.coordinateMeasure μ).restrict (E ∩ B.domain) =
      (B.coordinateMeasure μ).restrict E := by
    apply Measure.restrict_congr_set
    filter_upwards [hdom] with z hz
    simp only [mem_inter_iff, hz, and_true]
  apply B.stationary_image_of_local_integrals μ κ (E ∩ B.domain)
    (hE.inter (B.transverse_open.prod B.time_open).measurableSet) inter_subset_right
  intro A hA
  rw [heq]
  rw [h A hA]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hdom] with z hz
  simp only [mem_inter_iff, hz, and_true]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
