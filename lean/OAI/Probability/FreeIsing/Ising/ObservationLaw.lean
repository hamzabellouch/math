import OAI.Probability.FreeIsing.Ising.ObservationInnovation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

instance observationLaw_probability {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (observationLaw μ) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  unfold observationLaw
  infer_instance

theorem measurePreserving_observationLaw_relabel {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (g : TreeAut d) :
    MeasurePreserving (relabel g) (observationLaw μ) (observationLaw μ) := by
  refine ⟨measurable_relabel g, ?_⟩
  apply FactorTransport.map_invariant_of_ae_equivariant
    (PlantedStationarity.measurePreserving_planted_relabel hμ uniform01 g)
    (measurable_relabel g) measurable_uniformObservation
  exact Filter.Eventually.of_forall (uniformObservation_relabel g)

def past {d : ℕ} (t : ℝ≥0) (x : Paths d) : TreeVertex d → Set.Iic t → ℝ :=
  fun v s => x v s

theorem measurable_past {d : ℕ} (t : ℝ≥0) : Measurable (past (d := d) t) :=
  Measurable.of_eval fun v =>
    Measurable.of_eval fun s => measurable_evaluation v s

theorem filtration_eq_comap_past (d : ℕ) (t : ℝ≥0) :
    filtration d t = MeasurableSpace.comap (past t) inferInstance :=
  arrayNaturalFiltration_eq_comap evaluation measurable_evaluation t

theorem filtration_comap_uniformObservation (d : ℕ) (t : ℝ≥0)
    (hm : ∀ s, Measurable (fun u => WienerSampler.sample u s)) :
    (filtration d t).comap uniformObservation =
      ArrayPosteriorStationarity.filtration
        (fun s u => WienerSampler.sample u s) hm t := by
  rw [filtration_eq_comap_past, MeasurableSpace.comap_comp]
  unfold ArrayPosteriorStationarity.filtration arrayObservationFiltration
  rw [arrayNaturalFiltration_eq_comap]
  rfl

end Problem367.IsingObservationInnovation

end

end OAI
