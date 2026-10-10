import OAI.Probability.FreeIsing.Posterior.FiniteIsingFilteringRepresentation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
variable (hmB : ∀ i t, Measurable (B i t))

theorem observationFiltration_mono_of_subset
    {D E : Finset (TreeVertex d)} (hDE : D ⊆ E) :
    observationFiltration B hmB D ≤ observationFiltration B hmB E := by
  intro t
  change (⨆ i : D, Filtration.natural (plantedArrayObservation B signal i)
    (fun s => (plantedArrayObservation_measurable hmB measurable_signal i s).stronglyMeasurable) t) ≤
    ⨆ i : E, Filtration.natural (plantedArrayObservation B signal i)
      (fun s => (plantedArrayObservation_measurable hmB measurable_signal i s).stronglyMeasurable) t
  exact iSup_le fun i => le_iSup_of_le ⟨i.1, hDE i.2⟩ le_rfl

theorem observationFiltration_le_arrayObservationFiltration
    (D : Finset (TreeVertex d)) :
    observationFiltration B hmB D ≤
      arrayObservationFiltration B hmB signal measurable_signal := by
  intro t
  change (⨆ i : D, Filtration.natural (plantedArrayObservation B signal i)
    (fun s => (plantedArrayObservation_measurable hmB measurable_signal i s).stronglyMeasurable) t) ≤
    ⨆ i : TreeVertex d, Filtration.natural (plantedArrayObservation B signal i)
      (fun s => (plantedArrayObservation_measurable hmB measurable_signal i s).stronglyMeasurable) t
  exact iSup_le fun i => le_iSup_of_le i.1 le_rfl

theorem observationFiltration_monotone
    {D : ℕ → Finset (TreeVertex d)} (hD : Monotone D) :
    Monotone (fun n => observationFiltration B hmB (D n)) := by
  intro n m hnm
  exact observationFiltration_mono_of_subset B hmB (hD hnm)

theorem observationFiltration_time_monotone
    {D : ℕ → Finset (TreeVertex d)} (hD : Monotone D) (t : ℝ≥0) :
    Monotone (fun n => observationFiltration B hmB (D n) t) := by
  intro n m hnm
  exact observationFiltration_mono_of_subset B hmB (hD hnm) t

theorem iSup_observationFiltration_eq_arrayObservationFiltration
    {κ : Type*} (D : κ → Finset (TreeVertex d))
    (hcover : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) :
    (⨆ n, observationFiltration B hmB (D n) t) =
      arrayObservationFiltration B hmB signal measurable_signal t := by
  apply le_antisymm
  · exact iSup_le fun n => observationFiltration_le_arrayObservationFiltration B hmB (D n) t
  · change (⨆ i : TreeVertex d, Filtration.natural (plantedArrayObservation B signal i)
      (fun s => (plantedArrayObservation_measurable hmB measurable_signal i s).stronglyMeasurable) t) ≤ _
    refine iSup_le fun i => ?_
    obtain ⟨n, hn⟩ := hcover i
    apply le_iSup_of_le n
    change _ ≤ ⨆ j : D n, Filtration.natural (plantedArrayObservation B signal j)
      (fun s => (plantedArrayObservation_measurable hmB measurable_signal j s).stronglyMeasurable) t
    exact le_iSup_of_le ⟨i, hn⟩ le_rfl

end Problem367.FiniteIsingFiltering

end

end OAI
