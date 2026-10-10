import OAI.Probability.FreeIsing.Estimates.FreeLawStationarity
import OAI.Probability.FreeIsing.Posterior.PlantedSymmetry
import OAI.Probability.FreeIsing.Spins.Moments

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem measurePreserving_iid_relabel (nu : Measure A) [IsProbabilityMeasure nu]
    (g : TreeAut d) :
    MeasurePreserving (relabel g)
      (Measure.infinitePi (fun _ : TreeVertex d => nu))
      (Measure.infinitePi (fun _ : TreeVertex d => nu)) := by
  refine ⟨measurable_relabel g, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective

theorem measurePreserving_planted_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  let := hmu.isProbabilityMeasure
  exact (hmu.measurePreserving_relabel g).prod (measurePreserving_iid_relabel nu g)

def coordinateMap (F : IsingSpin → A → B)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : TreeVertex d → B :=
  fun v => F (p.1 v) (p.2 v)

theorem measurable_coordinateMap {F : IsingSpin → A → B}
    (hF : Measurable (Function.uncurry F)) : Measurable (coordinateMap (d := d) F) := by
  apply Measurable.of_eval
  intro v
  change Measurable ((Function.uncurry F) ∘
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => (p.1 v, p.2 v)))
  exact hF.comp (by fun_prop)

omit [MeasurableSpace A] [MeasurableSpace B] in

theorem coordinateMap_relabel (F : IsingSpin → A → B) (g : TreeAut d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    coordinateMap F (Prod.map (relabel g) (relabel g) p) =
      relabel g (coordinateMap F p) := rfl

theorem map_coordinateMap_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (F : IsingSpin → A → B)
    (hF : Measurable (Function.uncurry F)) (g : TreeAut d) :
    ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
      (coordinateMap F)).map (relabel g) =
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
        (coordinateMap F) := by
  rw [Measure.map_map (measurable_relabel g) (measurable_coordinateMap hF)]
  change (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
    (coordinateMap F ∘ Prod.map (relabel g) (relabel g)) = _
  rw [← Measure.map_map (measurable_coordinateMap hF)
    ((measurable_relabel g).prodMap (measurable_relabel g)),
    (measurePreserving_planted_relabel hmu nu g).map_eq]

theorem measurePreserving_coordinateMap_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu] (F : IsingSpin → A → B)
    (hF : Measurable (Function.uncurry F)) (g : TreeAut d) :
    MeasurePreserving (relabel g)
      ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map (coordinateMap F))
      ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map (coordinateMap F)) :=
  ⟨measurable_relabel g, map_coordinateMap_relabel hmu nu F hF g⟩

theorem freeIsing_gaussian_observationLaw_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (t : ℝ) (variance : ℝ≥0) (g : TreeAut d) :
    ((mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
      (PlantedSymmetry.observation t)).map (relabel g) =
      (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
        (PlantedSymmetry.observation t) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact map_coordinateMap_relabel hmu (ProbabilityTheory.gaussianReal 0 variance)
    (fun s b => t * spinSign s + b)
    (((hsign.comp measurable_fst).const_mul t).add measurable_snd) g

theorem freeIsing_gaussian_jointLaw_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (t : ℝ) (variance : ℝ≥0) (g : TreeAut d) :
    ((mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
      (PlantedSymmetry.jointObservation t)).map
        (Prod.map (relabel g) (relabel g)) =
      (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
        (PlantedSymmetry.jointObservation t) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_planted_relabel hmu (ProbabilityTheory.gaussianReal 0 variance) g)
    ((measurable_relabel g).prodMap (measurable_relabel g))
    (PlantedSymmetry.measurable_jointObservation t)
    (Filter.Eventually.of_forall (fun _ => rfl))

end Problem367.PlantedStationarity

end

end OAI
