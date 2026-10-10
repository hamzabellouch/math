import OAI.Probability.FreeIsing.Estimates.FreeLawSymmetry
import OAI.Probability.FreeIsing.Factors.Transport
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedSymmetry

def gaussianNoiseLaw (ι : Type*) (variance : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)

instance gaussianNoiseLaw_probability (ι : Type*) (variance : ℝ≥0) :
    IsProbabilityMeasure (gaussianNoiseLaw ι variance) := by
  unfold gaussianNoiseLaw
  infer_instance

theorem gaussianNoiseLaw_map_neg (ι : Type*) (variance : ℝ≥0) :
    (gaussianNoiseLaw ι variance).map Neg.neg = gaussianNoiseLaw ι variance := by
  change (Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)).map
      (fun x i => -x i) = Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
  simp only [gaussianReal_map_neg, neg_zero]

theorem gaussianNoiseLaw_measurePreserving_neg (ι : Type*) (variance : ℝ≥0) :
    MeasurePreserving Neg.neg (gaussianNoiseLaw ι variance) (gaussianNoiseLaw ι variance) :=
  ⟨measurable_neg, gaussianNoiseLaw_map_neg ι variance⟩

def observation {ι : Type*} (t : ℝ) (p : (ι → IsingSpin) × (ι → ℝ)) : ι → ℝ :=
  fun v => t * spinSign (p.1 v) + p.2 v

theorem measurable_observation {ι : Type*} (t : ℝ) :
    Measurable (observation (ι := ι) t) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval (fun vertex =>
    ((hsign.comp ((measurable_pi_apply vertex).comp measurable_fst)).const_mul t).add
      ((measurable_pi_apply vertex).comp measurable_snd))

theorem observation_flip {ι : Type*} (t : ℝ) (p : (ι → IsingSpin) × (ι → ℝ)) :
    observation t (Prod.map flipConfig Neg.neg p) = -observation t p := by
  funext v
  cases hs : p.1 v <;> simp [observation, flipConfig, IsingSpin.flip, spinSign, hs] <;> ring

def jointObservation {ι : Type*} (t : ℝ) (p : (ι → IsingSpin) × (ι → ℝ)) :
    (ι → IsingSpin) × (ι → ℝ) := (p.1, observation t p)

theorem measurable_jointObservation {ι : Type*} (t : ℝ) :
    Measurable (jointObservation (ι := ι) t) :=
  measurable_fst.prodMk (measurable_observation t)

theorem jointObservation_flip {ι : Type*} (t : ℝ)
    (p : (ι → IsingSpin) × (ι → ℝ)) :
    jointObservation t (Prod.map flipConfig Neg.neg p) =
      Prod.map flipConfig Neg.neg (jointObservation t p) := by
  apply Prod.ext
  · rfl
  · exact observation_flip t p

theorem product_measurePreserving_flip {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)} [SFinite mu] [SFinite nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) :
    MeasurePreserving (Prod.map flipConfig Neg.neg) (mu.prod nu) (mu.prod nu) :=
  (show MeasurePreserving flipConfig mu mu from ⟨measurable_flipConfig, hmu⟩).prod
    (show MeasurePreserving Neg.neg nu nu from ⟨measurable_neg, hnu⟩)

theorem jointObservationLaw_flip_invariant {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)} [SFinite mu] [SFinite nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) (t : ℝ) :
    ((mu.prod nu).map (jointObservation t)).map (Prod.map flipConfig Neg.neg) =
      (mu.prod nu).map (jointObservation t) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hmu hnu)
    (measurable_flipConfig.prodMap measurable_neg) (measurable_jointObservation t)
    (Filter.Eventually.of_forall (jointObservation_flip t))

theorem observationLaw_neg_invariant {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)} [SFinite mu] [SFinite nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) (t : ℝ) :
    ((mu.prod nu).map (observation t)).map Neg.neg = (mu.prod nu).map (observation t) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hmu hnu) measurable_neg (measurable_observation t)
    (Filter.Eventually.of_forall (observation_flip t))

theorem freeIsing_gaussian_observationLaw_neg_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (t : ℝ) (variance : ℝ≥0) :
    ((mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map (observation t)).map Neg.neg =
      (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map (observation t) := by
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  exact observationLaw_neg_invariant hmu.flip_invariant
    (gaussianNoiseLaw_map_neg (TreeVertex d) variance) t

theorem freeIsing_gaussian_jointLaw_flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (t : ℝ) (variance : ℝ≥0) :
    ((mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map (jointObservation t)).map
        (Prod.map flipConfig Neg.neg) =
      (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map (jointObservation t) := by
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  exact jointObservationLaw_flip_invariant hmu.flip_invariant
    (gaussianNoiseLaw_map_neg (TreeVertex d) variance) t

end Problem367.PlantedSymmetry

end

end OAI
