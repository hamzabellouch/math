import OAI.Probability.FreeIsing.Estimates.DiscrepancyDensityModification
import OAI.Probability.FreeIsing.Ising.CanonicalPosteriorStops
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingContinuousCopyDensity
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

def response (hb : 0 ≤ beta) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  continuousRootResponse hb v t (projection j q)

theorem response_progressive (hb : 0 ≤ beta) (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration (response hb v j) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun i =>
      (copyContinuousField_progressive beta i j T).measurable))).stronglyMeasurable

theorem response_eq_raw_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (j : Bool) (t : ℝ≥0) :
    response hb v j t =ᵐ[copies beta μ]
      fun q => responseRow beta (ConnectedHull.root d) v ((t : ℝ), projection j q) := by
  have h := (copyProjection_measurePreserving beta μ j).quasiMeasurePreserving.ae
    (continuousRootResponse_eq_response_ae hd hμ hb hcrit v t)
  filter_upwards [h] with q hq
  simpa only [response, responseRow, Real.toNNReal_coe] using hq

private theorem rawObservation_progressive (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => projection j q v t) := by
  cases j
  · exact IsingConditionalCopyBounds.progressive_rightObservation v
  · exact IsingConditionalCopyBounds.progressive_leftObservation v

private theorem rawPosterior_progressive (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => posterior beta v t (projection j q)) :=
  isStronglyProgressive_infiniteGibbsSpinMean _ beta v _ (rawObservation_progressive j)

private theorem rawResponse_progressive (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) =>
        responseRow beta (ConnectedHull.root d) v ((t : ℝ), projection j q)) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  simpa only [Function.comp_def, responseRow, Real.toNNReal_coe] using
    ((measurable_infiniteGibbsResponse beta (ConnectedHull.root d) v).comp
      (Measurable.of_eval (fun i =>
        (rawObservation_progressive j i T).measurable))).stronglyMeasurable

def continuousDensity (hb : 0 ≤ beta) (t : ℝ≥0) : Joint d → ℝ :=
  DiscrepancyEnergy.density (fun v => response hb v true t)
    (fun v => response hb v false t) (continuousDifference beta (ConnectedHull.root d) t)
    (copyContinuousPosterior beta (ConnectedHull.root d) true t)
    (copyContinuousPosterior beta (ConnectedHull.root d) false t)

theorem continuousDensity_progressive (hb : 0 ≤ beta) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (continuousDensity (d := d) hb) :=
  DiscrepancyEnergy.isStronglyProgressive_density (ι := TreeVertex d) (Ω := Joint d)
    (fun v => response_progressive hb v true) (fun v => response_progressive hb v false)
    (continuousDifference_progressive beta (ConnectedHull.root d))
    (copyContinuousPosterior_progressive beta (ConnectedHull.root d) true)
    (copyContinuousPosterior_progressive beta (ConnectedHull.root d) false)

theorem actualDensity_progressive :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t : ℝ≥0 => IsingCopyEnergy.density beta (ConnectedHull.root d) (t : ℝ)) := by
  unfold IsingCopyEnergy.density
  simp only [Real.toNNReal_coe]
  apply DiscrepancyEnergy.isStronglyProgressive_density
  · intro v
    exact rawResponse_progressive (beta := beta) v true
  · intro v
    exact rawResponse_progressive (beta := beta) v false
  · exact (isStronglyProgressive_artanh _
      (rawPosterior_progressive (beta := beta) (ConnectedHull.root d) true)).sub
      (isStronglyProgressive_artanh _
        (rawPosterior_progressive (beta := beta) (ConnectedHull.root d) false))
  · exact rawPosterior_progressive (beta := beta) (ConnectedHull.root d) true
  · exact rawPosterior_progressive (beta := beta) (ConnectedHull.root d) false

theorem continuousDensity_eq_actual_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (t : ℝ≥0) :
    continuousDensity hb t =ᵐ[copies beta μ]
      IsingCopyEnergy.density beta (ConnectedHull.root d) (t : ℝ) := by
  unfold continuousDensity IsingCopyEnergy.density
  simp only [Real.toNNReal_coe]
  apply DiscrepancyEnergy.density_congr_ae
  · intro v
    exact response_eq_raw_ae hd hμ hb hcrit v true t
  · intro v
    exact response_eq_raw_ae hd hμ hb hcrit v false t
  · exact (continuousDifference_modification hd hμ hb hcrit (ConnectedHull.root d)).2 t
  · exact (copyContinuousPosterior_modification hd hμ hb hcrit
      (ConnectedHull.root d) true).2 t
  · exact (copyContinuousPosterior_modification hd hμ hb hcrit
      (ConnectedHull.root d) false).2 t

theorem continuousDensity_eq_actual_prod_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    (fun p : ℝ × Joint d => continuousDensity hb p.1.toNNReal p.2) =ᵐ[
        (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)]
      (fun p => IsingCopyEnergy.density beta (ConnectedHull.root d) p.1 p.2) := by
  have hmap : Measurable (fun p : ℝ × Joint d => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hl := (stronglyMeasurable_joint_of_isStronglyProgressive
    (continuousDensity_progressive hb)).comp_measurable hmap
  have hr := (stronglyMeasurable_joint_of_isStronglyProgressive
    (actualDensity_progressive (d := d) (beta := beta))).comp_measurable hmap
  have he : (fun p : ℝ × Joint d => continuousDensity hb p.1.toNNReal p.2) =ᵐ[
        (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)]
      (fun p => IsingCopyEnergy.density beta (ConnectedHull.root d)
        (p.1.toNNReal : ℝ) p.2) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hl.measurable hr.measurable)).2
    exact Filter.Eventually.of_forall fun t =>
      continuousDensity_eq_actual_ae hd hμ hb hcrit t.toNNReal
  simpa only [IsingCopyEnergy.density, responseRow, Real.toNNReal_coe] using he

theorem continuousDensity_integrable
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => continuousDensity hb p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) :=
  (IsingCopyEnergy.density_integrable hμ hb (ConnectedHull.root d) T).congr
    (continuousDensity_eq_actual_prod_ae hd hμ hb hcrit T).symm

theorem ae_all_primitive_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∀ᵐ q ∂copies beta μ, ∀ t,
      nnrealTimePrimitive (continuousDensity hb) t q =
        nnrealTimePrimitive
          (fun s : ℝ≥0 => IsingCopyEnergy.density beta (ConnectedHull.root d) (s : ℝ)) t q :=
  ae_all_nnrealTimePrimitive_eq_of_modification (continuousDensity_progressive hb)
    actualDensity_progressive (continuousDensity_eq_actual_ae hd hμ hb hcrit)

theorem ae_all_stopped_primitive_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ t,
      stoppedProcess (nnrealTimePrimitive (continuousDensity hb)) τ t q =
        stoppedProcess (nnrealTimePrimitive
          (fun s : ℝ≥0 => IsingCopyEnergy.density beta (ConnectedHull.root d) (s : ℝ))) τ t q := by
  filter_upwards [ae_all_primitive_eq_actual hd hμ hb hcrit] with q hq
  intro t
  exact hq _

theorem integral_cutoff_density_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (t : ℝ≥0) :
    (∫ q, if (t : WithTop ℝ≥0) ≤ τ q then continuousDensity hb t q else 0
      ∂copies beta μ) =
      ∫ q, if (t : WithTop ℝ≥0) ≤ τ q then
        IsingCopyEnergy.density beta (ConnectedHull.root d) (t : ℝ) q else 0
        ∂copies beta μ := by
  apply integral_congr_ae
  filter_upwards [continuousDensity_eq_actual_ae hd hμ hb hcrit t] with q hq
  by_cases ht : (t : WithTop ℝ≥0) ≤ τ q
  · simp only [ht, ite_true, hq]
  · simp only [ht, ite_false]

theorem integral_stopDensity_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (s : ℝ) :
    (∫ q, StoppedTimePrimitive.stopDensity (continuousDensity hb) τ s.toNNReal q
      ∂copies beta μ) =
      ∫ q, if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
        IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
        ∂copies beta μ := by
  simpa only [StoppedTimePrimitive.stopDensity, IsingCopyEnergy.density,
    responseRow, Real.toNNReal_coe] using
      integral_cutoff_density_eq_actual hd hμ hb hcrit τ s.toNNReal

theorem integral_integral_stopDensity_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      StoppedTimePrimitive.stopDensity (continuousDensity hb) τ s.toNNReal q
        ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
          IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
          ∂copies beta μ := by
  apply intervalIntegral.integral_congr
  intro s _
  exact integral_stopDensity_eq_actual hd hμ hb hcrit τ s

end Problem367.IsingContinuousCopyDensity

end

end OAI
