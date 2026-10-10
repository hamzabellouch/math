import OAI.Probability.FreeIsing.Estimates.InfiniteComponentCavity
import OAI.Probability.FreeIsing.Ising.CopySmallLogLoss

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCavityTailTransport

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral IsingCopySmallLogLoss PlantedSymmetry CavityFieldLimit

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_identDistrib_relabel [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    IdentDistrib (cavityObservable hbeta t v w)
      (cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w))
      (observationLaw μ) (observationLaw μ) := by
  have hm := measurable_cavityObservable hbeta t v w
  have hg := measurePreserving_observationLaw_relabel hμ g
  have hmap : IdentDistrib (fun x => cavityObservable hbeta t v w (relabel g x))
      (cavityObservable hbeta t v w) (observationLaw μ) (observationLaw μ) := by
    refine ⟨(hm.comp hg.measurable).aemeasurable, hm.aemeasurable, ?_⟩
    change (observationLaw μ).map ((cavityObservable hbeta t v w) ∘ relabel g) = _
    rw [← Measure.map_map hm hg.measurable, hg.map_eq]
  exact hmap.symm.trans (IdentDistrib.of_ae_eq (hm.comp hg.measurable).aemeasurable
    (cavityObservable_relabel_ae hμ hbeta g t v w))

theorem cavityObservable_identDistrib_root_component
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    IdentDistrib
      (cavityObservable hbeta t ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d))
      (fun p => Real.artanh (selectedPosterior
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p))
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have hm := measurable_infiniteCavityField hbeta
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
  have h := hobs.comp hm
  change IdentDistrib
    (cavityObservable hbeta t ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d))
    (fun p => infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩
      (ConnectedHull.root d) (observation t p))
    (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) at h
  exact h.trans (IdentDistrib.of_ae_eq ((hm.comp (measurable_observation t)).aemeasurable)
    (hμ.infiniteCavityField_eq_component hbeta t c))

theorem exists_cavityObservable_identDistrib_root_component
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {v w : TreeVertex d} (hvw : treeAdj v w) :
    ∃ c : Fin d, IdentDistrib (cavityObservable hbeta t v w)
      (fun p => Real.artanh (selectedPosterior
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p))
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root w
  have hgv : treeAdj (⟨[], List.IsChain.nil⟩ : TreeVertex d) (g.toEquiv v) := by
    rw [← hg]
    exact (g.map_adj w v).2 hvw.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv v).1 = [c] := by
    rcases hgv with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hvc : g.toEquiv v = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  have h := cavityObservable_identDistrib_relabel hμ hbeta g.symm t v w
  change IdentDistrib (cavityObservable hbeta t v w)
    (cavityObservable hbeta t (g.toEquiv v) (g.toEquiv w))
    (observationLaw μ) (observationLaw μ) at h
  rw [hvc, hg] at h
  exact ⟨c, h.trans (cavityObservable_identDistrib_root_component hμ hbeta t c)⟩

theorem cavityObservable_tail_le_of_component_tails
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {v w : TreeVertex d} (hvw : treeAdj v w) {a : ℝ} {B : ℝ≥0∞}
    (hTail : ∀ c : Fin d,
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) {p | a < |Real.artanh
        (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p)|} ≤ B) :
    observationLaw μ {x | a < |cavityObservable hbeta t v w x|} ≤ B := by
  obtain ⟨c, hc⟩ := exists_cavityObservable_identDistrib_root_component hμ hbeta t hvw
  have heq := (hc.comp measurable_abs).measure_mem_eq
    (measurableSet_Ioi : MeasurableSet (Set.Ioi a))
  exact heq.trans_le (hTail c)

theorem logVariance_small_time_of_component_tails
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d) {v w : TreeVertex d} (hvw : treeAdj v w)
    {t T : ℝ≥0} (ht : 0 < (t : ℝ)) (htT : t ≤ T) {c : ℝ}
    (hTail : ∀ i : Fin d,
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) {p | (t : ℝ) ^ (1 / 8 : ℝ) <
        |Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := i))
          ⟨[i], List.IsChain.singleton i⟩ p)|} ≤
        ENNReal.ofReal (Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) :
    logVariance hbeta μ v w t ≤
      cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
        siteVariance beta μ o t +
      min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta μ o t)
        (cavityLogTailCoefficient (Real.tanh beta)
          (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
            Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2)) :=
  logVariance_small_time_of_tail hμ hbeta o v w ht htT
    (cavityObservable_tail_le_of_component_tails hμ hbeta t hvw hTail)

end Problem367.IsingCavityTailTransport

end

end OAI
