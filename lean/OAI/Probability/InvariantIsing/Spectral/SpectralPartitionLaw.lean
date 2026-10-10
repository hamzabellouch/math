import OAI.Probability.InvariantIsing.Spectral.SpectralPartitionIndex
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! The exact finite spectral law produced by a measurable partition. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

lemma spectralPartitionIndex_preimage {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S)) (i : ι) :
    (spectralPartitionIndex S hcover) ⁻¹' {i}=S i := by
  ext x
  exact spectralPartitionIndex_eq_iff S hcover hdis x i

lemma spectralPartitionWeights_sum {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) : ∑ i, μ.real (S i)=1 := by
  let : MeasurableSpace ι := ⊤
  have hm := measurable_spectralPartitionIndex S hcover hdis hS
  have hh := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (f := spectralPartitionIndex S hcover) (fun i _ => hm (measurableSet_singleton i))
  simpa only [spectralPartitionIndex_preimage S hcover hdis,Finset.coe_univ,
    Set.preimage_univ,probReal_univ] using hh

lemma spectralPartition_pushforward {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (lam : ι → ℝ) :
    μ.map (fun x => lam (spectralPartitionIndex S hcover x))=
      finiteSpectralMeasure (fun i => μ.real (S i)) lam := by
  let : MeasurableSpace ι := ⊤
  have hm := measurable_spectralPartitionIndex S hcover hdis hS
  have hl : Measurable lam := measurable_of_countable lam
  change μ.map (lam ∘ spectralPartitionIndex S hcover)=_
  rw [← Measure.map_map hl hm, Measure.map_eq_sum μ _ hm,
    Measure.map_sum hl.aemeasurable]
  change Measure.sum (fun i => Measure.map lam (μ ((spectralPartitionIndex S hcover) ⁻¹' {i}) •
    Measure.dirac i))=Measure.sum (fun i => ENNReal.ofReal (μ.real (S i)) • Measure.dirac (lam i))
  congr 1
  funext i
  rw [spectralPartitionIndex_preimage S hcover hdis, Measure.map_smul _ hl.aemeasurable,
    Measure.map_dirac]
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ (S i))]

end InvariantIsing

end

end OAI
