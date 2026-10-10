import OAI.Probability.InvariantIsing.Spectral.SpectralNullBoundaryPartition

namespace OAI

/-! Deterministic spectral labels associated with a finite measurable
partition, allowing empty cells until zero masses are removed. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function

namespace InvariantIsing

def spectralPartitionIndex {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (x : ℝ) : ι := (hcover x).choose

lemma spectralPartitionIndex_mem {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (x : ℝ) : x∈S (spectralPartitionIndex S hcover x) :=
  (hcover x).choose_spec

lemma spectralPartitionIndex_eq_iff {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S)) (x : ℝ) (i : ι) :
    spectralPartitionIndex S hcover x=i ↔ x∈S i := by
  constructor
  · intro h
    rw [← h]
    exact spectralPartitionIndex_mem S hcover x
  · intro hx
    by_contra hne
    exact (Set.disjoint_left.mp (hdis hne)) (spectralPartitionIndex_mem S hcover x) hx

lemma measurable_spectralPartitionIndex {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) : Measurable (spectralPartitionIndex S hcover) := by
  intro T _hT
  have he : (spectralPartitionIndex S hcover) ⁻¹' T=⋃ i∈T, S i := by
    ext x
    simp only [Set.mem_preimage,Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨spectralPartitionIndex S hcover x,hx,spectralPartitionIndex_mem S hcover x⟩
    · rintro ⟨i,hi,hxi⟩
      rwa [(spectralPartitionIndex_eq_iff S hcover hdis x i).mpr hxi]
  rw [he]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hS i

end InvariantIsing

end

end OAI
