import OAI.Probability.BenjaminiSchramm.PeakComparison
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm
variable {E : Type*}

lemma finset_subset_monotone_iUnion (s : Finset E) (W : ℕ → Set E) (hW : Monotone W)
    (hs : (s : Set E) ⊆ ⋃ n, W n) : ∃ n, (s : Set E) ⊆ W n := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert e s he ih =>
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hs (Finset.mem_insert_self e s))
    obtain ⟨m,hm⟩ := ih (fun _ h => hs (Finset.mem_insert_of_mem h))
    refine ⟨max n m,?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hW (le_max_left _ _) hn
    · exact hW (le_max_right _ _) (hm hf)

lemma finiteWitness_mem_iUnion_iff (A : Set (Set E)) (hA : IsUpperSet A) (hfA : FiniteWitness A)
    (W : ℕ → Set E) (hW : Monotone W) : (⋃ n, W n) ∈ A ↔ ∃ n, W n ∈ A := by
  constructor
  · intro h
    obtain ⟨s,hs,hsa⟩ := hfA _ h
    obtain ⟨n,hn⟩ := finset_subset_monotone_iUnion s W hW hs
    exact ⟨n,hA hn hsa⟩
  · rintro ⟨n,hn⟩
    exact hA (Set.subset_iUnion W n) hn

theorem law_finiteWitness_left_tendsto [Countable E]
    (A : Set (Set E)) (hA : IsUpperSet A) (hfA : FiniteWitness A)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => law (q n) A) atTop (𝓝 (law p A)) := by
  let B := fun n => CriticalPercolation.BernoulliProduct.atParameter (q n) ⁻¹' A
  have hmA := measurableSet_finiteWitness A hA hfA
  have hB : Monotone B := by
    intro n m hnm u hu
    exact hA (CriticalPercolation.BernoulliProduct.atParameter_mono u (hmono hnm)) hu
  have heq : (⋃ n, B n) = CriticalPercolation.BernoulliProduct.atParameter p ⁻¹' A := by
    ext u
    simp only [Set.mem_iUnion,Set.mem_preimage]
    rw [← CriticalPercolation.BernoulliProduct.atParameter_iUnion p q hqp hq u]
    exact (finiteWitness_mem_iUnion_iff A hA hfA _
      (fun n m hnm => CriticalPercolation.BernoulliProduct.atParameter_mono u (hmono hnm))).symm
  have hμ (r : unitInterval) : CriticalPercolation.BernoulliProduct.markLaw
      (CriticalPercolation.BernoulliProduct.atParameter r ⁻¹' A) = law r A := by
    rw [← Measure.map_apply (CriticalPercolation.BernoulliProduct.measurable_atParameter r) hmA,
      CriticalPercolation.BernoulliProduct.markLaw_map_atParameter,
      CriticalPercolation.BernoulliProduct.law_const]
    rfl
  have h := tendsto_measure_iUnion_atTop (μ := CriticalPercolation.BernoulliProduct.markLaw)
    hB
  rw [heq,hμ] at h
  simpa only [Function.comp_def,B,hμ] using h

end Percolation.BenjaminiSchramm

end

end OAI
