import OAI.Probability.InvariantIsing.Spectral.SpectralNullBoundaryCover
import Mathlib.Order.Disjointed

namespace OAI

/-! Ordered disjointization preserves the null boundaries required by
the spectral empirical-measure convergence argument. -/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace InvariantIsing

lemma null_frontier_sdiff (μ : Measure ℝ) (A B : Set ℝ)
    (hA : μ (frontier A)=0) (hB : μ (frontier B)=0) : μ (frontier (A\B))=0 := by
  apply measure_mono_null _ (measure_union_null_iff.mpr ⟨hA,hB⟩)
  intro x hx
  have hh := frontier_inter_subset A Bᶜ hx
  rcases hh with ⟨ha,_⟩ | ⟨_,hb⟩
  · exact Or.inl ha
  · exact Or.inr (by simpa only [frontier_compl] using hb)

lemma null_frontier_finsetUnion {ι : Type*} (μ : Measure ℝ) (t : Finset ι)
    (B : ι → Set ℝ) (hB : ∀ i∈t, μ (frontier (B i))=0) :
    μ (frontier (⋃ i∈t, B i))=0 := by
  apply measure_mono_null (t.frontier_biUnion_subset B)
  exact (measure_biUnion_null_iff t.countable_toSet).mpr hB

lemma null_frontier_disjointed {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (hB : ∀ i, μ (frontier (B i))=0) (i : Fin n) :
    μ (frontier (disjointed B i))=0 := by
  rw [disjointed_apply,Finset.sup_eq_iSup]
  exact null_frontier_sdiff μ _ _ (hB i)
    (null_frontier_finsetUnion μ (Finset.Iio i) B (fun j _ => hB j))

end InvariantIsing

end

end OAI
