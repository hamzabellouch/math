import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OAI

/-! # Finite disjoint Borel products in the original ambient space -/
namespace Falconer
open Set MeasureTheory

/-- The finite partition used by the graph regularization, with its actual cardinality. -/
def HasBorelProductPartition {d : ℕ} (S : Set (Space d × Space d)) (K : ℝ) : Prop :=
  ∃ n : ℕ, (n:ℝ) ≤ K ∧ ∃ A B : Fin n → Set (Space d),
    (∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i)) ∧
    (Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) ∧
    S = ⋃ i, A i ×ˢ B i

theorem HasBorelProductPartition.mono_bound {d : ℕ} {S : Set (Space d × Space d)}
    {K L : ℝ} (h : HasBorelProductPartition S K) (hKL : K ≤ L) :
    HasBorelProductPartition S L := by
  obtain ⟨n,hn,A,B,hAB,hdis,hS⟩ := h
  exact ⟨n,hn.trans hKL,A,B,hAB,hdis,hS⟩

theorem borel_product_partition_of_finset {d : ℕ} {ι : Type*}
    (T : Finset ι) (A B : ι → Set (Space d))
    (hm : ∀ i ∈ T, MeasurableSet (A i) ∧ MeasurableSet (B i))
    (hd : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) :
    HasBorelProductPartition (⋃ i ∈ T, A i ×ˢ B i) (T.card:ℝ) := by
  classical
  let e := T.equivFin
  refine ⟨T.card,le_rfl,(fun i => A (e.symm i).val),(fun i => B (e.symm i).val),?_,?_,?_⟩
  · intro i
    exact hm _ (e.symm i).property
  · intro i j hij
    apply hd _ (e.symm i).property _ (e.symm j).property
    intro h
    apply hij
    exact e.symm.injective (Subtype.ext h)
  · ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi,hz⟩
      refine ⟨e ⟨i,hi⟩,?_⟩
      simpa only [Equiv.symm_apply_apply] using hz
    · rintro ⟨i,hz⟩
      exact ⟨(e.symm i).val,(e.symm i).property,hz⟩

theorem borel_product_partition_single {d : ℕ} {A B : Set (Space d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    HasBorelProductPartition (A ×ˢ B) 1 := by
  refine ⟨1,by norm_num,(fun _ => A),(fun _ => B),(fun _ => ⟨hA,hB⟩),?_,?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · ext z
    simp only [mem_iUnion]
    exact ⟨fun hz => ⟨0,hz⟩,fun ⟨_,hz⟩ => hz⟩

end Falconer

end OAI
