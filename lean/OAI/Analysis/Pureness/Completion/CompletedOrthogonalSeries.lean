import OAI.Analysis.Pureness.Completion.CompletedOrthogonalRanks
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedRootRank_finset_orthogonal (τ : TracialState A) {ι : Type*} (I : Finset ι)
    (a : ι → CornerCompletion A) (ha : ∀ i, 0 ≤ a i)
    (ho : ∀ i j, i ≠ j → a i * a j = 0) :
    completedRootRank τ (∑ i ∈ I, a i) = ∑ i ∈ I, completedRootRank τ (a i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [completedRootRank_add_orthogonal τ _ _ (ha i) (Finset.sum_nonneg fun j _ => ha j), ih]
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact ho i j (fun hij => hi (hij ▸ hj))

theorem completedRootRank_tsum_orthogonal (τ : TracialState A)
    (a : ℕ → CornerCompletion A) (ha : ∀ i, 0 ≤ a i)
    (ho : ∀ i j, i ≠ j → a i * a j = 0) (hs : Summable a) :
    completedRootRank τ (∑' i, a i) = ∑' i, completedRootRank τ (a i) := by
  have hpos : 0 ≤ ∑' i, a i := tsum_nonneg ha
  rw [ENNReal.tsum_eq_iSup_nat]
  apply le_antisymm
  · apply completedRootRank_le_of_tendsto τ (fun k => Finset.sum_nonneg fun i _ => ha i)
      hpos hs.hasSum.tendsto_sum_nat
    intro k
    rw [completedRootRank_finset_orthogonal τ _ a ha ho]
    exact le_iSup (fun k => ∑ i ∈ Finset.range k, completedRootRank τ (a i)) k
  · apply iSup_le
    intro k
    rw [← completedRootRank_finset_orthogonal τ _ a ha ho]
    exact completedRootRank_mono_positive τ _ _ (Finset.sum_nonneg fun i _ => ha i)
      (Summable.sum_le_tsum (Finset.range k) (fun i _ => ha i) hs)
end CuntzPureness

end

end OAI
