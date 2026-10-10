import OAI.Combinatorics.BalancedRyser.Local.ReusePrefixExtension
import OAI.Combinatorics.BalancedRyser.Local.ReusePrescriptions
import OAI.Combinatorics.BalancedRyser.Local.ReuseWeightedBound

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators
noncomputable section
open scoped Classical

universe u

theorem pencilReuse_proof : Local.PencilReuseResult.{u} := by
  intro K hK
  refine ⟨ReuseTower.reuseBoundConstant K, ReuseTower.reuseBoundConstant_pos K,
    0, ?_⟩
  intro F _ _ _ _ Q w hw p
  have hsum := ReuseTower.sum_weightedWitnessMass_le_of_prefix_extensions
    K hK.le p (fun pre hpre j hj =>
      ReuseTower.prefixWeight_extension_le K hK.le p pre hpre j hj)
  have hselected := ReusePrescription.selected_reuse_le_reversed_function_sum
    Q w K hK.le hw p
  apply hselected.trans
  calc
    (∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t).reverse
        then ReuseTower.prefixWeight K p (List.ofFn t).reverse else 0) =
        ∑ n ∈ Finset.range 7, ReuseTower.weightedWitnessMass K p n := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold ReuseTower.weightedWitnessMass
      apply Finset.sum_congr rfl
      intro t ht
      exact (ReuseTower.score_cutoff_weight_eq K p (List.ofFn t).reverse 3).symm
    _ = ∑ n : Fin 7, ReuseTower.weightedWitnessMass K p n.val := by
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ _ := hsum

end
end Balanced

end OAI
