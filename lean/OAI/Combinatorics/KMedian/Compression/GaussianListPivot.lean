import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations

namespace OAI


                                         
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
 theorem pivot_ofFn {n : ℕ} (f : Fin n → ℚ)
    (h : (univ.filter (fun j => f j≠0)).Nonempty) :
    pivot (List.ofFn f)=(univ.filter (fun j => f j≠0)).min' h := by
  let p := (univ.filter (fun j => f j≠0)).min' h
  change (List.ofFn f).findIdx (fun q => decide (q≠0))=p.val
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using p.isLt)).mpr
  constructor
  · simpa only [List.getElem_ofFn,decide_eq_true_eq] using (mem_filter.mp (min'_mem _ h)).2
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not,not_not]
    by_contra hz
    have hm : p ≤ (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) := min'_le (univ.filter (fun j => f j≠0)) (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) (mem_filter.mpr ⟨mem_univ _,hz⟩)
    exact (not_le_of_gt hj) hm
 theorem pivot_ofFn_zero {n : ℕ} (f : Fin n → ℚ)
    (h : ¬(univ.filter (fun j => f j≠0)).Nonempty) :
    pivot (List.ofFn f)=n := by
  change (List.ofFn f).findIdx (fun q => decide (q≠0))=n
  apply Eq.trans (b:=(List.ofFn f).length) ?_ List.length_ofFn
  apply List.findIdx_eq_length_of_false
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  simp only [decide_eq_false_iff_not,not_not]
  by_contra hz
  exact h ⟨j,mem_filter.mpr ⟨mem_univ _,hz⟩⟩
end MetricKMedian.Gaussian.ListOperation
end

end OAI
