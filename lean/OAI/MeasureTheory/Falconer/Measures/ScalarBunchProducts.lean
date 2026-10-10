import OAI.MeasureTheory.Falconer.Geometry.ScalarBunchGeometry

namespace OAI

/-! Finite ledger products in the exact form used by the path tree. -/
namespace Falconer

 theorem scalar_list_product_powers {α : Type*} (L : List α) (f : α → ℕ) :
    (∏ i ∈ Finset.range L.length, (L.map (fun x => 2^(f x))).getD i 1) =
      2^((L.map f).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    rw [Finset.prod_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero]
    rw [ih,pow_add,Nat.mul_comm]

 theorem scalar_list_sum_logs {α : Type*} (L : List α) (f : α → ℕ) :
    (∑ i ∈ Finset.range L.length, Real.log ((L.map f).getD i 1 : ℝ)) =
      (L.map (fun x => Real.log (f x : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero]
    rw [ih,add_comm]

 theorem scalarBunchBoundary_length (lo : ℕ) (bs : List ScalarBunch) :
    scalarBunchBoundary lo bs bs.length = lo := by
  apply List.getD_eq_default
  simp

namespace Regularization

 theorem scalar_prefix_points_subset (Q : Finset (CellPath 1)) (a : ℕ) (x : ℝ) :
    scalarPrefixPoints Q a x ⊆ Q.image scalarPathCenter :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end Regularization
end Falconer

end OAI
