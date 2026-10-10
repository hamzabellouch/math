import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPathCoordinates

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkProducts
open Construction HistoryLinearization

theorem pathProduct_eq_leafStates {M : Type*} [CommMonoid M] (f : State → M)
    {l : ℕ} (h : History l) :
    (∏ path : Fin l → Bool, f (leafStateAt h path)) = (h.leafStates.map f).prod := by
  induction h with
  | leaf a => simp [leafStateAt,History.leafStates]
  | @node l a p u hp hm left right ihl ihr =>
      have ht (b : Bool) (x : Fin l → Bool) :
          Fin.tail ((Fin.consEquiv (fun _ : Fin (l+1) => Bool)) (b,x)) = x := rfl
      rw [← (Fin.consEquiv (fun _ : Fin (l+1) => Bool)).prod_comp]
      simp [ht,Fin.consEquiv_apply,Fintype.prod_prod_type,leafStateAt,History.leafStates,ihl,ihr,mul_comm]

theorem supported_bulk_eq_leaf_product {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    bulkProduct h.root.small = (h.leafStates.map (fun a => bulkProduct a.small)).prod := by
  induction h with
  | leaf a => simp [History.root,History.leafStates]
  | @node l a p u hp hm left right ihl ihr =>
      have hc := supported_child_products hs (History.supported_compensation_roles hs)
      have hp := (supported_product_split hs).1
      simp only [History.root,History.leafStates,List.map_append,List.prod_append]
      rw [← ihl (History.supported_left hs),← ihr (History.supported_right hs),hc.1,hc.2.1]
      exact hp

theorem supported_bulk_eq_path_product {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    bulkProduct h.root.small = ∏ path : Fin l → Bool, bulkProduct (leafStateAt h path).small := by
  rw [pathProduct_eq_leafStates (fun a => bulkProduct a.small) h]
  exact supported_bulk_eq_leaf_product h hs

end Ostmann.Arithmetic.HistoryBulkProducts

end

end OAI
