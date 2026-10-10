import OAI.NumberTheory.Ostmann.Arithmetic.HistoryLeafProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryTreeParameters

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryTreeParameters
open Construction HistoryBulkProducts HistoryResidueRegular HistoryLinearization

variable {q : ℕ} [Fact q.Prime]

def leafBulk : {l : ℕ} → (h : History l) → Regular q h → Tree.Leaves l → (ZMod q)ˣ
  | 0, .leaf a, hr, _ => bulkUnit (.leaf a) hr
  | _+1, .node _ _ _ _ _ left right, hr, path =>
      if path 0 then leafBulk right (right_regular hr) (Fin.tail path)
      else leafBulk left (left_regular hr) (Fin.tail path)

@[simp] theorem leafBulk_child_left {l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
    {left right : History l} (hr : Regular q (History.node a p u hp hm left right)) :
    Tree.Parameters.childLeaves (leafBulk _ hr) false = leafBulk left (left_regular hr) := by
  funext path
  simp [Tree.Parameters.childLeaves,leafBulk,Fin.tail_cons]

@[simp] theorem leafBulk_child_right {l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
    {left right : History l} (hr : Regular q (History.node a p u hp hm left right)) :
    Tree.Parameters.childLeaves (leafBulk _ hr) true = leafBulk right (right_regular hr) := by
  funext path
  simp [Tree.Parameters.childLeaves,leafBulk,Fin.tail_cons]

theorem leafBulk_coe {l : ℕ} (h : History l) (hr : Regular q h) (path : Tree.Leaves l) :
    (leafBulk h hr path : ZMod q) = (bulkProduct (leafStateAt h path).small : ZMod q) := by
  induction h with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
      simp only [leafBulk,leafStateAt]
      split_ifs
      · exact ihr (right_regular hr) (Fin.tail path)
      · exact ihl (left_regular hr) (Fin.tail path)

theorem leafProduct_leafBulk {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h) :
    Tree.Parameters.leafProduct (leafBulk h hr) = bulkUnit h hr := by
  apply Units.ext
  change (↑(∏ path, leafBulk h hr path) : ZMod q) = (bulkProduct h.root.small : ZMod q)
  change (Units.coeHom (ZMod q)) (∏ path, leafBulk h hr path) = _
  rw [map_prod]
  simp only [Units.coeHom_apply,leafBulk_coe]
  simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n:ZMod q))
    (supported_bulk_eq_path_product h hs).symm

theorem left_product_coe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    ((giantPlusUnit _ hr * leftConstant hs hr *
      Tree.Parameters.leafProduct (leafBulk left (left_regular hr)) : (ZMod q)ˣ) : ZMod q) =
      ((a.giantPlus*(hp.map SmallSlot.value).prod : ℕ) : ZMod q) := by
  rw [leafProduct_leafBulk left (History.supported_left hs)]
  change (a.giantPlus:ZMod q)*(fixedProduct hp:ZMod q)*
    (bulkProduct left.root.small:ZMod q) = _
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).1,
    product_split hp]
  simp only [Nat.cast_mul,mul_assoc]

theorem right_product_coe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    ((giantMinusUnit _ hr * rightConstant hs hr *
      Tree.Parameters.leafProduct (leafBulk right (right_regular hr)) : (ZMod q)ˣ) : ZMod q) =
      ((a.giantMinus*(hm.map SmallSlot.value).prod : ℕ) : ZMod q) := by
  rw [leafProduct_leafBulk right (History.supported_right hs)]
  change (a.giantMinus:ZMod q)*(fixedProduct hm:ZMod q)*
    (bulkProduct right.root.small:ZMod q) = _
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).2.1,
    product_split hm]
  simp only [Nat.cast_mul,mul_assoc]

end Ostmann.Arithmetic.HistoryTreeParameters

end

end OAI
