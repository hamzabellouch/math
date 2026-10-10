import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramPrime

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistoryBulkProducts HistoryResidueRegular HistoryTreeParameters
variable {q : ℕ} [Fact q.Prime]
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
variable {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem left_product_variable
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (X : (ZMod q)ˣ) :
    ((X*leftConstant hs hr*Tree.Parameters.leafProduct (leafBulk left (left_regular hr)):
      (ZMod q)ˣ):ZMod q)=(X:ZMod q)*((hp.map SmallSlot.value).prod:ZMod q) := by
  rw [leafProduct_leafBulk left (History.supported_left hs)]
  change (X:ZMod q)*(fixedProduct hp:ZMod q)*(bulkProduct left.root.small:ZMod q)=_
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).1,product_split hp]
  simp only [Nat.cast_mul,mul_assoc]

theorem right_product_variable
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (X : (ZMod q)ˣ) :
    ((X*rightConstant hs hr*Tree.Parameters.leafProduct (leafBulk right (right_regular hr)):
      (ZMod q)ˣ):ZMod q)=(X:ZMod q)*((hm.map SmallSlot.value).prod:ZMod q) := by
  rw [leafProduct_leafBulk right (History.supported_right hs)]
  change (X:ZMod q)*(fixedProduct hm:ZMod q)*(bulkProduct right.root.small:ZMod q)=_
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).2.1,product_split hm]
  simp only [Nat.cast_mul,mul_assoc]

theorem outgoing_left_variable
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (D P X : (ZMod q)ˣ) :
    (frequencyUnit left (left_regular hr):ZMod q)/
      ((D:ZMod q)*(P:ZMod q)*(splitConstant hs hr:ZMod q)*
        ((X*leftConstant hs hr*Tree.Parameters.leafProduct (leafBulk left (left_regular hr)):
          (ZMod q)ˣ):ZMod q))=
      primeArgument q D left.root P X := by
  rw [left_product_variable hs hr X]
  change (left.root.frequency:ZMod q)/
    ((D:ZMod q)*(P:ZMod q)*((u.map SmallSlot.value).prod:ZMod q)*
      ((X:ZMod q)*((hp.map SmallSlot.value).prod:ZMod q)))=_
  simp only [primeArgument,(History.supported_child_small_products hs).1,Nat.cast_mul,
    div_eq_mul_inv,mul_assoc,mul_left_comm]

theorem outgoing_right_variable
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (D P X : (ZMod q)ˣ) :
    (frequencyUnit right (right_regular hr):ZMod q)/
      ((D:ZMod q)*(P:ZMod q)*(splitConstant hs hr:ZMod q)*
        ((X*rightConstant hs hr*Tree.Parameters.leafProduct (leafBulk right (right_regular hr)):
          (ZMod q)ˣ):ZMod q))=
      primeArgument q D right.root P X := by
  rw [right_product_variable hs hr X]
  change (right.root.frequency:ZMod q)/
    ((D:ZMod q)*(P:ZMod q)*((u.map SmallSlot.value).prod:ZMod q)*
      ((X:ZMod q)*((hm.map SmallSlot.value).prod:ZMod q)))=_
  simp only [primeArgument,(History.supported_child_small_products hs).2,Nat.cast_mul,
    div_eq_mul_inv,mul_assoc,mul_left_comm]

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
