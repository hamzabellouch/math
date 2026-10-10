import OAI.NumberTheory.Ostmann.Arithmetic.HistoryTreeLeaves

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryTreeParameters
open Construction HistoryBulkProducts HistoryResidueRegular

variable {q : ℕ} [Fact q.Prime]

def nodePivot {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : ZMod q :=
  ((frequencyUnit left (left_regular hr) : ZMod q) *
      (giantMinusUnit _ hr * rightConstant hs hr *
        Tree.Parameters.leafProduct (leafBulk right (right_regular hr)) : (ZMod q)ˣ) -
    (frequencyUnit right (right_regular hr) : ZMod q) *
      (giantPlusUnit _ hr * leftConstant hs hr *
        Tree.Parameters.leafProduct (leafBulk left (left_regular hr)) : (ZMod q)ˣ)) /
      ((frequencyUnit _ hr : ZMod q)*(splitConstant hs hr : ZMod q))

theorem nodePivot_eq {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : nodePivot hs hr = (p:ZMod q) := by
  have heq := History.supported_reversal hs
  unfold Arithmetic.reversalNumerator at heq
  have hc := congrArg (fun z : ℤ => (z:ZMod q)) heq
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] at hc
  unfold nodePivot
  rw [left_product_coe hs hr,right_product_coe hs hr]
  change ((left.root.frequency:ZMod q)*_-(right.root.frequency:ZMod q)*_) /
    ((a.frequency:ZMod q)*((u.map SmallSlot.value).prod:ZMod q)) = _
  apply (div_eq_iff (mul_ne_zero (frequency_ne_zero hr)
    (list_product_ne_zero u (compensation_values_ne_zero hs hr)))).mpr
  simpa only [History.root,mul_assoc,mul_comm,mul_left_comm] using hc

theorem nodePivot_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : nodePivot hs hr ≠ 0 := by
  rw [nodePivot_eq]
  have hp := value_ne_zero (left_regular hr)
    (show left.root.giantPlus ∈ left.root.values by simp [State.values])
  rwa [(History.supported_child_giants hs).1] at hp

def pivotUnit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : (ZMod q)ˣ :=
  Units.mk0 _ (nodePivot_ne_zero hs hr)

theorem pivotUnit_left {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    pivotUnit hs hr = giantPlusUnit left (left_regular hr) := by
  apply Units.ext
  change nodePivot hs hr = (left.root.giantPlus : ZMod q)
  rw [nodePivot_eq,(History.supported_child_giants hs).1]

theorem pivotUnit_right {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    pivotUnit hs hr = giantPlusUnit right (right_regular hr) := by
  apply Units.ext
  change nodePivot hs hr = (right.root.giantPlus : ZMod q)
  rw [nodePivot_eq,(History.supported_child_giants hs).2.1]

theorem left_stateProduct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    left.root.product = p * (u.map SmallSlot.value).prod *
      (a.giantPlus * (hp.map SmallSlot.value).prod) := by
  obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
  simp only [State.product,State.values,List.prod_cons,
    hlp,hlm,(History.supported_child_small_products hs).1]
  ring

theorem right_stateProduct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    right.root.product = p * (u.map SmallSlot.value).prod *
      (a.giantMinus * (hm.map SmallSlot.value).prod) := by
  obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
  simp only [State.product,State.values,List.prod_cons,
    hrp,hrm,(History.supported_child_small_products hs).2]
  ring

def argument (D : (ZMod q)ˣ) (a : State) : ZMod q :=
  (a.frequency : ZMod q) / ((D : ZMod q)*(a.product : ZMod q))

theorem parentPlus_eq_childMinus {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    giantPlusUnit _ hr = giantMinusUnit left (left_regular hr) := by
  apply Units.ext
  change (a.giantPlus:ZMod q) = (left.root.giantMinus:ZMod q)
  rw [(History.supported_child_giants hs).2.2.1]

theorem parentMinus_eq_childMinus {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    giantMinusUnit _ hr = giantMinusUnit right (right_regular hr) := by
  apply Units.ext
  change (a.giantMinus:ZMod q) = (right.root.giantMinus:ZMod q)
  rw [(History.supported_child_giants hs).2.2.2]

theorem outgoing_left {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (D : (ZMod q)ˣ) :
    (frequencyUnit left (left_regular hr) : ZMod q) /
      ((D:ZMod q)*(pivotUnit hs hr:ZMod q)*(splitConstant hs hr:ZMod q)*
        (giantPlusUnit _ hr * leftConstant hs hr *
          Tree.Parameters.leafProduct (leafBulk left (left_regular hr)) : (ZMod q)ˣ)) =
      argument D left.root := by
  rw [left_product_coe hs hr]
  change (left.root.frequency:ZMod q) /
    ((D:ZMod q)*nodePivot hs hr*((u.map SmallSlot.value).prod:ZMod q)*
      ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ZMod q)) = _
  rw [nodePivot_eq]
  simp only [argument,left_stateProduct hs,Nat.cast_mul,mul_assoc]

theorem outgoing_right {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (D : (ZMod q)ˣ) :
    (frequencyUnit right (right_regular hr) : ZMod q) /
      ((D:ZMod q)*(pivotUnit hs hr:ZMod q)*(splitConstant hs hr:ZMod q)*
        (giantMinusUnit _ hr * rightConstant hs hr *
          Tree.Parameters.leafProduct (leafBulk right (right_regular hr)) : (ZMod q)ˣ)) =
      argument D right.root := by
  rw [right_product_coe hs hr]
  change (right.root.frequency:ZMod q) /
    ((D:ZMod q)*nodePivot hs hr*((u.map SmallSlot.value).prod:ZMod q)*
      ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ZMod q)) = _
  rw [nodePivot_eq]
  simp only [argument,right_stateProduct hs,Nat.cast_mul,mul_assoc]

end Ostmann.Arithmetic.HistoryTreeParameters

end

end OAI
