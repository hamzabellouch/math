import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryResidueRegular

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryResidueRegular
open Construction HistoryBulkProducts

variable {K : Type*} [Field K]

theorem list_product_ne_zero (xs : List SmallSlot)
    (hx : ∀x∈xs,(x.value:K)≠0) : ((xs.map SmallSlot.value).prod:K)≠0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons,List.prod_cons,Nat.cast_mul]
      exact mul_ne_zero (hx x (by simp)) (ih (fun y hy => hx y (by simp [hy])))

theorem bulkProduct_ne_zero (xs : List SmallSlot)
    (hx : ∀x∈xs,(x.value:K)≠0) : (bulkProduct xs:K)≠0 := by
  apply list_product_ne_zero
  intro x hx'
  exact hx x (List.mem_of_mem_filter hx')

theorem fixedProduct_ne_zero (xs : List SmallSlot)
    (hx : ∀x∈xs,(x.value:K)≠0) : (fixedProduct xs:K)≠0 := by
  apply list_product_ne_zero
  intro x hx'
  exact hx x (List.mem_of_mem_filter hx')

variable {q : ℕ} [Fact q.Prime]

theorem small_value_ne_zero {l : ℕ} {h : History l} (hr : Regular q h) {x : SmallSlot}
    (hx : x ∈ h.root.small) : (x.value:ZMod q) ≠ 0 := by
  apply value_ne_zero hr
  simp only [State.values,List.mem_cons,List.mem_map]
  exact Or.inr (Or.inr ⟨x,hx,rfl⟩)

def frequencyUnit {l : ℕ} (h : History l) (hr : Regular q h) : (ZMod q)ˣ :=
  Units.mk0 _ (frequency_ne_zero hr)

def giantPlusUnit {l : ℕ} (h : History l) (hr : Regular q h) : (ZMod q)ˣ :=
  Units.mk0 (h.root.giantPlus : ZMod q) (value_ne_zero hr (by simp [State.values]))

def giantMinusUnit {l : ℕ} (h : History l) (hr : Regular q h) : (ZMod q)ˣ :=
  Units.mk0 (h.root.giantMinus : ZMod q) (value_ne_zero hr (by simp [State.values]))

def bulkUnit {l : ℕ} (h : History l) (hr : Regular q h) : (ZMod q)ˣ :=
  Units.mk0 _ (bulkProduct_ne_zero h.root.small (fun _ hx => small_value_ne_zero hr hx))

def fixedUnit {l : ℕ} (h : History l) (hr : Regular q h) : (ZMod q)ˣ :=
  Units.mk0 _ (fixedProduct_ne_zero h.root.small (fun _ hx => small_value_ne_zero hr hx))

theorem inherited_values_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    (∀x∈hp,(x.value:ZMod q)≠0) ∧ (∀x∈hm,(x.value:ZMod q)≠0) := by
  have hperm := History.supported_small_split hs
  constructor
  · intro x hx
    apply small_value_ne_zero hr
    exact hperm.mem_iff.mpr (List.mem_append_left hm hx)
  · intro x hx
    apply small_value_ne_zero hr
    exact hperm.mem_iff.mpr (List.mem_append_right hp hx)

theorem compensation_values_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    ∀x∈u,(x.value:ZMod q)≠0 := by
  intro x hx
  apply small_value_ne_zero (left_regular hr)
  exact (History.supported_child_small hs).1.mem_iff.mpr (List.mem_append_left hp hx)

def leftConstant {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : (ZMod q)ˣ :=
  Units.mk0 _ (fixedProduct_ne_zero hp (inherited_values_ne_zero hs hr).1)

def rightConstant {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : (ZMod q)ˣ :=
  Units.mk0 _ (fixedProduct_ne_zero hm (inherited_values_ne_zero hs hr).2)

def splitConstant {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) : (ZMod q)ˣ :=
  Units.mk0 _ (list_product_ne_zero u (compensation_values_ne_zero hs hr))

end Ostmann.Arithmetic.HistoryResidueRegular

end

end OAI
