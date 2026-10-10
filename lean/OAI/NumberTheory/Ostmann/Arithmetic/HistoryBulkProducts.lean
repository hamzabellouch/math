import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkProducts
open Construction

def bulkProduct (xs : List SmallSlot) : ℕ :=
  ((xs.filter (fun q => q.role = .bulk)).map SmallSlot.value).prod

def fixedProduct (xs : List SmallSlot) : ℕ :=
  ((xs.filter (fun q => q.role ≠ .bulk)).map SmallSlot.value).prod

theorem product_split (xs : List SmallSlot) :
    (xs.map SmallSlot.value).prod = fixedProduct xs * bulkProduct xs := by
  induction xs with
  | nil => simp [fixedProduct,bulkProduct]
  | cons q xs ih =>
      by_cases hq : q.role = .bulk <;>
        simp [fixedProduct,bulkProduct,hq] at * <;> rw [ih] <;> ring

@[simp] theorem bulkProduct_append (xs ys : List SmallSlot) :
    bulkProduct (xs++ys) = bulkProduct xs * bulkProduct ys := by
  simp [bulkProduct,List.filter_append,List.map_append]
@[simp] theorem fixedProduct_append (xs ys : List SmallSlot) :
    fixedProduct (xs++ys) = fixedProduct xs * fixedProduct ys := by
  simp [fixedProduct,List.filter_append,List.map_append]

theorem bulkProduct_perm {xs ys : List SmallSlot} (h : xs.Perm ys) :
    bulkProduct xs = bulkProduct ys := by
  unfold bulkProduct
  exact ((h.filter (fun q : SmallSlot => decide (q.role = SlotRole.bulk))).map SmallSlot.value).prod_eq

theorem fixedProduct_perm {xs ys : List SmallSlot} (h : xs.Perm ys) :
    fixedProduct xs = fixedProduct ys := by
  unfold fixedProduct
  exact ((h.filter (fun q : SmallSlot => decide (q.role ≠ SlotRole.bulk))).map SmallSlot.value).prod_eq

theorem compensation_bulkProduct (l : ℕ) (u : List SmallSlot)
    (hu : ∀q∈u,q.role=.compensation l) : bulkProduct u = 1 := by
  have hf : u.filter (fun q => q.role = .bulk) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    simp [hu q hq]
  simp [bulkProduct,hf]

theorem compensation_fixedProduct (l : ℕ) (u : List SmallSlot)
    (hu : ∀q∈u,q.role=.compensation l) : fixedProduct u = (u.map SmallSlot.value).prod := by
  rw [product_split,compensation_bulkProduct l u hu,mul_one]

theorem supported_product_split {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    bulkProduct a.small = bulkProduct hp * bulkProduct hm ∧
      fixedProduct a.small = fixedProduct hp * fixedProduct hm := by
  have h := History.supported_small_split hs
  exact ⟨(bulkProduct_perm h).trans (bulkProduct_append hp hm),
    (fixedProduct_perm h).trans (fixedProduct_append hp hm)⟩

theorem supported_child_products {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hu : ∀q∈u,q.role=.compensation (l+1)) :
    bulkProduct left.root.small = bulkProduct hp ∧
    bulkProduct right.root.small = bulkProduct hm ∧
    fixedProduct left.root.small = (u.map SmallSlot.value).prod * fixedProduct hp ∧
    fixedProduct right.root.small = (u.map SmallSlot.value).prod * fixedProduct hm := by
  obtain ⟨hl,hr⟩ := History.supported_child_small hs
  have hb := compensation_bulkProduct (l+1) u hu
  have hf := compensation_fixedProduct (l+1) u hu
  constructor
  · rw [bulkProduct_perm hl,bulkProduct_append,hb,one_mul]
  constructor
  · rw [bulkProduct_perm hr,bulkProduct_append,hb,one_mul]
  constructor
  · rw [fixedProduct_perm hl,fixedProduct_append,hf]
  · rw [fixedProduct_perm hr,fixedProduct_append,hf]

end Ostmann.Arithmetic.HistoryBulkProducts

end

end OAI
