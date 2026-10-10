import OAI.NumberTheory.Ostmann.Arithmetic.HistoryTreeParameters
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistory

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramParameters
open Construction HistoryBulkProducts

def eraseBulkValue (a : SmallSlot) : SmallSlot :=
  if a.role=.bulk then ⟨a.role,0,a.origin⟩ else a

@[simp] theorem eraseBulkValue_role (a : SmallSlot) :
    (eraseBulkValue a).role=a.role := by
  simp only [eraseBulkValue]; split_ifs <;> rfl

@[simp] theorem eraseBulkValue_origin (a : SmallSlot) :
    (eraseBulkValue a).origin=a.origin := by
  simp only [eraseBulkValue]; split_ifs <;> rfl

@[simp] theorem eraseBulkValue_zero (r : SlotRole) (o : ℕ) :
    eraseBulkValue ⟨r,0,o⟩=⟨r,0,o⟩ := by
  simp only [eraseBulkValue]; split_ifs <;> rfl

theorem fixedProduct_erase (xs : List SmallSlot) :
    fixedProduct (xs.map eraseBulkValue)=fixedProduct xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a.role=.bulk
    · simpa [fixedProduct,eraseBulkValue,ha] using ih
    · simpa [fixedProduct,eraseBulkValue,ha] using congrArg (fun n => a.value*n) ih

theorem fixedProduct_eq_of_erase_eq {xs ys : List SmallSlot}
    (h : xs.map eraseBulkValue=ys.map eraseBulkValue) : fixedProduct xs=fixedProduct ys := by
  rw [←fixedProduct_erase xs,←fixedProduct_erase ys,h]

theorem erase_reinsert (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot) :
    (Template.reinsert j T u h).map eraseBulkValue=
      Template.reinsert j T (u.map eraseBulkValue) (h.map eraseBulkValue) := by
  induction T generalizing u h with
  | nil => rfl
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · cases u <;> simp [Template.reinsert,hq,ih]
    · cases h <;> simp [Template.reinsert,hq,ih]

theorem erase_reinsert_eq (j : ℕ) (T : List SourceSlot) (u : List SmallSlot)
    {h h' : List SmallSlot} (hh : h.map eraseBulkValue=h'.map eraseBulkValue) :
    (Template.reinsert j T u h).map eraseBulkValue=
      (Template.reinsert j T u h').map eraseBulkValue := by
  rw [erase_reinsert,erase_reinsert,hh]

theorem erase_take_eq {xs ys : List SmallSlot}
    (h : xs.map eraseBulkValue=ys.map eraseBulkValue) (n : ℕ) :
    (xs.take n).map eraseBulkValue=(ys.take n).map eraseBulkValue := by
  simpa only [List.map_take] using congrArg (List.take n) h

theorem erase_drop_eq {xs ys : List SmallSlot}
    (h : xs.map eraseBulkValue=ys.map eraseBulkValue) (n : ℕ) :
    (xs.drop n).map eraseBulkValue=(ys.drop n).map eraseBulkValue := by
  simpa only [List.map_drop] using congrArg (List.drop n) h

theorem assignedSlots_erase_eq (sources : SourceFamily) (T : List SourceSlot)
    (x y : SourceAssignment sources T)
    (h : ∀i : Fin T.length, T[i].role≠.bulk → (x i:ℕ)=(y i:ℕ)) :
    (assignedSlots sources T x).map eraseBulkValue=
      (assignedSlots sources T y).map eraseBulkValue := by
  simp only [assignedSlots,Template.sample,List.map_ofFn]
  congr 1
  funext i
  by_cases hi : T[i].role=.bulk
  · change T[i.val].role=.bulk at hi
    simp [eraseBulkValue,hi]
  · have hv := h i hi
    change T[i.val].role≠.bulk at hi
    simp [eraseBulkValue,hi,hv]

end Ostmann.Arithmetic.HistoryBulkDiagramParameters

end

end OAI
