import Mathlib.Data.List.OfFn
import OAI.NumberTheory.Ostmann.Conclusion.BulkPermutation

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Construction

def initialBulkSlots (m : ℕ) : List SourceSlot :=
  List.ofFn (fun i : Fin m => ⟨.bulk,i.val⟩)

@[simp] theorem initialBulkSlots_length (m : ℕ) : (initialBulkSlots m).length=m := by
  simp [initialBulkSlots]

@[simp] theorem initial_bulk_role_iff (m k : ℕ) (i : Fin (Template.initial m k).length) :
    (Template.initial m k)[i.val].role=.bulk ↔ i.val < m := by
  simpa [Template.initial] using InitialCoordinatesTemplate.initialRoles_bulk_iff m k
    ⟨i.val,by simpa [Template.initial] using i.isLt⟩

@[simp] theorem initial_bulk_origin (m k : ℕ) (i : Fin (Template.initial m k).length) :
    (Template.initial m k)[i.val].origin=i.val := by simp [Template.initial]

theorem initial_take_bulk (m k : ℕ) : (Template.initial m k).take m=initialBulkSlots m := by
  apply List.ext_getElem
  · simp [InitialCoordinatesTemplate.initial_length]
    omega
  · intro i hi hj
    have him : i < m := by simpa using hj
    have hiT : i<(Template.initial m k).length := by
      rw [InitialCoordinatesTemplate.initial_length]
      omega
    have hr := (initial_bulk_role_iff m k ⟨i,hiT⟩).mpr him
    simpa [initialBulkSlots,List.getElem_take,Template.initial] using hr

def bulkLeafTail (m k : ℕ) : ℕ → List SourceSlot
  | 0 => (Template.initial m k).drop m
  | l+1 => Template.remainder (l+1) (bulkLeafTail m k l)

def bulkLeafTemplate (m k l : ℕ) : List SourceSlot :=
  initialBulkSlots m ++ bulkLeafTail m k l

@[simp] theorem bulkLeafTemplate_zero (m k : ℕ) : bulkLeafTemplate m k 0=Template.initial m k := by
  rw [bulkLeafTemplate,bulkLeafTail,← initial_take_bulk,List.take_append_drop]

@[simp] theorem bulkLeafTemplate_succ (m k l : ℕ) :
    bulkLeafTemplate m k (l+1)=Template.remainder (l+1) (bulkLeafTemplate m k l) := by
  have hp : (initialBulkSlots m).filter
      (fun q => decide (q.role ≠ SlotRole.compensation (l+1)))=initialBulkSlots m := by
    apply List.filter_eq_self.mpr
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    simp
  simp only [bulkLeafTemplate,bulkLeafTail,Template.remainder,List.filter_append,hp]

theorem bulkLeafTail_not_bulk (m k l : ℕ) : ∀q∈bulkLeafTail m k l,q.role≠.bulk := by
  induction l with
  | zero =>
    intro q hq hr
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    have hiT : m+i<(Template.initial m k).length := by
      simp only [bulkLeafTail,List.length_drop] at hi
      omega
    have hri : (Template.initial m k)[m+i].role=.bulk := by
      simpa only [bulkLeafTail,List.getElem_drop] using hr
    have hh := (initial_bulk_role_iff m k ⟨m+i,hiT⟩).mp hri
    change m+i < m at hh
    omega
  | succ l ih =>
    intro q hq
    exact ih q (List.mem_filter.mp hq).1

@[simp] theorem bulkLeafTemplate_bulk_iff (m k l : ℕ)
    (i : Fin (bulkLeafTemplate m k l).length) :
    (bulkLeafTemplate m k l)[i.val].role=.bulk ↔ i.val < m := by
  by_cases hi : i.val < m
  · have hh : i.val<(initialBulkSlots m).length := by simpa using hi
    simp only [bulkLeafTemplate,List.getElem_append_left hh]
    simp [initialBulkSlots,hi]
  · have hh : (initialBulkSlots m).length ≤ i.val := by simpa using Nat.le_of_not_gt hi
    have hr := bulkLeafTail_not_bulk m k l _ (List.getElem_mem
      (show i.val-(initialBulkSlots m).length<(bulkLeafTail m k l).length by
        have := i.isLt
        simp only [bulkLeafTemplate,List.length_append,initialBulkSlots_length] at *
        omega))
    simp only [bulkLeafTemplate,List.getElem_append_right hh]
    exact iff_of_false hr hi

@[simp] theorem bulkLeafTemplate_bulk_origin (m k l : ℕ)
    (i : Fin (bulkLeafTemplate m k l).length) (hi : i.val < m) :
    (bulkLeafTemplate m k l)[i.val].origin=i.val := by
  simp only [bulkLeafTemplate]
  rw [List.getElem_append_left (by simpa using hi)]
  simp [initialBulkSlots]

theorem current_eq_bulkLeafBlocks (m k l : ℕ) :
    Template.current (Template.initial m k) l=
      (List.replicate (2^l) (bulkLeafTemplate m k l)).flatten := by
  induction l with
  | zero => simp [Template.current]
  | succ l ih =>
    simp only [Template.current,ih,Template.remainder,List.filter_flatten,List.map_replicate]
    have he := (bulkLeafTemplate_succ m k l).symm
    unfold Template.remainder at he
    rw [he]
    rw [← List.flatten_append,← List.replicate_add]
    congr 2
    simp [pow_succ]
    omega

@[simp] theorem current_bulk_block_length (m k l : ℕ) :
    (Template.current (Template.initial m k) l).length=
      2^l*(bulkLeafTemplate m k l).length := by
  rw [current_eq_bulkLeafBlocks]
  simp [List.length_flatten,List.map_replicate]

end Ostmann.Conclusion

end

end OAI
