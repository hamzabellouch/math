import OAI.NumberTheory.Ostmann.Arithmetic.HistoryTreeLeaves
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionPermutation
import OAI.NumberTheory.Ostmann.Construction.CanonicalSourceLabels
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingCounterpart

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion HistoryBulkProducts HistoryLinearization

def bulkValues (xs : List SmallSlot) : List ℕ :=
  (xs.filter (fun q => decide (q.role=.bulk))).map SmallSlot.value

@[simp] theorem bulkValues_append (xs ys : List SmallSlot) :
    bulkValues (xs++ys)=bulkValues xs++bulkValues ys := by
  simp [bulkValues]

theorem bulkValues_length_of_matches {T : List SourceSlot} {xs : List SmallSlot}
    (h : Template.Matches T xs) :
    (bulkValues xs).length=Template.countRole T .bulk := by
  have he := congrArg (fun zs : List (SlotRole × ℕ) =>
    (zs.filter (fun q => decide (q.1=.bulk))).length) h
  simpa [bulkValues,Template.countRole,List.filter_map,Function.comp_def] using he

theorem bulkValues_reinsert (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : Template.Matches (Template.extracted j T) u)
    (hh : Template.Matches (Template.remainder j T) h) :
    bulkValues (Template.reinsert j T u h)=bulkValues h := by
  have he := (reinsert_role_filters j T u h hu hh).2
  have hp : (fun q : SmallSlot => decide (q.role=.bulk) &&
      decide (q.role≠.compensation j))=(fun q => decide (q.role=.bulk)) := by
    funext q
    by_cases hq : q.role=.bulk <;> simp [hq]
  unfold bulkValues
  conv_rhs => rw [←he,List.filter_filter,hp]

theorem bulkValues_halves (xs : List SmallSlot) (n N : ℕ)
    (hn : (bulkValues (xs.take n)).length=N) :
    bulkValues (xs.take n)=(bulkValues xs).take N ∧
      bulkValues (xs.drop n)=(bulkValues xs).drop N := by
  have he : bulkValues xs=bulkValues (xs.take n)++bulkValues (xs.drop n) := by
    rw [←bulkValues_append,List.take_append_drop]
  constructor <;> rw [he,←hn] <;> simp

theorem bulkLeafTemplate_filter_bulk (m k l : ℕ) :
    (bulkLeafTemplate m k l).filter (fun q => decide (q.role=.bulk))=initialBulkSlots m := by
  have ht : (bulkLeafTail m k l).filter (fun q => decide (q.role=.bulk))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    simp [bulkLeafTail_not_bulk m k l q hq]
  have hi : (initialBulkSlots m).filter (fun q => decide (q.role=.bulk))=initialBulkSlots m := by
    apply List.filter_eq_self.mpr
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    rfl
  simp only [bulkLeafTemplate,List.filter_append,ht,hi,List.append_nil]

theorem current_count_bulk (m k l : ℕ) :
    Template.countRole (Template.current (Template.initial m k) l) .bulk=2^l*m := by
  simp [Template.countRole,current_eq_bulkLeafBlocks,List.filter_flatten,
    bulkLeafTemplate_filter_bulk,List.length_flatten]

theorem remainder_count_bulk (m k l : ℕ) :
    Template.countRole (Template.remainder (l+1)
      (Template.current (Template.initial m k) l)) .bulk=2^l*m := by
  rw [Template.countRole_remainder _ _ _ (by simp),current_count_bulk]

def orderedLeafIndex : (l : ℕ) → Tree.Leaves l ≃ Fin (2^l)
  | 0 => by
      change (Fin 0 → Bool) ≃ Fin 1
      exact Equiv.ofUnique _ _
  | l+1 => (Fin.consEquiv (fun _ : Fin (l+1) => Bool)).symm |>.trans
      ((Equiv.boolProdEquivSum (Tree.Leaves l)).trans
        ((Equiv.sumCongr (orderedLeafIndex l) (orderedLeafIndex l)).trans
          (finSumFinEquiv.trans (finCongr (by omega)))))

@[simp] theorem orderedLeafIndex_zero (p : Tree.Leaves 0) :
    (orderedLeafIndex 0 p).val=0 := by omega

@[simp] theorem orderedLeafIndex_left (l : ℕ) (p : Tree.Leaves l) :
    (orderedLeafIndex (l+1) (Fin.cons false p)).val=(orderedLeafIndex l p).val := by
  simp [orderedLeafIndex,Equiv.boolProdEquivSum,finSumFinEquiv]

@[simp] theorem orderedLeafIndex_right (l : ℕ) (p : Tree.Leaves l) :
    (orderedLeafIndex (l+1) (Fin.cons true p)).val=2^l+(orderedLeafIndex l p).val := by
  simp [orderedLeafIndex,Equiv.boolProdEquivSum,finSumFinEquiv,Nat.add_comm]

def bulkBlock (m : ℕ) : (l : ℕ) → Tree.Leaves l → List ℕ → List ℕ
  | 0, _, xs => xs
  | l+1, p, xs => if p 0 then bulkBlock m l (Fin.tail p) (xs.drop (2^l*m))
      else bulkBlock m l (Fin.tail p) (xs.take (2^l*m))

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
