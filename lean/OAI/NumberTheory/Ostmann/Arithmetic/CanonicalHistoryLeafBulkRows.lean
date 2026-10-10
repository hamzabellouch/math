import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion

def rows {n m : ℕ} (f : Fin n → Fin m → ℕ) : List ℕ :=
  (List.ofFn (fun b => List.ofFn (f b))).flatten

@[simp] theorem rows_length {n m : ℕ} (f : Fin n → Fin m → ℕ) :
    (rows f).length=n*m := by
  simp [rows,List.length_flatten,List.map_ofFn,Function.comp_def]

theorem rows_split {n m : ℕ} (f : Fin (n+n) → Fin m → ℕ) :
    rows f=rows (fun b : Fin n => f (b.castLE (Nat.le_add_right n n))) ++
      rows (fun b : Fin n => f (b.natAdd n)) := by
  unfold rows
  rw [List.ofFn_add,List.flatten_append]

theorem bulkBlock_rows (m l : ℕ) (path : Tree.Leaves l)
    (f : Fin (2^l) → Fin m → ℕ) :
    bulkBlock m l path (rows f)=List.ofFn (f (orderedLeafIndex l path)) := by
  induction l with
  | zero =>
    have hz : orderedLeafIndex 0 path=(0:Fin 1) := by ext; simp
    simp [bulkBlock,rows,hz]
  | succ l ih =>
    have hn : 2^(l+1)=2^l+2^l := by omega
    let f' : Fin (2^l+2^l) → Fin m → ℕ := fun b => f (Fin.cast hn.symm b)
    have he : rows f=rows f' := by
      unfold rows
      rw [List.ofFn_congr hn]
    rw [he,rows_split]
    have hl := rows_length (fun b : Fin (2^l) => f' (b.castLE (Nat.le_add_right _ _)))
    simp only [bulkBlock]
    split_ifs with hp
    · rw [←hl,List.drop_left,ih]
      congr 1
      apply congrArg f
      apply Fin.ext
      have hepath : path=Fin.cons true (Fin.tail path) := by
        simpa only [hp] using (Fin.cons_self_tail path).symm
      rw [hepath,orderedLeafIndex_right]
      rfl
    · rw [←hl,List.take_left,ih]
      congr 1
      apply congrArg f
      apply Fin.ext
      have hp' : path 0=false := Bool.eq_false_iff.mpr hp
      have hepath : path=Fin.cons false (Fin.tail path) := by
        simpa only [hp'] using (Fin.cons_self_tail path).symm
      rw [hepath,orderedLeafIndex_left]
      rfl

theorem bulkValues_ofFn_prefix {d m : ℕ} (hm : m≤d) (f : Fin d→SmallSlot)
    (hf : ∀ i : Fin d, (f i).role = SlotRole.bulk ↔ i.val < m) :
    bulkValues (List.ofFn f)=List.ofFn (fun i : Fin m => (f (i.castLE hm)).value) := by
  have hd : d=m+(d-m) := by omega
  have he := List.ofFn_congr hd f
  rw [he,List.ofFn_add,bulkValues_append]
  have hl : (List.ofFn (fun i : Fin m =>
      f (Fin.cast hd.symm (i.castLE (Nat.le_add_right m (d-m)))))).filter
      (fun q => decide (q.role=.bulk)) =
        List.ofFn (fun i : Fin m => f (Fin.cast hd.symm
          (i.castLE (Nat.le_add_right m (d-m))))) := by
    apply List.filter_eq_self.mpr
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact decide_eq_true ((hf _).mpr i.isLt)
  have hr : (List.ofFn (fun i : Fin (d-m) =>
      f (Fin.cast hd.symm (i.natAdd m)))).filter
      (fun q => decide (q.role=.bulk))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    simp [hf]
  simp only [bulkValues,hl,hr,List.map_nil,List.append_nil,List.map_ofFn]
  rfl

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
