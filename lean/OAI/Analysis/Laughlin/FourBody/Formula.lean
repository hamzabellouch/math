import OAI.Analysis.Laughlin.FourBody.Ungroup

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators

noncomputable def boundedCreate (Q n : ℕ) : Module.End ℂ (Space Q) :=
  if h : n ≤ Q then create ⟨n,by omega⟩ else 0

theorem boundedCreate_rowOutput (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) :
    boundedCreate Q (T.val.val-t) = create (rowOutputMode Q t hQ T) := by
  have ht : T.val.val-t ≤ Q := by have h := T.val.isLt; omega
  rw [boundedCreate,dite_eq_left ht]
  rfl

theorem sourceRowSquareVector_eq_F (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) (x : Space Q) :
    sourceRowSquareVector Q hQ row x = ((row.2.1 : ℂ)/10^7) • sourcePairEnd Q row.1 x +
      (row.2.2.map (fun e => (sourceAlpha row.1 e : ℂ) •
        boundedCreate Q (e.1+e.2.1-row.1)
          (boundedAnnihilate Q e.2.1 (sourcePairEnd Q e.1 x)))).sum := by
  rw [sourceRowSquareVector]
  congr 1
  simp only [sourceRowLevel_entries,linearMap_list_sum]
  have ht (T : RowLevel row.1) (e : ℕ × ℕ × ℤ) :
      create (rowOutputMode Q row.1 hQ T)
        (if e.1+e.2.1=T.val.val then (sourceAlpha row.1 e : ℂ) • sourceEntryThree Q e x else 0) =
      if e.1+e.2.1=T.val.val then (sourceAlpha row.1 e : ℂ) •
        boundedCreate Q (T.val.val-row.1) (sourceEntryThree Q e x) else 0 := by
    rw [boundedCreate_rowOutput Q row.1 hQ T]
    by_cases he : e.1+e.2.1=T.val.val <;> simp only [he,ite_true,ite_false,map_smul,map_zero]
  simp_rw [ht,finset_list_sum_swap]
  congr 1
  apply List.map_congr_left
  intro e he
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  rw [rowLevel_sum_select row.1 (e.1+e.2.1) het (by omega)]
  rw [sourceEntryThree_eq Q e (by omega) (by omega),boundedAnnihilate,
    dite_eq_left (show e.2.1 ≤ Q by omega)]

end Laughlin.Fock

end OAI
