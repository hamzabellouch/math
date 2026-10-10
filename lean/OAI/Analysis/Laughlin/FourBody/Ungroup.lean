import OAI.Analysis.Laughlin.FourBody.Expansion

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def boundedAnnihilate (Q n : ℕ) : Module.End ℂ (Space Q) :=
  if h : n ≤ Q then annihilate ⟨n,by omega⟩ else 0

theorem boundedAnnihilate_rowOutput (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) :
    boundedAnnihilate Q (T.val.val-t) = annihilate (rowOutputMode Q t hQ T) := by
  have ht : T.val.val-t ≤ Q := by have h := T.val.isLt; omega
  rw [boundedAnnihilate,dite_eq_left ht]
  rfl

theorem linearMap_list_sum {I : Type*} (Q : ℕ) (L : Module.End ℂ (Space Q))
    (l : List I) (v : I → Space Q) :
    L (l.map v).sum = (l.map (fun i => L (v i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,map_add,ih]

noncomputable def sourceRowFourEntry (Q t : ℕ) (e f : ℕ × ℕ × ℤ) (x : Space Q) : ℂ :=
  -(sourceAlpha t e : ℂ)*(sourceAlpha t f : ℂ) * occupationInner Q
    (boundedAnnihilate Q (f.1+f.2.1-t) (sourceEntryThree Q e x))
    (boundedAnnihilate Q (e.1+e.2.1-t) (sourceEntryThree Q f x))

theorem sourceRowFourForm_entries (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) (x : Space Q) :
    sourceRowFourForm Q hQ row x =
      (row.2.2.map (fun e => (row.2.2.map (fun f => sourceRowFourEntry Q row.1 e f x)).sum)).sum := by
  classical
  let term := fun (T S : RowLevel row.1) (e f : ℕ × ℕ × ℤ) =>
    if e.1+e.2.1=T.val.val then if f.1+f.2.1=S.val.val then
      -(sourceAlpha row.1 e : ℂ)*(sourceAlpha row.1 f : ℂ) * occupationInner Q
        (boundedAnnihilate Q (S.val.val-row.1) (sourceEntryThree Q e x))
        (boundedAnnihilate Q (T.val.val-row.1) (sourceEntryThree Q f x)) else 0 else 0
  have ht (T S : RowLevel row.1) :
      -occupationInner Q
        (annihilate (rowOutputMode Q row.1 hQ S) (sourceRowLevel Q row.1 T.val.val row.2.2 x))
        (annihilate (rowOutputMode Q row.1 hQ T) (sourceRowLevel Q row.1 S.val.val row.2.2 x)) =
      (row.2.2.map (fun e => (row.2.2.map (fun f => term T S e f)).sum)).sum := by
    rw [← boundedAnnihilate_rowOutput,← boundedAnnihilate_rowOutput]
    simp only [sourceRowLevel_entries,linearMap_list_sum]
    rw [occupationInner_list_left]
    simp_rw [occupationInner_list_right]
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro f hf
    dsimp only [term]
    by_cases heT : e.1+e.2.1=T.val.val <;> by_cases hfS : f.1+f.2.1=S.val.val
    · simp only [ite_eq_left heT,ite_eq_left hfS,map_smul,occupationInner_smul_left,
        occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal]
      ring
    all_goals simp [heT,hfS,occupationInner]
  rw [sourceRowFourForm,← Finset.sum_neg_distrib]
  simp only [← Finset.sum_neg_distrib,ht]
  simp_rw [finset_list_sum_swap]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  obtain ⟨hft,hf15,hf8⟩ := (source_threeBody_rows_support row hr).2 f hf
  simp only [term,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [rowLevel_sum_select row.1 (e.1+e.2.1) het (by omega)]
  rw [rowLevel_sum_select row.1 (f.1+f.2.1) hft (by omega)]
  rfl

end Laughlin.Fock

end OAI
