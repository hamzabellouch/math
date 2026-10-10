import OAI.Analysis.MarkovType.SubdivisionProfileDefs
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.Subdivision

theorem ofList_append (left right : List ℝ) :
    ofList (left ++ right) = ofList left +
      Finsupp.mapDomain (fun i => left.length + i) (ofList right) := by
  classical
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          rw [← List.ofFn_fin_append]
          simp only [ofList_ofFn, List.length_ofFn, C00.ofArray, C00.place,
            Fin.sum_univ_add, Fin.append_left, Fin.append_right,
            Fin.val_castAdd, Fin.val_natAdd,
            Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

theorem ofList_replicate (J : ℕ) (c : ℝ) :
    ofList (List.replicate J c) = ∑ j : Fin J, Finsupp.single j.val c := by
  rw [← List.ofFn_const, ofList_ofFn]
  rfl

theorem pieces_ofFn_eq {m : ℕ} (a : Fin m → ℝ) (J : ℕ → ℕ) :
    ofList (pieces (List.ofFn fun i => (a i, J i.val))) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single ((∑ k ∈ Finset.range i.val, J k) + t.val)
          (a i / (J i.val : ℝ)) := by
  classical
  induction m generalizing J with
  | zero =>
      simp only [List.ofFn_zero, pieces_nil, Fin.sum_univ_zero]
      exact ofList_ofFn (fun i : Fin 0 => Fin.elim0 i)
  | succ m ih =>
      rw [List.ofFn_succ, pieces_cons, ofList_append, ofList_replicate,
        List.length_replicate]
      simp only [Fin.val_succ]
      rw [ih (fun i => a i.succ) (fun k => J (k + 1))]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Finset.range_zero, Finset.sum_empty,
        zero_add, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [Finset.sum_range_succ']
      omega

theorem finiteSubdivision_eq {m : ℕ} (a : Fin m → ℝ) (J : ℕ → ℕ) :
    finiteSubdivision a (fun i => J i.val) =
      ∑ i : Fin m, ∑ t : Fin (J i.val),
        Finsupp.single ((∑ k ∈ Finset.range i.val, J k) + t.val)
          (a i / (J i.val : ℝ)) :=
  pieces_ofFn_eq a J

end MarkovSuperreflexivity.Subdivision

end

end OAI
