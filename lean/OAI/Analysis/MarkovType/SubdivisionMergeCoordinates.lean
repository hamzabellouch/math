import OAI.Analysis.MarkovType.SubdivisionProfileExpansion
import OAI.Analysis.MarkovType.C00FiniteCoordinates
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

private theorem singleton_vector (a : ℝ) : ofList [a] = Finsupp.single 0 a := by
  simpa using ofList_replicate 1 a

private theorem pair_vector (a b : ℝ) :
    ofList [a, b] = Finsupp.single 0 a + Finsupp.single 1 b := by
  change ofList ([a] ++ [b]) = _
  rw [ofList_append, singleton_vector, singleton_vector]
  simp only [List.length_singleton, Finsupp.mapDomain_single, Nat.add_zero]

private theorem pair_context_vector (left right : List ℝ) (a b : ℝ) :
    ofList (left ++ ([a, b] ++ right)) =
      ofList left + Finsupp.single left.length a + Finsupp.single (left.length + 1) b +
        Finsupp.mapDomain (fun k => left.length + 2 + k) (ofList right) := by
  rw [ofList_append, ofList_append, pair_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    ← Finsupp.mapDomain_comp, Function.comp_def, List.length_cons, List.length_nil,
    Nat.add_zero, Nat.add_assoc]
  have hshift (k : ℕ) : 0 + (1 + (1 + k)) = 2 + k := by omega
  simp only [hshift, add_assoc]

private theorem single_context_vector (left right : List ℝ) (a : ℝ) :
    ofList (left ++ ([a] ++ right)) =
      ofList left + Finsupp.single left.length a +
        Finsupp.mapDomain (fun k => left.length + 1 + k) (ofList right) := by
  rw [ofList_append, ofList_append, singleton_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    ← Finsupp.mapDomain_comp, Function.comp_def, List.length_singleton,
    Nat.add_zero, Nat.add_assoc]
  abel

private theorem merge_left_context (left : List ℝ) :
    Finsupp.mapDomain (C00.mergeIndex left.length) (ofList left) = ofList left := by
  classical
  induction left using List.ofFnRec with
  | h m left =>
      simp only [List.length_ofFn, ofList_ofFn, C00.ofArray, C00.place,
        Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
      apply Finset.sum_congr rfl
      intro i _
      simp only [C00.mergeIndex, ite_eq_left (Nat.le_of_lt i.isLt)]

theorem mergeAt_context (left right : List ℝ) (a b : ℝ) :
    C00.mergeAt left.length (ofList (left ++ ([a, b] ++ right))) =
      ofList (left ++ ([a + b] ++ right)) := by
  classical
  rw [C00.mergeAt, pair_context_vector]
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rw [merge_left_context]
  have h0 : C00.mergeIndex left.length left.length = left.length := by
    simp only [C00.mergeIndex, le_refl, ite_true]
  have h1 : C00.mergeIndex left.length (left.length + 1) = left.length := by
    simp only [C00.mergeIndex]
    rw [ite_eq_right (by omega)]
    omega
  have hr :
      Finsupp.mapDomain (C00.mergeIndex left.length)
        (Finsupp.mapDomain (fun k => left.length + 2 + k) (ofList right)) =
      Finsupp.mapDomain (fun k => left.length + 1 + k) (ofList right) := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext k
    simp only [Function.comp_def, C00.mergeIndex]
    rw [ite_eq_right (by omega)]
    omega
  rw [h0, h1, hr, single_context_vector, Finsupp.single_add]
  abel

theorem exists_context (x : C00) (i : ℕ) :
    ∃ left right : List ℝ, ∃ a b : ℝ,
      left.length = i ∧ ofList (left ++ ([a, b] ++ right)) = x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  let B : ℕ := max m (i + 2)
  let L : List ℝ := List.ofFn fun j : Fin B => x j.val
  have hL : ofList L = x := by
    rw [ofList_ofFn]
    apply C00.ofArray_of_vanishes
    intro k hk
    rw [← ha]
    exact C00.ofArray_apply_of_ge a k ((le_max_left _ _).trans hk)
  have hi : i < L.length := by
    simp only [L, List.length_ofFn]
    have h := le_max_right m (i + 2)
    omega
  have hi1 : i + 1 < L.length := by
    simp only [L, List.length_ofFn]
    have h := le_max_right m (i + 2)
    omega
  have hdrop : L.drop i = L[i] :: L[i + 1] :: L.drop (i + 2) := by
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi1]
  have hdec : L.take i ++ ([L[i], L[i + 1]] ++ L.drop (i + 2)) = L := by
    change L.take i ++ (L[i] :: L[i + 1] :: L.drop (i + 2)) = L
    rw [← hdrop]
    exact List.take_append_drop i L
  refine ⟨L.take i, L.drop (i + 2), L[i], L[i + 1], ?_, ?_⟩
  · simp only [List.length_take, min_eq_left hi.le]
  · rw [hdec]
    exact hL

end MarkovSuperreflexivity.Subdivision

end

end OAI
