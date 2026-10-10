import Mathlib

namespace OAI


                                 
section
namespace MetricKMedian.ListSigma
open Finset

 theorem take_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k ≤ n) :
    (List.ofFn f).take k=List.ofFn (fun i : Fin k => f (Fin.castLE hk i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hk]
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

 theorem flatten_entry {α : Type} (xs : List (List α)) (i : ℕ) (hi : i<xs.length)
    (j : ℕ) (hj : j<xs[i].length) :
    xs.flatten[((xs.take i).map List.length).sum+j]?=some (xs[i][j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.take_zero,List.map_nil,List.sum_nil,zero_add,List.flatten_cons,List.getElem_cons_zero] at *
      have hj' : j<a.length := hj
      rw [List.getElem?_append_left hj',List.getElem?_eq_getElem hj']
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons,List.getElem_cons_succ] at *
      rw [Nat.add_assoc,List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact ih i hi' hj

 theorem ofFn_sigma {α : Type} {m : ℕ} {n : Fin m → ℕ} (f : (i : Fin m) → Fin (n i) → α) :
    (List.ofFn (fun i => List.ofFn (f i))).flatten=
      List.ofFn (fun j => let z := (finSigmaFinEquiv (n:=n)).symm j; f z.1 z.2) := by
  have hlen : (List.ofFn (fun i => List.ofFn (f i))).flatten.length=∑i,n i := by
    simp only [List.length_flatten,List.map_ofFn,List.length_ofFn,Function.comp_def,List.sum_ofFn]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen
  · intro k hk hk'
    let j : Fin (∑i,n i) := ⟨k,by simpa only [List.length_ofFn] using hk'⟩
    let z := (finSigmaFinEquiv (n:=n)).symm j
    have hindex : (∑i : Fin z.1.val,n (Fin.castLE z.1.isLt.le i))+z.2.val=k := by
      rw [← finSigmaFinEquiv_apply z]
      exact congrArg Fin.val (Equiv.apply_symm_apply _ j)
    have he := flatten_entry (List.ofFn (fun i => List.ofFn (f i))) z.1.val
      (by simpa only [List.length_ofFn] using z.1.isLt) z.2.val
      (by simpa only [List.getElem_ofFn,List.length_ofFn] using z.2.isLt)
    rw [take_ofFn _ _ z.1.isLt.le] at he
    simp only [List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn,List.getElem_ofFn] at he
    rw [hindex,List.getElem?_eq_getElem hk] at he
    simpa only [List.getElem_ofFn] using Option.some.inj he

end MetricKMedian.ListSigma
end

end OAI
