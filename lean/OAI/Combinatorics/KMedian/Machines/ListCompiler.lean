import Mathlib

namespace OAI

section Inline_PCPListCompiler
namespace MetricKMedian.PCP.Compiler
open scoped Classical

lemma length_flatMap_uniform {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x∈xs, (f x).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    simp only [Nat.add_mul,Nat.one_mul]; omega
lemma getElem?_flatMap_uniform {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x∈xs, (f x).length=n) (i : ℕ) (hi : i<xs.length) (j : ℕ) (hj : j<n) :
    (xs.flatMap f)[i*n+j]?=(f xs[i])[j]? := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      have hn := h a (by simp)
      simp only [List.flatMap_cons,Nat.zero_mul,Nat.zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      have hn := h a (by simp)
      have hi' : i<xs.length := by simpa using hi
      have hnle : (f a).length ≤ (i+1)*n+j := by rw [hn,Nat.add_mul,Nat.one_mul]; omega
      rw [List.flatMap_cons,List.getElem?_append_right hnle,hn]
      have he : (i+1)*n+j-n=i*n+j := by simp only [Nat.add_mul,Nat.one_mul]; omega
      rw [he]
      exact ih xs (fun x hx => h x (by simp [hx])) hi'
end MetricKMedian.PCP.Compiler

end Inline_PCPListCompiler

end OAI
