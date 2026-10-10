import OAI.Computability.MatchingCount.FoldRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma element_code_le {α : Type} [Coding α] (l : List α) (a : α) (ha : a∈l) :
    (encode a).length≤(encode l).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    simp only [code_cons,pairBits_length]
    rcases ha with rfl | ha
    · omega
    · have hh := ih ha; omega

lemma list_code_bound {α : Type} [Coding α] (l : List α) (M : ℕ)
    (hb : ∀ a∈l,(encode a).length≤M) : (encode l).length≤l.length*(2*M+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hb a (by simp)
    have hl := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    simp only [code_cons,pairBits_length,List.length_cons]
    nlinarith

lemma code_reverse_length {α : Type} [Coding α] (l : List α) :
    (encode l.reverse).length=(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons,code_append,pairBits_length,ih]; omega

lemma append_map_fold {α β : Type} (f : α → β) (l : List α) (b : List β) :
    l.foldl (fun b a => b++[f a]) b=b++l.map f := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma append_fold {α : Type} (l : List (List α)) (b : List α) :
    l.foldl (fun b a => b++a) b=b++l.flatten := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma code_flatten_le {α : Type} [Coding α] (l : List (List α)) :
    (encode l.flatten).length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatten_cons,code_append,List.length_append,code_cons,pairBits_length]; omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listMap [Inhabited α] (f : α → β) (hf : Poly f) : Poly (List.map f) := by
  let p := hf.routine.time
  have hs : Poly (fun z : List β×α => z.1++[f z.2]) := by fun_prop
  have hfold := listFold (default:α) (fun z : List β×α => z.1++[f z.2]) hs
    (X+X*(2*(X+p)+1)) (by
      intro z k
      rw [append_map_fold,code_append,List.length_append]
      let N := (encode z).length
      have help : ∀ a∈z.1.take k,(encode a).length≤N := by
        intro a ha
        have hh := element_code_le z.1 a (List.mem_of_mem_take ha)
        simp only [N,encode_prod,pairBits_length]
        omega
      have hb : ∀ b∈(z.1.take k).map f,(encode b).length≤N+p.eval N := by
        intro b hb
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        have ht := hf.routine.length_bound a
        have hh := help a ha
        have hm := polynomial_eval_mono p hh
        exact ht.trans (Nat.add_le_add hh hm)
      have hmap := list_code_bound ((z.1.take k).map f) (N+p.eval N) hb
      have ht : (z.1.take k).length≤N := (show (z.1.take k).length≤z.1.length by simp only [List.length_take]; exact Nat.min_le_right _ _).trans
        ((list_length_le_code z.1).trans (by simp only [N,encode_prod,pairBits_length]; omega))
      have hmul := Nat.mul_le_mul_right (2*(N+p.eval N)+1) ht
      simp only [List.length_map] at hmap
      have hb₀ : (encode z.2).length≤N := by simp only [N,encode_prod,pairBits_length]; omega
      simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      change (encode z.2).length+(encode ((z.1.take k).map f)).length≤N+N*(2*(N+p.eval N)+1)
      omega)
  have hh : Poly (fun l : List α => l.foldl (fun b a => b++[f a]) []) :=
    comp _ (fun l : List α => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by rw [append_map_fold,List.nil_append])

@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List α) → List α) := by
  have hs : Poly (fun z : List α×List α => z.1++z.2) := by fun_prop
  have hfold := listFold ([]:List α) (fun z : List α×List α => z.1++z.2) hs X (by
    intro z k
    rw [append_fold,code_append,List.length_append]
    have h₁ := code_flatten_le (z.1.take k)
    have h₂ : (encode (z.1.take k)).length≤(encode z.1).length := by
      have hh := congrArg (fun l => (encode l).length) (List.take_append_drop k z.1)
      rw [code_append,List.length_append] at hh
      omega
    simp only [eval_X,encode_prod,pairBits_length]
    omega)
  have hh : Poly (fun l : List (List α) => l.foldl (fun b a => b++a) []) :=
    comp _ (fun l : List (List α) => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by simp [append_fold])

@[fun_prop] theorem listFlatMap [Inhabited α] (f : α → List β) (hf : Poly f) :
    Poly (List.flatMap f) := by
  have hm := listMap f hf
  have hl : Poly (List.flatten : List (List β) → List β) := listFlatten
  have hh : Poly (fun l : List α => (l.map f).flatten) := comp _ _ hl hm
  exact hh

@[fun_prop] theorem listFilter [Inhabited α] (f : α → Bool) (hf : Poly f) :
    Poly (List.filter f) := by
  have hs : Poly (fun a => if f a then [a] else []) := by fun_prop
  have hh := listFlatMap (fun a => if f a then [a] else []) hs
  exact hh.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.filter_cons,ih]; split <;> simp_all)

end Poly
end BinaryMatching.StackCode
end

end OAI
