import OAI.Computability.MatchingCount.IntegerRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_option_none {α : Type} [Coding α] : encode (none:Option α)=[] := rfl
lemma code_option_some {α : Type} [Coding α] (a : α) :
    (encode (some a)).length=2*(encode a).length+1 := by
  change (encode ([a]:List α)).length=_
  simp

lemma fold_code_additive {α β : Type} [Coding α] [Coding β]
    (f : β×α → β) (C : ℕ)
    (hf : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1))
    (l : List α) (b : β) :
    (encode (l.foldl (fun b a => f (b,a)) b)).length≤
      (encode b).length+C*(encode l).length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have h := hf (b,a)
    have hi := ih (f (b,a))
    simp only [List.foldl_cons,code_cons,pairBits_length]
    nlinarith

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFoldAdd [Inhabited α] (f : β×α → β) (hf : Poly f) (C : ℕ)
    (hb : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1)) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  apply listFold default f hf ((Polynomial.C C+1)*X)
  intro z k
  have hh := fold_code_additive f C hb (z.1.take k) z.2
  have ht := code_take_le z.1 k
  have hm := Nat.mul_le_mul_left C ht
  simp only [encode_prod,pairBits_length,eval_mul,eval_add,eval_C,eval_one,eval_X]
  nlinarith

@[fun_prop] theorem listDrop : Poly (fun z : ℕ×List α => z.2.drop z.1) := by
  have hi := boundedIterate (List.tail:List α → List α) listTail X (by
    intro z j hj
    have he : ∀ (k : ℕ) (l : List α),List.tail^[k] l=l.drop k := by
      intro k l
      induction k with
      | zero => simp
      | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]
    rw [he]
    have hh := code_drop_le z.2 j
    simp only [encode_prod,pairBits_length,eval_X]
    omega)
  apply hi.congr
  intro z
  induction z.1 generalizing z with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]

@[fun_prop] theorem listGetD (a : α) : Poly (fun z : List α×ℕ => z.1[z.2]?.getD a) := by
  have h : Poly (fun z : List α×ℕ => (z.1.drop z.2).headD a) := by fun_prop
  exact h.congr (fun z => by simp only [List.headD_eq_head?_getD,List.head?_drop])

@[fun_prop] theorem listNatSum : Poly (List.sum : List ℕ → ℕ) := by
  have hfold := listFoldAdd (fun z : ℕ×ℕ => z.1+z.2) natAdd 1 (by
    intro z; simp only [encode_nat,unary_length]; omega)
  have h : Poly (fun l : List ℕ => l.foldl (·+·) 0) := comp _ (fun l : List ℕ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

@[fun_prop] theorem listIntSum : Poly (List.sum : List ℤ → ℤ) := by
  have hfold := listFoldAdd (fun z : ℤ×ℤ => z.1+z.2) intAdd 1 (by
    intro z
    have h := Int.natAbs_add_le z.1 z.2
    simp only [encode_int,encode_prod,pairBits_length,intParts,encode_bool,List.length_singleton,
      encode_nat,unary_length]
    omega)
  have h : Poly (fun l : List ℤ => l.foldl (·+·) 0) := comp _ (fun l : List ℤ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

end Poly

def rangeStep (z : ℕ×List ℕ) : ℕ×List ℕ := (z.1+1,z.2++[z.1])
lemma rangeStep_iterate (k : ℕ) (z : ℕ×List ℕ) :
    rangeStep^[k] z=(z.1+k,z.2++List.range' z.1 k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply',ih,rangeStep,List.range'_concat,List.append_assoc,Nat.add_assoc]

namespace Poly
@[fun_prop] theorem listRange : Poly List.range := by
  have hs : Poly rangeStep := by unfold rangeStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×List ℕ) => rangeStep^[z.1] z.2) :=
    boundedIterate rangeStep hs (8*(X+1)^2) (by
      intro z j hj
      rw [rangeStep_iterate]
      have hb := list_code_bound (List.range' z.2.1 j) (z.2.1+j) (by
        intro a ha
        obtain ⟨i,hi,he⟩ := List.mem_range'.mp ha
        simp only [encode_nat,unary_length]
        omega)
      simp only [List.length_range'] at hb
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,code_append,List.length_append,
        eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      nlinarith [Nat.mul_le_mul hj hj, Nat.mul_le_mul_right z.2.1 hj])
  have h : Poly (fun n : ℕ => (rangeStep^[n] (0,[])).2) := by fun_prop
  exact h.congr (fun n => by simp [rangeStep_iterate,List.range_eq_range'])
end Poly
end BinaryMatching.StackCode
end

end OAI
