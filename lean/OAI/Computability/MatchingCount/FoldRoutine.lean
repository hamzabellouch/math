import OAI.Computability.MatchingCount.UnaryArithmetic

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_drop_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.drop n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

def foldStep {α β : Type} (a₀ : α) (f : β×α → β) (z : List α×β) : List α×β :=
  if z.1.isEmpty then z else (z.1.tail,f (z.2,z.1.headD a₀))

lemma foldStep_iterate {α β : Type} (a₀ : α) (f : β×α → β) (n : ℕ) (z : List α×β) :
    (foldStep a₀ f)^[n] z=(z.1.drop n,(z.1.take n).foldl (fun b a => f (b,a)) z.2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,b⟩
    cases l with
    | nil => simp [Function.iterate_succ_apply,foldStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,foldStep,ih]

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFold (a₀ : α) (f : β×α → β) (hf : Poly f) (P : Polynomial ℕ)
    (hb : ∀ (z : List α×β) k,
      (encode ((z.1.take k).foldl (fun b a => f (b,a)) z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  have hs : Poly (foldStep a₀ f) := by unfold foldStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×β) => (foldStep a₀ f)^[z.1] z.2) :=
    boundedIterate (foldStep a₀ f) hs (X+P) (by
      intro z j hj
      rw [foldStep_iterate]
      have hl := code_drop_le z.2.1 j
      have hn : (encode z.2).length≤(encode z).length := by
        simp only [encode_prod,pairBits_length]
        omega
      have hacc := (hb z.2 j).trans (polynomial_eval_mono P hn)
      simp only [encode_prod,pairBits_length,eval_add,eval_X] at *
      omega)
  have h : Poly (fun z : List α×β => ((foldStep a₀ f)^[(encode z.1).length] z).2) :=
    second _ (comp _ (fun z : List α×β => ((encode z.1).length,z)) hi
      (pair _ _ (comp _ Prod.fst codeLength (first _ identity)) identity))
  exact h.congr (fun z => by
    rw [foldStep_iterate]
    simp only [List.take_of_length_le (list_length_le_code z.1)])

omit [Coding α] in
private lemma count_fold (l : List α) (b : ℕ) :
    l.foldl (fun b _ => b+1) b=b+l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

@[fun_prop] theorem listLength [Inhabited α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun z : ℕ×α => z.1+1) := by fun_prop
  have hfold := listFold (default:α) (fun z : ℕ×α => z.1+1) hf X (by
    intro z k
    rw [count_fold]
    have hk : (z.1.take k).length≤z.1.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have hl := list_length_le_code z.1
    simp only [encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
    omega)
  have hh : Poly (fun l : List α => l.foldl (fun b _ => b+1) 0) :=
    comp _ (fun l : List α => (l,0)) hfold (by fun_prop)
  exact hh.congr (fun l => by simp)

end Poly
end BinaryMatching.StackCode
end

end OAI
