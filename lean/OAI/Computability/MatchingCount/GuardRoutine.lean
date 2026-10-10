import OAI.Computability.MatchingCount.ScaledState

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def guardedStep {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) : ℕ×α :=
  (z.1,if (encode (f z.2)).length≤z.1 then f z.2 else z.2)

lemma guardedStep_size {α : Type} [Coding α] [Inhabited α] (f : α → α) (z : ℕ×α) (j : ℕ) :
    ((guardedStep f)^[j] z).1=z.1 ∧
      (encode ((guardedStep f)^[j] z).2).length≤ max z.1 (encode z.2).length := by
  induction j with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact ih.1
    · simp only [guardedStep,ih.1]
      split_ifs with h
      · exact h.trans (Nat.le_max_left _ _)
      · exact ih.2

lemma guardedStep_eq {α : Type} [Coding α] [Inhabited α] (f : α → α) (B : ℕ) (a : α) (k : ℕ)
    (h : ∀ j,j≤k → (encode (f^[j] a)).length≤B) :
    (guardedStep f)^[k] (B,a)=(B,f^[k] a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih (fun j hj => h j (by omega))]
    have hh := h (k+1) le_rfl
    rw [Function.iterate_succ_apply'] at hh
    simp only [guardedStep,ite_eq_left hh,Function.iterate_succ_apply']

namespace Poly
variable {α : Type} [Coding α] [Inhabited α]
@[fun_prop] theorem guardedStep_poly (f : α → α) (hf : Poly f) : Poly (guardedStep f) := by
  unfold guardedStep
  have hc : Poly (fun z : ℕ×α => (encode (f z.2)).length) :=
    Poly.comp _ (fun z : ℕ×α => f z.2) Poly.codeLength (by fun_prop)
  have hh : Poly (fun z : ℕ×α => (z.1,if decide ((encode (f z.2)).length≤z.1) then f z.2 else z.2)) := by fun_prop
  exact hh.congr (fun _ => by simp)

@[fun_prop] theorem guardedIterate (f : α → α) (hf : Poly f) :
    Poly (fun z : ℕ×(ℕ×α) => ((guardedStep f)^[z.1] z.2).2) := by
  apply second
  apply boundedIterate (guardedStep f) (guardedStep_poly f hf) (3*X+1)
  intro z j hj
  have hh := guardedStep_size f z.2 j
  rw [code_pair_length,hh.1,code_nat_length]
  have hb : max z.2.1 (encode z.2.2).length≤(encode z).length := by
    simp only [code_pair_length,code_nat_length]
    omega
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  have hN : z.2.1≤(encode z).length := by simp only [code_pair_length,code_nat_length]; omega
  omega
end Poly
end BinaryMatching.StackCode
end

end OAI
