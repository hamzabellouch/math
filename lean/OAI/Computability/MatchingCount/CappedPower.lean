import OAI.Computability.MatchingCount.GuardRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def capDouble (z : ℕ×ℕ) : ℕ×ℕ := (z.1,min z.1 (2*z.2))
lemma capDouble_spec (z : ℕ×ℕ) (k : ℕ) :
    (capDouble^[k] z).1=z.1 ∧ (capDouble^[k] z).2≤ max z.1 z.2 := by
  induction k with
  | zero => exact ⟨rfl,Nat.le_max_right _ _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1,(min_le_left _ _).trans (by rw [ih.1]; exact Nat.le_max_left _ _)⟩

lemma capDouble_start (b k : ℕ) : (capDouble^[k] (b,min b 1))=(b,min b (2^k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    change (b,min b (2*min b (2^k)))=(b,min b (2^(k+1)))
    rw [pow_succ]
    congr 1
    omega

def cappedPow2 (b k : ℕ) : ℕ := (capDouble^[k] (b,min b 1)).2
lemma cappedPow2_eq (b k : ℕ) : cappedPow2 b k=min b (2^k) := by
  simp only [cappedPow2,capDouble_start]
lemma cappedPow2_of_le (b k : ℕ) (h : 2^k≤b) : cappedPow2 b k=2^k := by
  rw [cappedPow2_eq,min_eq_right h]

namespace Poly
@[fun_prop] theorem capDouble_poly : Poly capDouble := by unfold capDouble; fun_prop
@[fun_prop] theorem cappedPow2_poly : Poly (fun z : ℕ×ℕ => cappedPow2 z.1 z.2) := by
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => capDouble^[z.1] z.2) :=
    boundedIterate capDouble capDouble_poly (3*X+1) (by
      intro z j hj
      obtain ⟨h₁,h₂⟩ := capDouble_spec z.2 j
      rw [code_pair_length,h₁,code_nat_length,code_nat_length]
      have hm : max z.2.1 z.2.2≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      have hn : z.2.1≤(encode z).length := by
        simp only [code_pair_length,code_nat_length]; omega
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)
  unfold cappedPow2
  fun_prop
end Poly
end BinaryMatching.StackCode
end

end OAI
