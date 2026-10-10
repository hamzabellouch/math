import OAI.Computability.MatchingCount.ListRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem natSucc : Poly (fun n : ℕ => n+1) := by
  refine ⟨(Routine.pushBit true).reindex encode encode (fun n : ℕ => n+1) unary
    (fun _ => rfl) ?_⟩
  intro n
  simp

@[fun_prop] theorem natPred : Poly (Nat.pred : ℕ → ℕ) := by
  refine ⟨Routine.tail.reindex encode encode Nat.pred unary (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natZeroTest : Poly (fun n : ℕ => decide (n=0)) := by
  refine ⟨Routine.isEmpty.reindex encode encode (fun n : ℕ => decide (n=0)) unary
    (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natAdd : Poly (fun z : ℕ×ℕ => z.1+z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : ℕ×ℕ => z.1+z.2)
    (fun z => (unary z.1,unary z.2)) (fun _ => rfl) ?_⟩
  intro z
  simp only [id_eq,encode_nat,unary,List.replicate_add]

@[fun_prop] theorem natSub : Poly (fun z : ℕ×ℕ => z.1-z.2) := by
  have hp : Poly (fun z : ℕ×ℕ => Nat.pred^[z.1] z.2) :=
    boundedIterate Nat.pred natPred X (by
      intro z j hj
      simp only [Nat.pred_iterate,encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
      omega)
  have h : Poly (fun z : ℕ×ℕ => Nat.pred^[z.2] z.1) := by fun_prop
  exact h.congr (fun z => Nat.pred_iterate z.1 z.2)

@[fun_prop] theorem boolNot : Poly (Bool.not : Bool → Bool) := by
  have h : Poly (fun b : Bool => if b then false else true) := by fun_prop
  exact h.congr (fun b => by cases b <;> rfl)

@[fun_prop] theorem boolAnd : Poly (fun z : Bool×Bool => z.1 && z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then z.2 else false) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem boolOr : Poly (fun z : Bool×Bool => z.1 || z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then true else z.2) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem natLE : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℕ×ℕ => decide (z.1-z.2=0)) := comp _ _ natZeroTest natSub
  exact h.congr (fun z => by simp [Nat.sub_eq_zero_iff_le])

@[fun_prop] theorem natLT : Poly (fun z : ℕ×ℕ => decide (z.1<z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => !(decide (z.2≤z.1))) := comp _ _ boolNot hle
  exact h.congr (fun z => by simp [←decide_not])

@[fun_prop] theorem natEQ : Poly (fun z : ℕ×ℕ => decide (z.1=z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2) && decide (z.2≤z.1)) :=
    comp _ _ boolAnd (pair _ _ natLE hle)
  exact h.congr (fun z => by simp [le_antisymm_iff])

private def addStep (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.2+z.1)
private lemma addStep_iterate (n : ℕ) (z : ℕ×ℕ) : addStep^[n] z=(z.1,z.2+n*z.1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,addStep,Nat.add_mul,Nat.add_assoc]

@[fun_prop] theorem natMul : Poly (fun z : ℕ×ℕ => z.1*z.2) := by
  have hs : Poly addStep := by unfold addStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => addStep^[z.1] z.2) :=
    boundedIterate addStep hs ((X+1)^2) (by
      intro z j hj
      simp only [addStep_iterate,encode_prod,encode_nat,unary_length,pairBits_length,
        eval_pow,eval_add,eval_X,eval_one]
      have hh : j*z.2.1≤z.1*z.2.1 := Nat.mul_le_mul_right _ hj
      nlinarith [sq_nonneg (z.1:ℤ),sq_nonneg (z.2.1:ℤ)])
  have h : Poly (fun z : ℕ×ℕ => (addStep^[z.2] (z.1,0)).2) := by fun_prop
  exact h.congr (fun z => by simp [addStep_iterate,Nat.mul_comm])

@[fun_prop] theorem natMin : Poly (fun z : ℕ×ℕ => min z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])

@[fun_prop] theorem natMax : Poly (fun z : ℕ×ℕ => max z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])

variable {α : Type} [Coding α]
@[fun_prop] theorem natLe_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ natLE (pair _ _ hf hg)
@[fun_prop] theorem natLt_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ natLT (pair _ _ hf hg)
@[fun_prop] theorem natEq_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a=g a)) := comp _ _ natEQ (pair _ _ hf hg)
@[fun_prop] theorem natPow (k : ℕ) : Poly (fun n : ℕ => n^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (constant (α := ℕ) (1:ℕ))
  | succ k ih =>
    have h : Poly (fun n : ℕ => n^k*n) := comp _ _ natMul (pair _ _ ih identity)
    exact h.congr (fun n => (pow_succ n k).symm)
end Poly
end BinaryMatching.StackCode
end

end OAI
