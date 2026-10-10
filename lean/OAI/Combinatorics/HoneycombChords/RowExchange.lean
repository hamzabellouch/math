import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace OAI

/-!
# Monodromy row exchange and fusion

Formalized from *Uniform marked polygon estimates and sharp finite bridge moments*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix BigOperators
abbrev Spin := Fin 3
abbrev Local := Matrix (Spin×Spin) (Spin×Spin) ℂ
abbrev Space (n : ℕ) := Fin n→Spin
noncomputable def block (A : Local) (s t : Spin) : Matrix Spin Spin ℂ :=
  fun a b=>A (a,s) (b,t)

noncomputable def row : (n : ℕ)→(Fin n→Local)→Space n→Space n→Matrix Spin Spin ℂ
  | 0,_,_,_=>1
  | n+1,A,s,t=>block (A 0) (s 0) (t 0)*row n (Fin.tail A) (Fin.tail s) (Fin.tail t)
noncomputable def forward (n : ℕ) (A B : Fin n→Local) (s t : Space n) : Local :=
  ∑ v : Space n,Matrix.kronecker (row n A s v) (row n B v t)
noncomputable def backward (n : ℕ) (A B : Fin n→Local) (s t : Space n) : Local :=
  ∑ v : Space n,Matrix.kronecker (row n A v t) (row n B s v)
noncomputable def localForward (A B : Local) (s t : Spin) : Local :=
  ∑ v : Spin,Matrix.kronecker (block A s v) (block B v t)
noncomputable def localBackward (A B : Local) (s t : Spin) : Local :=
  ∑ v : Spin,Matrix.kronecker (block A v t) (block B s v)
lemma sum_space_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Space (n+1)→M) :
    (∑ v,f v)=∑ a : Spin,∑ v : Space n,f (Fin.cons a v) := by
  calc
    _ = ∑ p : Spin×Space n,f (Fin.cons p.1 p.2) := (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1)=>Spin))
    (fun p : Spin×Space n=>f (Fin.cons p.1 p.2)) f (fun p=>rfl)).symm
    _ = _ := Fintype.sum_prod_type _
lemma forward_succ (n : ℕ) (A B : Fin (n+1)→Local) (s t : Space (n+1)) :
    forward (n+1) A B s t=
      localForward (A 0) (B 0) (s 0) (t 0)*
        forward n (Fin.tail A) (Fin.tail B) (Fin.tail s) (Fin.tail t) := by
  unfold forward
  rw [sum_space_succ]
  simp only [row,Fin.cons_zero,Fin.tail_cons,Matrix.kronecker,Matrix.mul_kronecker_mul]
  simp only [localForward,Matrix.kronecker,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
lemma backward_succ (n : ℕ) (A B : Fin (n+1)→Local) (s t : Space (n+1)) :
    backward (n+1) A B s t=
      localBackward (A 0) (B 0) (s 0) (t 0)*
        backward n (Fin.tail A) (Fin.tail B) (Fin.tail s) (Fin.tail t) := by
  unfold backward
  rw [sum_space_succ]
  simp only [row,Fin.cons_zero,Fin.tail_cons,Matrix.kronecker,Matrix.mul_kronecker_mul]
  simp only [localBackward,Matrix.kronecker,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem row_exchange (n : ℕ) (F : Local) (A B : Fin n→Local)
    (h : ∀ i s t,F*localForward (A i) (B i) s t=localBackward (A i) (B i) s t*F)
    (s t : Space n) : F*forward n A B s t=backward n A B s t*F := by
  induction n with
  | zero => simp [forward,backward,row]
  | succ n ih =>
    rw [forward_succ,backward_succ,←mul_assoc,h 0,mul_assoc,
      ih (Fin.tail A) (Fin.tail B) (fun i=>h i.succ),←mul_assoc]
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix BigOperators

theorem row_fusion (n : ℕ) (W : Matrix (Spin×Spin) Spin ℂ)
    (A B C : Fin n→Local)
    (h : ∀ i s t,localBackward (A i) (B i) s t*W=W*block (C i) s t)
    (s t : Space n) : backward n A B s t*W=W*row n C s t := by
  induction n with
  | zero => simp [backward,row,Matrix.kronecker]
  | succ n ih =>
    rw [backward_succ,Matrix.mul_assoc,ih (Fin.tail A) (Fin.tail B) (Fin.tail C)
      (fun i=>h i.succ),←Matrix.mul_assoc,h 0,Matrix.mul_assoc]
    rfl

theorem row_quotient_fusion (n : ℕ) (Z : Matrix Spin (Spin×Spin) ℂ)
    (A B C : Fin n→Local)
    (h : ∀ i s t,Z*localForward (A i) (B i) s t=block (C i) s t*Z)
    (s t : Space n) : Z*forward n A B s t=row n C s t*Z := by
  induction n with
  | zero => simp [forward,row,Matrix.kronecker]
  | succ n ih =>
    rw [forward_succ,←Matrix.mul_assoc,h 0,Matrix.mul_assoc,ih (Fin.tail A) (Fin.tail B)
      (Fin.tail C) (fun i=>h i.succ),←Matrix.mul_assoc]
    rfl
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix BigOperators
lemma block_conjTranspose (A : Local) (hA : A.conjTranspose=A) (s t : Spin) :
    (block A s t).conjTranspose=block A t s := by
  ext a b
  exact congrFun (congrFun hA (a,t)) (b,s)
lemma localBackward_conjTranspose (A B : Local) (hA : A.conjTranspose=A)
    (hB : B.conjTranspose=B) (s t : Spin) :
    (localBackward A B s t).conjTranspose=localForward A B t s := by
  simp only [localBackward,localForward,Matrix.conjTranspose_sum,Matrix.kronecker,
    Matrix.conjTranspose_kronecker,block_conjTranspose A hA,block_conjTranspose B hB]
end CriticalHoneycomb.Transfer.RowExchange

end

end OAI
