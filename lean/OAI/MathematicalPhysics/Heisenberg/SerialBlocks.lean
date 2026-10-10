import OAI.MathematicalPhysics.Heisenberg.MeshProduct

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Serial
open MeshPair
variable {V : Type} [Fintype V] [DecidableEq V]

lemma prefix_add (K : ℕ → Matrix V V ℝ) (m n : ℕ) :
    prefixMatrix K (m+n)=prefixMatrix (fun j=>K (m+j)) n*prefixMatrix K m := by
  induction n with
  | zero=>simp [prefixMatrix]
  | succ n ih=>rw [Nat.add_succ,prefixMatrix,ih,prefixMatrix,Matrix.mul_assoc]

lemma prefix_congr (K L : ℕ → Matrix V V ℝ) (n : ℕ)
    (h : ∀ j,j<n → K j=L j) : prefixMatrix K n=prefixMatrix L n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [prefixMatrix,prefixMatrix,h n (by omega),ih (fun j hj=>h j (by omega))]

lemma prefix_periodic (K : ℕ → Matrix V V ℝ) (Q k : ℕ) :
    prefixMatrix (fun j=>K (j%Q)) (k*Q)=(prefixMatrix (fun j=>K (j%Q)) Q)^k := by
  induction k with
  | zero=>simp [prefixMatrix]
  | succ k ih=>
    rw [Nat.succ_mul,prefix_add,ih,pow_succ']
    congr 1
    apply prefix_congr
    intro j _
    rw [Nat.add_mod]
    simp

lemma prefix_period (K : ℕ → Matrix V V ℝ) (Q : ℕ) :
    prefixMatrix (fun j=>K (j%Q)) Q=prefixMatrix K Q := by
  apply prefix_congr
  intro j hj
  rw [Nat.mod_eq_of_lt hj]

lemma completed_sweeps (A P : ℕ → Matrix V V ℝ) (q c k : ℕ) :
    let Q:=q+c
    let base : ℕ → Matrix V V ℝ:=fun j=>if j<q then A j else 1
    let final : ℕ → Matrix V V ℝ:=fun j=>if j<q then A j else P (j-q)
    let all : ℕ → Matrix V V ℝ:=fun j=>if j<k*Q then base (j%Q) else final (j-k*Q)
    prefixMatrix all ((k+1)*Q)=prefixMatrix P c*(prefixMatrix A q)^(k+1) := by
  intro Q base final all
  rw [Nat.succ_mul,prefix_add]
  have hfirst : prefixMatrix all (k*Q)=(prefixMatrix A q)^k := by
    trans prefixMatrix (fun j=>base (j%Q)) (k*Q)
    · apply prefix_congr; intro j hj; simp [all,hj]
    rw [prefix_periodic,prefix_period]
    congr 1
    change prefixMatrix base (q+c)=_
    rw [prefix_add]
    have he : prefixMatrix (fun j=>base (q+j)) c=1 := by
      suffices ∀ n,prefixMatrix (fun j=>base (q+j)) n=1 from this c
      intro n
      induction n with
      | zero=>rfl
      | succ n ih=>rw [prefixMatrix,ih]; simp [base]
    rw [he,Matrix.one_mul]
    apply prefix_congr; intro j hj; simp [base,hj]
  have hlast : prefixMatrix (fun j=>all (k*Q+j)) Q=prefixMatrix P c*prefixMatrix A q := by
    trans prefixMatrix final Q
    · apply prefix_congr; intro j _; simp [all]
    change prefixMatrix final (q+c)=_
    rw [prefix_add]
    congr 1
    · apply prefix_congr; intro j _; simp [final]
    · apply prefix_congr; intro j hj; simp [final,hj]
  rw [hfirst,hlast,Matrix.mul_assoc,pow_succ']

end Heisenberg.Serial
end
end

end OAI
