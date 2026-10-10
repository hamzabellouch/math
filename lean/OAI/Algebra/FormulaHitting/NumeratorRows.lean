import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Matrix.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace NCHitting

open Polynomial

variable {F : Type*} [Field F]

def numeratorRow {I : Type*} [Fintype I] (q : F[X]) (P : Matrix I I F[X])
    (u : I → F) : ℕ → I → F[X]
  | 0, l => C (u l)
  | j + 1, l => q * (numeratorRow q P u j l).derivative -
      C (j : F) * q.derivative * numeratorRow q P u j l +
      ∑ t : I, numeratorRow q P u j t * P t l

private theorem degree_q_derivative {q p : F[X]} {n b : ℕ}
    (hn : 0 < n) (hq : q.natDegree ≤ n) (hp : p.natDegree ≤ b) :
    (q * p.derivative).natDegree ≤ b + (n-1) := by
  by_cases hzero : p.natDegree = 0
  · simp [Polynomial.derivative_of_natDegree_zero hzero]
  · have hb : 0 < b := by omega
    have hd := p.natDegree_derivative_le
    have hm : (q * p.derivative).natDegree ≤ q.natDegree + p.derivative.natDegree :=
      Polynomial.natDegree_mul_le
    omega

theorem numeratorRow_degree {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (hq : q.natDegree ≤ n) (hP : ∀ t l, (P t l).natDegree ≤ n-1)
    (j : ℕ) (l : I) :
    (numeratorRow q P u j l).natDegree ≤ j * (n-1) := by
  induction j generalizing l with
  | zero => simp [numeratorRow]
  | succ j ih =>
    have ihall : ∀ l, (numeratorRow q P u j l).natDegree ≤ j * (n-1) := by
      intro l'
      exact ih l'
    have ha := degree_q_derivative hn hq (ihall l)
    have hb : (C (j : F) * q.derivative * numeratorRow q P u j l).natDegree ≤
        j * (n-1) + (n-1) := by
      have hq' : q.derivative.natDegree ≤ n-1 :=
        q.natDegree_derivative_le.trans (Nat.sub_le_sub_right hq 1)
      have hC := Polynomial.natDegree_C_mul_le (j : F) q.derivative
      have hmul : (C (j : F) * q.derivative * numeratorRow q P u j l).natDegree ≤
          (C (j : F) * q.derivative).natDegree + (numeratorRow q P u j l).natDegree :=
        Polynomial.natDegree_mul_le
      have hp := ihall l
      omega
    have hc : (∑ t : I, numeratorRow q P u j t * P t l).natDegree ≤
        j * (n-1) + (n-1) := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t _
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (ihall t) (hP t l))
    rw [numeratorRow, Nat.add_mul, one_mul]
    apply Polynomial.natDegree_add_le_of_degree_le _ hc
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ha hb)

end NCHitting

end

end OAI
