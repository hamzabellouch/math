import OAI.Combinatorics.ContingencyTables.Model
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # A dimension-recursive feasible table constructor

The constructor removes a column on each inner call and a row on each
outer call. Large binary margins are never processed one unit at a time.
-/

namespace ContingencyTables.GreedyFeasibleTable

open scoped BigOperators

structure RowSplit (n : ℕ) where
  assigned : Fin n → ℕ
  remaining : Fin n → ℕ
  unused : ℕ

def splitRow : {n : ℕ} → ℕ → (Fin n → ℕ) → RowSplit n
  | 0,a,_ => ⟨Fin.elim0,Fin.elim0,a⟩
  | _n+1,a,c =>
    let b := min a (c 0)
    let tail := splitRow (a-b) (fun i => c i.succ)
    ⟨Fin.cons b tail.assigned,Fin.cons (c 0-b) tail.remaining,tail.unused⟩

lemma splitRow_columns {n : ℕ} (a : ℕ) (c : Fin n → ℕ) (i : Fin n) :
    (splitRow a c).assigned i+(splitRow a c).remaining i=c i := by
  induction n generalizing a with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [splitRow,Fin.cons_zero]
      omega
    · simpa only [splitRow,Fin.cons_succ] using ih (a-min a (c 0)) (fun j => c j.succ) j

lemma splitRow_balance {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (∑ i,(splitRow a c).assigned i)+(splitRow a c).unused=a := by
  induction n generalizing a with
  | zero => simp [splitRow]
  | succ n ih =>
    have ht := ih (a-min a (c 0)) (fun j => c j.succ)
    simp only [splitRow,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    omega

lemma splitRow_unused {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (splitRow a c).unused=a-∑ i,c i := by
  induction n generalizing a with
  | zero => simp [splitRow]
  | succ n ih =>
    simpa only [splitRow,Fin.sum_univ_succ] using
      (ih (a-min a (c 0)) (fun j => c j.succ)).trans (by omega)

lemma splitRow_sum {n : ℕ} (a : ℕ) (c : Fin n → ℕ) (ha : a ≤ ∑ i,c i) :
    (∑ i,(splitRow a c).assigned i)=a := by
  have hb := splitRow_balance a c
  rw [splitRow_unused,Nat.sub_eq_zero_of_le ha,add_zero] at hb
  exact hb

lemma splitRow_remaining_sum {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (∑ i,(splitRow a c).remaining i)=(∑ i,c i)-a := by
  have hc : (∑ i,(splitRow a c).assigned i)+(∑ i,(splitRow a c).remaining i)=∑ i,c i := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => splitRow_columns a c i)
  have hb := splitRow_balance a c
  rw [splitRow_unused] at hb
  omega

def matrix : {m n : ℕ} → (Fin m → ℕ) → (Fin n → ℕ) → Fin m → Fin n → ℕ
  | 0,_,_,_ => Fin.elim0
  | _m+1,_,r,c =>
    let row := splitRow (r 0) c
    Fin.cons row.assigned (matrix (fun i => r i.succ) row.remaining)

/-- The arithmetic constructor fills any equal-total natural margins. -/
theorem matrix_hasMargins {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) : HasMargins (matrix r c) r c := by
  induction m generalizing c with
  | zero =>
    constructor
    · intro i
      exact Fin.elim0 i
    · intro j
      have hc : c j ≤ ∑ k,c k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [Fin.sum_univ_zero] at htotal
      simp only [Fin.sum_univ_zero]
      omega
  | succ m ih =>
    have ha : r 0 ≤ ∑ j,c j := by
      rw [Fin.sum_univ_succ] at htotal
      omega
    have htail : (∑ i : Fin m,r i.succ)=∑ j,(splitRow (r 0) c).remaining j := by
      rw [splitRow_remaining_sum]
      rw [Fin.sum_univ_succ] at htotal
      omega
    have hm := ih (fun i => r i.succ) (splitRow (r 0) c).remaining htail
    constructor
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [matrix,Fin.cons_zero] using splitRow_sum (r 0) c ha
      · simpa only [matrix,Fin.cons_succ] using hm.1 i
    · intro j
      simpa only [matrix,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hm.2 j] using
        splitRow_columns (r 0) c j

/-- A literal, dimension-recursive fallback for the sampling algorithm. -/
def table {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) : Table r c := ⟨matrix r c,matrix_hasMargins r c htotal⟩

end ContingencyTables.GreedyFeasibleTable

end OAI
