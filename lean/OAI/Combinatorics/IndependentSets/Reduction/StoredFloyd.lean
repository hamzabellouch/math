import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Represented
import OAI.Combinatorics.IndependentSets.Expansion.Capped

namespace OAI

namespace IndependentSetsCut.CounterMachine.UnaryTables
lemma wordValue_words (f : ℕ → ℕ) (n k : ℕ) (h : k<n) :
    Expr.wordValue (words f n) k = f k := by
  change Expr.wordValue (Expr.unaryWords ((List.range n).map f)) k = _
  rw [Expr.wordValue_encoded]
  simp [h]

lemma words_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ j<n, f j=g j) : words f n=words g n := by
  unfold words
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)
end IndependentSetsCut.CounterMachine.UnaryTables

namespace LargeIndependentSets.StoredFloyd
open ShortestPaths
open IndependentSetsCut.CounterMachine

structure State (B : ℕ) where
  n : ℕ
  k : ℕ
  matrix : Capped.Matrix B n

def entry {B n : ℕ} (a : Capped.Matrix B n) (i j : ℕ) : ℕ :=
  if hi : i<n then if hj : j<n then (a.get ⟨i,hi⟩ ⟨j,hj⟩).val else 0 else 0

@[simp] lemma entry_fin {B n : ℕ} (a : Capped.Matrix B n) (i j : Fin n) :
    entry a i.val j.val = (a.get i j).val := by simp [entry,i.isLt,j.isLt]

def State.value {B : ℕ} (s : State B) (w : ℕ) : ℕ :=
  if w=0 then s.n else if w=1 then s.k else
    entry s.matrix ((w-2)/s.n) ((w-2)%s.n)

def State.bits {B : ℕ} (s : State B) : List Bool :=
  IndependentSetsCut.CounterMachine.UnaryTables.words s.value (2+s.n*s.n)

def State.step {B : ℕ} (s : State B) : State B where
  n := s.n
  k := s.k+1
  matrix := if h : s.k<s.n then s.matrix.pivot ⟨s.k,h⟩ else s.matrix

@[simp] lemma read_n {B : ℕ} (s : State B) : Expr.wordValue s.bits 0 = s.n := by
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]
@[simp] lemma read_k {B : ℕ} (s : State B) : Expr.wordValue s.bits 1 = s.k := by
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]

lemma read_cell {B : ℕ} (s : State B) (i j : Fin s.n) :
    Expr.wordValue s.bits (2+i.val*s.n+j.val) = (s.matrix.get i j).val := by
  have hn : 0<s.n := Nat.zero_lt_of_lt i.isLt
  have hlt : i.val*s.n+j.val < s.n*s.n := by
    calc
      _ < (i.val+1)*s.n := by nlinarith [j.isLt]
      _ ≤ s.n*s.n := Nat.mul_le_mul_right _ i.isLt
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp only [State.value,show 2+i.val*s.n+j.val≠0 by omega,ite_false,
    show 2+i.val*s.n+j.val≠1 by omega]
  rw [show 2+i.val*s.n+j.val-2=i.val*s.n+j.val by omega]
  have hd : (i.val*s.n+j.val)/s.n=i.val := by
    rw [Nat.mul_comm i.val s.n,Nat.mul_add_div hn,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  simp [hd, Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

def sizeExpr : Expr := Expr.word (.const 0)
def pivotExpr : Expr := Expr.word (.const 1)
def cellExpr (i j : Expr) : Expr :=
  Expr.word (.add (.const 2) (.add (.mul i sizeExpr) j))
def minExpr (a b : Expr) : Expr := .sub a (.sub a b)
def countExpr : Expr := .add (.const 2) (.mul sizeExpr sizeExpr)
def rowExpr : Expr := Expr.quotient (.sub (.arg 0) (.const 2)) sizeExpr
def colExpr : Expr := Expr.remainder (.sub (.arg 0) (.const 2)) sizeExpr

def valueExpr (B : ℕ) : Expr :=
  Expr.cond (Expr.equal (.arg 0) (.const 0)) sizeExpr
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (.add pivotExpr (.const 1))
      (Expr.cond (Expr.lt pivotExpr sizeExpr)
        (minExpr (cellExpr rowExpr colExpr)
          (minExpr (.add (cellExpr rowExpr pivotExpr) (cellExpr pivotExpr colExpr)) (.const (B+1))))
        (cellExpr rowExpr colExpr)))

@[simp] lemma sizeExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    sizeExpr.eval s.bits args = s.n := by simp [sizeExpr,Expr.eval]
@[simp] lemma pivotExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    pivotExpr.eval s.bits args = s.k := by simp [pivotExpr,Expr.eval]
@[simp] lemma cellExpr_eval (i j : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (cellExpr i j).eval s args = Expr.wordValue s
      (2+i.eval s args*sizeExpr.eval s args+j.eval s args) := by
  simp [cellExpr,Expr.eval,Nat.add_assoc]
@[simp] lemma minExpr_eval (a b : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (minExpr a b).eval s args = min (a.eval s args) (b.eval s args) := by
  simp only [minExpr,Expr.eval]; omega
@[simp] lemma countExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    countExpr.eval s.bits args = 2+s.n*s.n := by simp [countExpr,Expr.eval]

lemma valueExpr_eval {B : ℕ} (s : State B) (w : ℕ) (hw : w<2+s.n*s.n) :
    (valueExpr B).eval s.bits (fun _ => w) = s.step.value w := by
  by_cases hw0 : w=0
  · subst w
    simp [valueExpr,Expr.eval,State.value,State.step]
  by_cases hw1 : w=1
  · subst w
    simp [valueExpr,Expr.eval,State.value,State.step]
  have hw2 : 2≤w := by omega
  have ht : w-2<s.n*s.n := by omega
  have hn : 0<s.n := by nlinarith
  have hi : (w-2)/s.n<s.n := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hj : (w-2)%s.n<s.n := Nat.mod_lt _ hn
  let i : Fin s.n := ⟨(w-2)/s.n,hi⟩
  let j : Fin s.n := ⟨(w-2)%s.n,hj⟩
  have hr : rowExpr.eval s.bits (fun _ => w) = i.val := by simp [rowExpr,Expr.eval,i]
  have hc : colExpr.eval s.bits (fun _ => w) = j.val := by simp [colExpr,Expr.eval,j]
  simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hw0,hw1,ite_false,
    ne_eq,not_true_eq_false,
    sizeExpr_eval,pivotExpr_eval,Expr.lt_eval,minExpr_eval,cellExpr_eval,hr,hc]
  by_cases hk : s.k<s.n
  · let k : Fin s.n := ⟨s.k,hk⟩
    simp only [hk,ite_true,one_ne_zero,not_false_eq_true,read_cell]
    have h1 := read_cell s i k
    have h2 := read_cell s k j
    dsimp [k] at h1 h2
    rw [h1,h2]
    simp [State.value,State.step,hw0,hw1,hk,entry,hi,hj,
      Capped.Matrix.pivot,Capped.Matrix.get,ShortestPaths.pivot,Capped.min_val,Capped.add_val,i,j]
  · simp only [hk,ite_false,not_true_eq_false,read_cell]
    simp [State.value,State.step,hw0,hw1,hk,entry,hi,hj,i,j]

lemma body_spec {B : ℕ} (s : State B) :
    IndependentSetsCut.CounterMachine.UnaryTables.words (fun j => (valueExpr B).eval s.bits (fun _ => j))
      (countExpr.eval s.bits (fun _ => 0)) = s.step.bits := by
  rw [countExpr_eval]
  change IndependentSetsCut.CounterMachine.UnaryTables.words _ (2+s.n*s.n) = IndependentSetsCut.CounterMachine.UnaryTables.words s.step.value (2+s.n*s.n)
  exact IndependentSetsCut.CounterMachine.UnaryTables.words_congr (valueExpr_eval s)

noncomputable def body (B : ℕ) :
    Turing.TM2ComputableInPolyTime State.bits State.bits (@State.step B) :=
  IndependentSetsCut.CounterMachine.UnaryTables.encodedComputer State.bits State.bits State.step countExpr (valueExpr B) body_spec

lemma body_finiteAlphabet (B : ℕ) (k : (body B).tm.K) : Finite ((body B).tm.Γ k) :=
  IndependentSetsCut.CounterMachine.UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _ k
end LargeIndependentSets.StoredFloyd

end OAI
