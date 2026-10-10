import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.RankOrder
import OAI.Combinatorics.MatchingCount.Machines.TreeLookup

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def bit (b : Bool) : Data := if b then .cons .nil .nil else .nil
def nat (n : ℕ) : Data := ofList (n.bits.map bit)
def row (xs : List ℕ) : Data := ofList (xs.map nat)
def table (xs : List (List ℕ)) : Data := ofList (xs.map row)
@[simp] lemma nat_zero : nat 0=.nil := by simp [nat,Nat.bits,ofList]
@[simp] lemma row_nil : row []=.nil := rfl
lemma map_getD {α β : Type} (f : α→β) (xs : List α) (n : ℕ) (d : α) :
    (xs.map f).getD n (f d)=f (xs.getD n d) := by
  induction xs generalizing n with
  | nil => simp
  | cons _ _ ih =>
    cases n with
    | zero => rfl
    | succ index => exact ih index
lemma row_getD (xs : List ℕ) (n : ℕ) :
    (xs.map nat).getD n .nil=nat (xs.getD n 0) := by
  simpa only [nat_zero] using map_getD nat xs n 0
lemma table_getD (xs : List (List ℕ)) (n : ℕ) :
    (xs.map row).getD n .nil=row (xs.getD n []) := by
  simpa only [row_nil] using map_getD row xs n []
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeLookup
open TreeData TreeMachine RegisterProc

lemma result_frame (E : Env R) (n : ℕ) (xs : List Data) : result E n xs 3=E 3 := by
  induction n generalizing E xs with
  | zero => cases xs <;> simp [result,putPair]
  | succ n ih => cases xs with
    | nil => simp [result]
    | cons x xs => simpa [result,putPair] using ih (putPair (putPair E 2 0 .nil (unary n)) 2 1 x (ofList xs)) xs
end MatchingFPRAS.TreeLookup

namespace MatchingFPRAS.TableLookup
open TreeData TreeMachine RegisterProc

abbrev R := TreeLookup.R
abbrev first (E : Env R) (a : ℕ) (t : UnitRefresh.Materialized.Table) :=
  TreeLookup.result E a (t.map row)
def middle (E : Env R) (a : ℕ) (t : UnitRefresh.Materialized.Table) : Env R :=
  let F:=first E a t
  let G:=putPair F 2 1 (F 2) (F 2)
  putPair G 3 0 (G 3) (G 3)
def result (E : Env R) (a r : ℕ) (t : UnitRefresh.Materialized.Table) : Env R :=
  TreeLookup.result (middle E a t) r ((t.getD a []).map nat)

def program : Proc (K R) :=
  seq (compile TreeLookup.program)
    (seq (procedure (Instr.copy (Λ:=Unit) 2 1 (by decide) ()))
      (seq (procedure (Instr.copy (Λ:=Unit) 3 0 (by decide) ())) (compile TreeLookup.program)))

lemma output (E : Env R) (a r : ℕ) (t : UnitRefresh.Materialized.Table) :
    result E a r t 2=nat (UnitRefresh.Materialized.read t a r) := by
  rw [result,TreeLookup.output,row_getD]
  rfl
lemma middle_zero (E : Env R) (a : ℕ) (t : UnitRefresh.Materialized.Table) :
    middle E a t 0=E 3 := by simp [middle,putPair,TreeLookup.result_frame]
lemma middle_one (E : Env R) (a : ℕ) (t : UnitRefresh.Materialized.Table) :
    middle E a t 1=row (t.getD a []) := by
  change (putPair (putPair (first E a t) 2 1 (first E a t 2) (first E a t 2)) 3 0
    ((putPair (first E a t) 2 1 (first E a t 2) (first E a t 2)) 3)
    ((putPair (first E a t) 2 1 (first E a t 2) (first E a t 2)) 3)) 1=_
  simp only [putPair,Function.update_of_ne (by decide : (1 : R)≠0),
    Function.update_of_ne (by decide : (1 : R)≠3),Function.update_self]
  exact (TreeLookup.output E a (t.map row)).trans (table_getD t a)

theorem stack_exec (E : Env R) (a r : ℕ) (t : UnitRefresh.Materialized.Table) (B : ℕ)
    (h : SizeBound E B) (ha : E 0=unary a) (ht : E 1=table t) (hr : E 3=unary r) :
    Exec program (encodeEnv E) (encodeEnv (result E a r t))
      ((20*(a+r+2)+8)*(B+1)) ∧ SizeBound (result E a r t) B := by
  let F:=first E a t
  let G:=putPair F 2 1 (F 2) (F 2)
  have hF : SizeBound F B := (TreeLookup.runs a (t.map row) E B h ha ht).2
  have hG : SizeBound G B := hF.putPair 2 1 (F 2) (F 2) (hF 2) (hF 2)
  have hH : SizeBound (middle E a t) B := hG.putPair 3 0 (G 3) (G 3) (hG 3) (hG 3)
  have h₁:=TreeLookup.stack_exec a (t.map row) E B h ha ht
  have h₂:=copy_exec F 2 1 (by decide) ()
  have h₃:=copy_exec G 3 0 (by decide) ()
  have h₄:=TreeLookup.stack_exec r ((t.getD a []).map nat) (middle E a t) B hH
    ((middle_zero E a t).trans hr) (middle_one E a t)
  constructor
  · have he:=h₁.seq (h₂.seq (h₃.seq h₄))
    apply he.mono
    have hF1:=hF 1; have hF2:=hF 2
    have hG0:=hG 0; have hG3:=hG 3
    nlinarith
  · exact (TreeLookup.runs r ((t.getD a []).map nat) (middle E a t) B hH
      ((middle_zero E a t).trans hr) (middle_one E a t)).2
end MatchingFPRAS.TableLookup

end OAI
