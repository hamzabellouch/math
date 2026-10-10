import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.StoredFloyd

namespace OAI

namespace LargeIndependentSets.UniformLC
open IndependentSetsCut.CounterMachine
open scoped Classical BigOperators
noncomputable section

structure Table (L R : Type) where
  nu : ℕ
  nv : ℕ
  ne : ℕ
  hu : 0 < nu
  hv : 0 < nv
  he : 0 < ne
  left : Fin ne → Fin nu
  right : Fin ne → Fin nv
  project : Fin ne → L → R

def Table.lc {L R : Type} (t : Table L R) : LabelCoverData (Fin t.nu) (Fin t.nv) L R (Fin t.ne) :=
  ⟨t.left,t.right,t.project⟩

instance {L R : Type} (t : Table L R) : Nonempty (Fin t.ne) := ⟨⟨0,t.he⟩⟩

variable {L R : Type} [Fintype L] [Fintype R]

def projectCode (f : L → R) : ℕ := (Fintype.equivFin (L → R) f).val

def Table.value (t : Table L R) (w : ℕ) : ℕ :=
  if w=0 then t.nu else if w=1 then t.nv else if w=2 then t.ne else
    if h : (w-3)/3 < t.ne then
      if (w-3)%3=0 then (t.left ⟨(w-3)/3,h⟩).val
      else if (w-3)%3=1 then (t.right ⟨(w-3)/3,h⟩).val
      else projectCode (t.project ⟨(w-3)/3,h⟩)
    else 0

def Table.bits (t : Table L R) := UnaryTables.words t.value (3+3*t.ne)

@[simp] lemma read_nu (t : Table L R) : Expr.wordValue t.bits 0=t.nu := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]
@[simp] lemma read_nv (t : Table L R) : Expr.wordValue t.bits 1=t.nv := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]
@[simp] lemma read_ne (t : Table L R) : Expr.wordValue t.bits 2=t.ne := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]

lemma read_field (t : Table L R) (c : Fin t.ne) (j : Fin 3) :
    Expr.wordValue t.bits (3+3*c.val+j.val) =
      if j.val=0 then (t.left c).val else if j.val=1 then (t.right c).val else projectCode (t.project c) := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by have := c.isLt; have := j.isLt; omega)]
  have hsub : 3+3*c.val+j.val-3=3*c.val+j.val := by omega
  have hdiv : (3*c.val+j.val)/3=c.val := by omega
  have hmod : (3*c.val+j.val)%3=j.val := by omega
  simp [Table.value,show 3+3*c.val+j.val≠1 by omega,
    show 3+3*c.val+j.val≠2 by omega,hsub,hdiv,hmod,c.isLt]

def nuExpr : Expr := Expr.word (.const 0)
def nvExpr : Expr := Expr.word (.const 1)
def neExpr : Expr := Expr.word (.const 2)
def fieldExpr (c : Expr) (j : ℕ) : Expr := Expr.word (.add (.add (.const 3) (.mul (.const 3) c)) (.const j))

@[simp] lemma nuExpr_eval (t : Table L R) (a : ℕ → ℕ) : nuExpr.eval t.bits a=t.nu := by simp [nuExpr,Expr.eval]
@[simp] lemma nvExpr_eval (t : Table L R) (a : ℕ → ℕ) : nvExpr.eval t.bits a=t.nv := by simp [nvExpr,Expr.eval]
@[simp] lemma neExpr_eval (t : Table L R) (a : ℕ → ℕ) : neExpr.eval t.bits a=t.ne := by simp [neExpr,Expr.eval]

lemma fieldExpr_eval (t : Table L R) (a : ℕ → ℕ) (c : Expr) (e : Fin t.ne)
    (hc : c.eval t.bits a=e.val) (j : Fin 3) :
    (fieldExpr c j.val).eval t.bits a =
      if j.val=0 then (t.left e).val else if j.val=1 then (t.right e).val else projectCode (t.project e) := by
  simp only [fieldExpr,Expr.word_eval,Expr.eval,hc,read_field]

end
end LargeIndependentSets.UniformLC

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators

def finLookup {m : ℕ} (f : Fin m → ℕ) (x : Expr) : Expr :=
  listSum (List.finRange m) (fun i => .mul (equal x (.const i.val)) (.const (f i)))

lemma finLookup_eval {m : ℕ} (f : Fin m → ℕ) (x : Expr) (s : List Bool) (a : ℕ → ℕ)
    (i : Fin m) (hi : x.eval s a=i.val) :
    (finLookup f x).eval s a=f i := by
  simp only [finLookup,listSum_eval,eval,equal_eval,hi,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp [Fin.val_inj]

noncomputable def staticLookup {α : Type} [Fintype α] (f : α → ℕ) (x : Expr) : Expr :=
  finLookup (fun i => f ((Fintype.equivFin α).symm i)) x

lemma staticLookup_eval {α : Type} [Fintype α] (f : α → ℕ) (x : Expr)
    (s : List Bool) (a : ℕ → ℕ) (v : α) (hv : x.eval s a=(Fintype.equivFin α v).val) :
    (staticLookup f x).eval s a=f v := by
  rw [staticLookup,finLookup_eval _ _ _ _ _ hv,Equiv.symm_apply_apply]

def listAll {α : Type} (xs : List α) (f : α → Expr) : Expr :=
  .zero (listSum xs (fun a => .zero (f a)))

lemma listAll_eval {α : Type} (xs : List α) (f : α → Expr) (s : List Bool) (a : ℕ → ℕ) :
    (listAll xs f).eval s a = if ∀ x ∈ xs, (f x).eval s a≠0 then 1 else 0 := by
  simp only [listAll,eval,listSum_eval]
  congr 1
  simp only [List.sum_eq_zero_iff,List.mem_map,forall_exists_index,and_imp]
  simp

end IndependentSetsCut.CounterMachine.Expr

end OAI
