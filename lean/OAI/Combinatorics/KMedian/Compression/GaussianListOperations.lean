import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianKernel

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

abbrev Row := List ℚ
abbrev Rows := List Row

def erase (as : List α) (p : ℕ) := as.take p++(as.drop p).tail

def insert (as : List α) (p : ℕ) (a : α) := as.take p++a::as.drop p

def pivot (row : Row) : ℕ := row.findIdx (fun q => decide (q≠0))

def coefficients (row : Row) (p : ℕ) : Row := (erase row p).map (fun q => q/row[p]?.getD 0)

def reduce (c : Row) (p : ℕ) (row : Row) : Row :=
  ((erase row p).zip c).map (fun x => x.1-x.2*row[p]?.getD 0)

def residual (row : Row) (p : ℕ) (rows : Rows) : Rows :=
  rows.map (reduce (coefficients row p) p)

def lift (row : Row) (p : ℕ) (z : Row) : Row :=
  insert z p (-(((coefficients row p).zip z).map (fun x => x.1*x.2)).sum)

def basis (slots : List Unit) : Row :=
  if slots.isEmpty then [] else 1::slots.tail.map (fun _ => 0)

def matrix {r n : ℕ} (A : Fin r → Fin n → ℚ) : Rows :=
  List.ofFn (fun i => List.ofFn (A i))

 theorem erase_eq (as : List α) (p : ℕ) : erase as p=as.eraseIdx p := by
  simp only [erase,List.eraseIdx_eq_take_drop_succ,List.tail_drop]

 theorem erase_ofFn {n : ℕ} (f : Fin (n+1) → α) (p : Fin (n+1)) :
    erase (List.ofFn f) p.val=List.ofFn (fun j => f (p.succAbove j)) := by
  rw [erase_eq]
  have hl : ((List.ofFn f).eraseIdx p.val).length=n := by
    rw [List.length_eraseIdx_of_lt (by simpa using p.isLt),List.length_ofFn]
    omega
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hl)
  intro i hi hj
  have hin : i<n := by simpa only [List.length_ofFn] using hj
  rw [List.getElem_eraseIdx]
  simp only [List.getElem_ofFn]
  by_cases hip : i<p.val
  · rw [dite_eq_left hip,Fin.succAbove_of_castSucc_lt _ _ (by exact hip)]
    rfl
  · rw [dite_eq_right hip,Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt hip)]
    rfl

 theorem get_ofFn {n : ℕ} (f : Fin n → α) (p : Fin n) (a0 : α) :
    (List.ofFn f)[p.val]?.getD a0=f p := by
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using p.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

 theorem zip_ofFn {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i => (f i,g i)) := by
  apply List.ext_getElem (by simp only [List.length_zip,List.length_ofFn,min_self])
  intro i hi hj
  simp only [List.getElem_zip,List.getElem_ofFn]

 theorem coefficients_ofFn {n : ℕ} (f : Fin (n+1) → ℚ) (p : Fin (n+1)) :
    coefficients (List.ofFn f) p.val=List.ofFn (fun j => f (p.succAbove j)/f p) := by
  rw [coefficients,erase_ofFn,get_ofFn,List.map_ofFn]
  rfl

 theorem reduce_ofFn {n : ℕ} (f : Fin (n+1) → ℚ) (c : Fin n → ℚ) (p : Fin (n+1)) :
    reduce (List.ofFn c) p.val (List.ofFn f)=List.ofFn (fun j => f (p.succAbove j)-c j*f p) := by
  rw [reduce,erase_ofFn,get_ofFn,zip_ofFn,List.map_ofFn]
  rfl

 theorem residual_matrix {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    residual (List.ofFn (A 0)) p.val (matrix (fun i : Fin r => A i.succ))=
      matrix (Gaussian.residual A p) := by
  simp only [residual,matrix,List.map_ofFn,Function.comp_def,coefficients_ofFn,reduce_ofFn]
  rfl

 theorem insert_eq (as : List α) (p : ℕ) (a : α) (h : p≤as.length) :
    insert as p a=as.insertIdx p a := by
  induction as generalizing p with
  | nil =>
      have hp : p=0 := by simpa using h
      subst p
      rfl
  | cons b bs ih =>
      cases p with
      | zero => rfl
      | succ p =>
          simp only [insert,List.take_succ_cons,List.drop_succ_cons,List.cons_append,List.insertIdx_succ_cons]
          congr 1
          exact ih p (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using h)

 theorem insert_ofFn {n : ℕ} (f : Fin n → α) (p : Fin (n+1)) (a : α) :
    insert (List.ofFn f) p.val a=List.ofFn (p.insertNth a f) := by
  rw [insert_eq _ _ _ (by simp only [List.length_ofFn]; omega)]
  apply List.ext_getElem (by rw [List.length_insertIdx_of_le_length (by simp only [List.length_ofFn]; omega),List.length_ofFn,List.length_ofFn])
  intro i hi hj
  rw [List.getElem_insertIdx]
  simp only [List.getElem_ofFn]
  have hin : i<n+1 := by simpa only [List.length_ofFn] using hj
  by_cases hip : i<p.val
  · rw [dite_eq_left hip]
    have hsmall : i<n := by omega
    have he : p.succAbove (⟨i,hsmall⟩ : Fin n)=(⟨i,hin⟩ : Fin (n+1)) := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hip)]
      rfl
    rw [← he,Fin.insertNth_apply_succAbove]
  · rw [dite_eq_right hip]
    by_cases hie : i=p.val
    · subst i
      rw [dite_eq_left rfl]
      simpa only using (Fin.insertNth_apply_same (α:=fun _ => α) p a f).symm
    · rw [dite_eq_right hie]
      have hsmall : i-1<n := by omega
      have he : p.succAbove (⟨i-1,hsmall⟩ : Fin n)=(⟨i,hin⟩ : Fin (n+1)) := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by change p.val ≤ i - 1; omega)]
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [← he,Fin.insertNth_apply_succAbove]

 theorem lift_ofFn {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) (z : Fin n → ℚ) :
    lift (List.ofFn (A 0)) p.val (List.ofFn z)=List.ofFn (Gaussian.lift A p z) := by
  simp only [lift,coefficients_ofFn,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn,insert_ofFn,Gaussian.lift]

 theorem basis_ofFn (n : ℕ) : basis (List.replicate n ())=List.ofFn (fun j : Fin n => if j.val=0 then (1:ℚ) else 0) := by
  cases n with
  | zero => simp [basis]
  | succ n =>
      rw [List.ofFn_succ]
      simp only [basis,List.replicate_succ,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.tail_cons,List.map_replicate,Fin.val_zero,ite_true]
      congr 1
      simp only [Fin.val_succ,Nat.succ_ne_zero,ite_false,List.ofFn_const]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
