import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
@[simp] lemma mk₂_head (a : Γ) (L R : List Γ) : (Tape.mk₂ L (a::R)).head=a := rfl
@[simp] lemma mk₂_right (a : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_left (a : Γ) (L R : List Γ) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_write (a b : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).write b=Tape.mk₂ L (b::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]
lemma mk₂_left_nil (R : List Γ) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (default::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk,ListBlank.head_mk]
lemma mk₂_right_nil (L : List Γ) :
    (Tape.mk₂ L []).move .right=Tape.mk₂ (default::L) [] := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk,ListBlank.head_mk]
lemma mk₂_write_nil (L : List Γ) (a : Γ) :
    (Tape.mk₂ L []).write a=Tape.mk₂ L [a] := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk]
lemma blank_zero (n : ℕ) : (ListBlank.mk (List.replicate n (default : Γ)))=ListBlank.mk [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,←ListBlank.cons_mk,ih]; exact ListBlank.cons_head_tail (ListBlank.mk [])
lemma blank_append_zero (L : List Γ) (n : ℕ) :
    ListBlank.mk (L++List.replicate n default)=ListBlank.mk L := by
  induction L with
  | nil => exact blank_zero n
  | cons a L ih => rw [List.cons_append,←ListBlank.cons_mk,ih,ListBlank.cons_mk]

def Exec (M : Λ→TM1.Stmt Γ Λ σ) (c d : TM1.Cfg Γ Λ σ) (t : ℕ) : Prop :=
  ∃ k,k≤t ∧ MachineCost.run (TM1.step M) k c=d
lemma Exec.refl (M : Λ→TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) : Exec M c c 0 := ⟨0,le_rfl,rfl⟩
lemma Exec.step (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) (T : Tape Γ) :
    Exec M ⟨some l,v,T⟩ (TM1.stepAux (M l) v T) 1 := ⟨1,le_rfl,rfl⟩
lemma Exec.trans {M : Λ→TM1.Stmt Γ Λ σ} {c d e : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (g : Exec M d e t) : Exec M c e (s+t) := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  exact ⟨i+j,Nat.add_le_add hi hj,by rw [MachineCost.run_add,he,hf]⟩
lemma Exec.mono {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (hst : s≤t) : Exec M c d t :=
  let ⟨k,hk,he⟩:=h; ⟨k,hk.trans hst,he⟩

def select [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  vs.foldr (fun v tail=>.branch (fun _ s=>decide (s=v)) (f v) tail) fallback
lemma select_step [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) (v : σ) (hv : v∈vs) (T : Tape Γ) :
    TM1.stepAux (select vs f fallback) v T=TM1.stepAux (f v) v T := by
  induction vs with
  | nil => simp at hv
  | cons a as ih =>
    simp only [List.mem_cons] at hv
    simp only [select,List.foldr_cons,TM1.stepAux]
    by_cases h:v=a
    · simp only [h,decide_true,Bool.cond_true]
    · simp only [h,decide_false,Bool.cond_false]
      exact ih (hv.resolve_left h)

def writeLeft (xs : List Γ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  xs.foldr (fun a tail=>.write (fun _ _=>a) (.move .left tail)) q
lemma writeLeft_step (xs : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) (R : List Γ) :
    TM1.stepAux (writeLeft xs q) v (Tape.mk₂ [] (default::R))=
      TM1.stepAux q v (Tape.mk₂ [] (default::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeLeft,List.foldr_cons,TM1.stepAux,mk₂_write,mk₂_left_nil]
    rw [show List.foldr (fun a tail=>TM1.Stmt.write (fun _ _=>a) (.move .left tail)) q bs=writeLeft bs q from rfl,ih]
    simp only [List.reverse_cons,List.cons_append,List.append_assoc,List.nil_append]

def eraseToLeft (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.move .left (.write (fun _ _=>default) tail)) n
lemma eraseToLeft_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseToLeft xs.length q) v (Tape.mk₂ (xs++L) R)=
      TM1.stepAux q v (Tape.mk₂ L (List.replicate xs.length default++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseToLeft,TM1.stepAux,List.cons_append,mk₂_left,mk₂_write]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.move .left (.write (fun _ _=>default) tail)) xs.length=eraseToLeft xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

variable {I : Type} [DecidableEq I]
def grab (is : List I) (q : TM1.Stmt Γ Λ (I→Γ)) : TM1.Stmt Γ Λ (I→Γ) :=
  is.foldr (fun i tail=>.load (fun a v=>Function.update v i a) (.move .right tail)) q
lemma grab_step (is : List I) (f v : I→Γ) (q : TM1.Stmt Γ Λ (I→Γ)) (L R : List Γ) :
    TM1.stepAux (grab is q) v (Tape.mk₂ L (is.map f++R))=
      TM1.stepAux q (is.foldl (fun v i=>Function.update v i (f i)) v)
        (Tape.mk₂ ((is.map f).reverse++L) R) := by
  induction is generalizing v L with
  | nil => rfl
  | cons i is ih =>
    simp only [grab,List.foldr_cons,List.map_cons,List.cons_append,TM1.stepAux,mk₂_head,mk₂_right,List.foldl_cons]
    rw [show List.foldr (fun i tail=>TM1.Stmt.load (fun a v=>Function.update v i a) (.move .right tail)) q is=grab is q from rfl,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
omit [Inhabited Γ] in
lemma fold_updates (is : List I) (f v : I→Γ) (i : I) :
    (is.foldl (fun v i=>Function.update v i (f i)) v) i=if i∈is then f i else v i := by
  induction is generalizing v with
  | nil => simp
  | cons a is ih =>
    rw [List.foldl_cons,ih]
    by_cases hi:i∈is <;> by_cases ha:i=a <;> simp [hi,ha]
lemma grab_fin (n : ℕ) (f v : Fin n→Γ) (q : TM1.Stmt Γ Λ (Fin n→Γ)) (L R : List Γ) :
    TM1.stepAux (grab (List.finRange n) q) v (Tape.mk₂ L (List.ofFn f++R))=
      TM1.stepAux q f (Tape.mk₂ ((List.ofFn f).reverse++L) R) := by
  have he : (List.finRange n).map f=List.ofFn f := List.ofFn_eq_map.symm
  rw [←he,grab_step]
  have hf : (List.finRange n).foldl (fun v i=>Function.update v i (f i)) v=f := by
    funext i
    rw [fold_updates]
    simp
  rw [hf]
end MatchingFPRAS.LiteralTape

end OAI
