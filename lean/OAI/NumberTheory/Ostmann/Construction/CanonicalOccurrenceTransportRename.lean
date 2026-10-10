import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCode

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistorySymbolicState Characters.RationalHistory

variable {ι κ : Type}

def StateCode.rename (f : ι → κ) (e : StateCode ι) : StateCode κ :=
  ⟨e.plus.rename f,e.minus.rename f,e.small.map (Expr.rename f)⟩

def renameTree (f : ι → κ) : {l:ℕ} → TreeCode ι l → TreeCode κ l
  | 0,e => e.rename f
  | _+1,e => (e.1.rename f,renameTree f e.2.1,renameTree f e.2.2)

def renameCompensation (f : ι → κ) : {l:ℕ} → CompensationCode ι l → CompensationCode κ l
  | 0,_ => ()
  | _+1,e => (e.1.map (Expr.rename f),renameCompensation f e.2.1,renameCompensation f e.2.2)

lemma select_map {A B : Type} (R : A → B) (d : A) (order : List ℕ) (xs : List A) :
    (select d order xs).map R=select (R d) order (xs.map R) := by
  simp only [select,List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply,List.getElem?_map]
  cases xs[i]? <;> rfl

lemma product_rename (f : ι → κ) (es : List (Expr ι)) :
    (Arithmetic.HistorySymbolicStep.product es).rename f=
      Arithmetic.HistorySymbolicStep.product (es.map (Expr.rename f)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [Arithmetic.HistorySymbolicStep.product,Expr.rename,List.map_cons,ih]

lemma pivot_rename (f : ι → κ) (s v w : ℤ) (p m : Expr ι) (u hp hm : List (Expr ι)) :
    (Arithmetic.HistorySymbolicStep.pivot s v w p m u hp hm).rename f=
      Arithmetic.HistorySymbolicStep.pivot s v w (p.rename f) (m.rename f)
        (u.map (Expr.rename f)) (hp.map (Expr.rename f)) (hm.map (Expr.rename f)) := by
  simp only [Arithmetic.HistorySymbolicStep.pivot,Expr.rename,product_rename]

theorem execute_rename (f : ι → κ) {l : ℕ} (p : Plan l) (e : StateCode ι)
    (c : CompensationCode ι l) :
    renameTree f (execute p e c)=execute p (e.rename f) (renameCompensation f c) := by
  induction p generalizing e with
  | leaf s => rfl
  | node s v w n split lo ro left right ihl ihr =>
    simp only [execute,renameTree,renameCompensation,ihl,ihr]
    congr 1
    apply Prod.ext
    · apply congrArg₂ (fun e c => execute left e c) _ rfl
      apply StateCode.ext
      · simp only [StateCode.rename,pivot_rename,List.map_take,List.map_drop,select_map,Expr.rename]
      · rfl
      · simp only [StateCode.rename,select_map,List.map_append,List.map_take,Expr.rename]
    · apply congrArg₂ (fun e c => execute right e c) _ rfl
      apply StateCode.ext
      · simp only [StateCode.rename,pivot_rename,List.map_take,List.map_drop,select_map,Expr.rename]
      · rfl
      · simp only [StateCode.rename,select_map,List.map_append,List.map_drop,Expr.rename]

lemma compensationCode_rename (f : ι → κ) {l : ℕ} (h : History l)
    (c : InternalKey h → Expr ι) :
    renameCompensation f (compensationCode h c)=compensationCode h (fun i => (c i).rename f) := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right ihl ihr =>
    simp only [compensationCode,renameCompensation,List.map_ofFn,Function.comp_def,ihl,ihr]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
