import Mathlib
import OAI.Analysis.MatrixSigning.Realization.Realization
import OAI.Analysis.MatrixSigning.Encoding.WordOperations

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma listCode_append (ea : α → Word) (xs ys : List α) :
    listCode ea (xs++ys)=listCode ea xs++listCode ea ys := by
  simp only [listCode,FramedMapRoutine.tape,List.flatMap_append]

@[simp] lemma listCode_cons (ea : α → Word) (x : α) (xs : List α) :
    listCode ea (x::xs)=prodCode ea (listCode ea) (x,xs) := rfl

@[simp] lemma listCode_nil (ea : α → Word) : listCode ea []=[] := rfl

def consList (ea : α → Word) :
    Realizes (prodCode ea (listCode ea)) (listCode ea) (fun p => p.1::p.2) :=
  (identity (prodCode ea (listCode ea))).changeOutput (listCode ea) (fun p => p.1::p.2) (fun _ => rfl)

def appendList (ea : α → Word) :
    Realizes (prodCode (listCode ea) (listCode ea)) (listCode ea) (fun p => p.1++p.2) where
  cost := fun p => 5*(listCode ea p.1).length+4
  routine := by
    have h := WordOperations.appending.reindex (fun p : List α×List α => (listCode ea p.1,listCode ea p.2))
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [listCode_append] at hp ⊢
    exact hp

def reverseBody (ea : α → Word) :
    Realizes (prodCode (listCode ea) ea) (listCode ea) (fun p => p.2::p.1) :=
  ((second (listCode ea) ea).both (first (listCode ea) ea)).then (consList ea)

lemma fold_cons (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

def reverseList (ea : α → Word) : Realizes (listCode ea) (listCode ea) List.reverse :=
  (((constant (listCode ea) (listCode ea) []).both (identity (listCode ea))).then
    (reverseBody ea).fold).congr (fun xs => by simp)

def mapCtxUpdate (f : γ×α → β) (p : (γ×List β)×α) : γ×List β :=
  (p.1.1,f (p.1.1,p.2)::p.1.2)

def mapCtxBody (ec : γ → Word) (ea : α → Word) (eb : β → Word)
    {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode (prodCode ec (listCode eb)) ea) (prodCode ec (listCode eb)) (mapCtxUpdate f) :=
  let old := first (prodCode ec (listCode eb)) ea
  let context := old.then (first ec (listCode eb))
  let acc := old.then (second ec (listCode eb))
  let element := second (prodCode ec (listCode eb)) ea
  context.both ((((context.both element).then r).both acc).then (consList eb))

lemma fold_mapCtx (f : γ×α → β) (c : γ) (xs : List α) (acc : List β) :
    xs.foldl (fun s x => mapCtxUpdate f (s,x)) (c,acc)=
      (c,(xs.map (fun x => f (c,x))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    change xs.foldl (fun s x => mapCtxUpdate f (s,x)) (c,f (c,x)::acc)=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

def Realizes.mapCtx {ec : γ → Word} {ea : α → Word} {eb : β → Word}
    {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode ec (listCode ea)) (listCode eb) (fun p => p.2.map (fun x => f (p.1,x))) :=
  let context := first ec (listCode ea)
  let xs := second ec (listCode ea)
  let init := context.both (constant (prodCode ec (listCode ea)) (listCode eb) [])
  let loop := (init.both xs).then (mapCtxBody ec ea eb r).fold
  ((loop.then (second ec (listCode eb))).then (reverseList eb)).congr (fun p => by
    simp only [fold_mapCtx,List.append_nil,List.reverse_reverse])

end CurrentKS.Realization

end OAI
