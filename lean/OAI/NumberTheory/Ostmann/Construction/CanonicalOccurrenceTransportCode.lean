import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportKeys

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistorySymbolicState Arithmetic.HistorySymbolicSlots
open Characters.RationalHistory

structure StateCode (ι : Type) where
  plus : Expr ι
  minus : Expr ι
  small : List (Expr ι)

@[ext] theorem StateCode.ext {ι : Type} {e f : StateCode ι}
    (hp : e.plus=f.plus) (hm : e.minus=f.minus) (hs : e.small=f.small) : e=f := by
  cases e
  cases f
  congr

def stateCode {ι : Type} {a : State} (e : StateExpr a ι) : StateCode ι :=
  ⟨e.plus,e.minus,List.ofFn e.small⟩

@[reducible] def TreeCode (ι : Type) : ℕ → Type _
  | 0 => StateCode ι
  | l+1 => StateCode ι × (TreeCode ι l × TreeCode ι l)

def treeCode {ι : Type} : {l:ℕ} → (h:History l) → TreeExpr ι h → TreeCode ι l
  | _,.leaf _,e => stateCode e
  | _,.node _ _ _ _ _ left right,e =>
    (stateCode e.1,treeCode left e.2.1,treeCode right e.2.2)

def select {A : Type} (default : A) (order : List ℕ) (xs : List A) : List A :=
  order.map (fun i => xs[i]?.getD default)

def permutationOrder {A : Type} {xs ys : List A} (h : xs.Perm ys) : List ℕ :=
  List.ofFn (fun i => ((Arithmetic.OccurrencePermutation.indexEquiv h).symm i).val)

lemma select_ofFn {B : Type} (default : B) {n m : ℕ} (f : Fin n → B)
    (e : Fin m → Fin n) :
    select default (List.ofFn fun i => (e i).val) (List.ofFn f)=List.ofFn (fun i => f (e i)) := by
  simp only [select,List.map_ofFn]
  congr 1
  funext i
  simp [(e i).isLt]

lemma reorder_code {ι : Type} {xs ys : List SmallSlot} (h : xs.Perm ys)
    (f : Fin xs.length → Expr ι) :
    List.ofFn (reorder h f)=select (.fixed 0) (permutationOrder h) (List.ofFn f) := by
  exact (select_ofFn (.fixed 0) f (Arithmetic.OccurrencePermutation.indexEquiv h).symm).symm

lemma leftPart_code {ι : Type} {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) :
    List.ofFn (leftPart f)=(List.ofFn f).take xs.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take]
    congr 1

lemma rightPart_code {ι : Type} {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) :
    List.ofFn (rightPart f)=(List.ofFn f).drop xs.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_drop]
    congr 1

lemma append_code {ι : Type} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι) :
    List.ofFn (append f g)=List.ofFn f++List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    by_cases hx : i<xs.length
    · rw [List.getElem_append_left (by simpa using hx)]
      simp only [List.getElem_ofFn]
      convert Fin.append_left f g ⟨i,hx⟩ using 1
      congr 1
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hx)]
      simp only [List.getElem_ofFn]
      have hiy : i-xs.length<ys.length := by
        simp only [List.length_append,List.length_ofFn] at hj
        omega
      simp only [List.length_ofFn]
      change Fin.append f g ⟨i,_⟩=g ⟨i-xs.length,_⟩
      have he : (⟨i,by simpa only [List.length_append,List.length_ofFn] using hj⟩ : Fin (xs.length+ys.length))=
          Fin.natAdd xs.length ⟨i-xs.length,hiy⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [he,Fin.append_right]

inductive Plan : ℕ → Type
  | leaf (s : ℤ) : Plan 0
  | node {l : ℕ} (s v w : ℤ) (halfLength : ℕ)
      (split leftOrder rightOrder : List ℕ) (left right : Plan l) : Plan (l+1)

def plan {V : ℕ → ℕ} {outside : List ℕ} :
    {l:ℕ} → (h:History l) → h.Supported V outside → Plan l
  | _,.leaf a,_ => .leaf a.frequency
  | _,.node a _ _ hp _ left right,hs =>
      .node a.frequency left.root.frequency right.root.frequency hp.length
        (permutationOrder (History.supported_small_split hs))
        (permutationOrder (History.supported_child_small hs).1.symm)
        (permutationOrder (History.supported_child_small hs).2.symm)
        (plan left (History.supported_left hs)) (plan right (History.supported_right hs))

@[reducible] def CompensationCode (ι : Type) : ℕ → Type _
  | 0 => Unit
  | l+1 => List (Expr ι) × (CompensationCode ι l × CompensationCode ι l)

def compensationCode {ι : Type} : {l:ℕ} → (h:History l) → 
    (InternalKey h → Expr ι) → CompensationCode ι l
  | _,.leaf _,_ => ()
  | _,.node _ _ _ _ _ left right,comp =>
      (List.ofFn fun i => comp (.inl i),
       compensationCode left (fun i => comp (.inr (.inl i))),
       compensationCode right (fun i => comp (.inr (.inr i))))

def execute {ι : Type} : {l:ℕ} → Plan l → StateCode ι → CompensationCode ι l → TreeCode ι l
  | _,.leaf _,e,_ => e
  | _,.node s v w n split lo ro left right,e,comp =>
      let es := select (.fixed 0) split e.small
      let hp := es.take n
      let hm := es.drop n
      let p := Arithmetic.HistorySymbolicStep.pivot s v w e.plus e.minus comp.1 hp hm
      (e,
       execute left ⟨p,e.plus,select (.fixed 0) lo (comp.1++hp)⟩ comp.2.1,
       execute right ⟨p,e.minus,select (.fixed 0) ro (comp.1++hm)⟩ comp.2.2)

theorem encode_code {ι : Type} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) :
    treeCode h (encode V outside h hs e comp)=execute (plan h hs) (stateCode e) (compensationCode h comp) := by
  induction h with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
    change StateExpr a ι at e
    simp only [encode,treeCode,plan,compensationCode,execute,ihl,ihr]
    congr 1
    apply Prod.ext
    · apply congrArg₂ (fun e c => execute (plan left (History.supported_left hs)) e c) _ rfl
      apply StateCode.ext
      · simp only [stateCode,leftState,pivotExpr,splitSlots,leftPart_code,rightPart_code,reorder_code]
        rfl
      · rfl
      · simp only [stateCode,leftState,reorder_code,append_code,leftPart_code,splitSlots]
        rfl
    · apply congrArg₂ (fun e c => execute (plan right (History.supported_right hs)) e c) _ rfl
      apply StateCode.ext
      · simp only [stateCode,rightState,pivotExpr,splitSlots,leftPart_code,rightPart_code,reorder_code]
        rfl
      · rfl
      · simp only [stateCode,rightState,reorder_code,append_code,rightPart_code,splitSlots]
        rfl

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
