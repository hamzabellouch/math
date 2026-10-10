import Mathlib
import OAI.Computability.VertexCover.Machines.Loop
import OAI.Computability.VertexCover.Machines.FiniteMemory

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

def listBits {α : Type} (e : α → List Bool) : List α → List Bool
  | [] => [false]
  | a::as => true :: pairBits (e a) (listBits e as)

@[simp] theorem listBits_nil {α : Type} (e : α → List Bool) : listBits e [] = [false] := rfl
@[simp] theorem listBits_cons {α : Type} (e : α → List Bool) (a : α) (as : List α) :
    listBits e (a::as) = true :: pairBits (e a) (listBits e as) := rfl

@[simp] theorem pairBits_length (a b : List Bool) : (pairBits a b).length = 2*a.length+1+b.length := by
  simp [pairBits, frame_length]

@[simp] theorem listBits_cons_length {α : Type} (e : α → List Bool) (a : α) (as : List α) :
    (listBits e (a::as)).length = 2*(e a).length+2+(listBits e as).length := by
  simp only [listBits_cons, List.length_cons, pairBits_length]; omega

theorem listBits_length_pos {α : Type} (e : α → List Bool) (as : List α) :
    0 < (listBits e as).length := by
  cases as <;> simp

theorem list_length_le_bits {α : Type} (e : α → List Bool) (as : List α) :
    as.length ≤ (listBits e as).length := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.length_cons, listBits_cons_length]; omega

theorem listBits_append_length {α : Type} (e : α → List Bool) (as bs : List α) :
    (listBits e (as++bs)).length + 1 = (listBits e as).length + (listBits e bs).length := by
  induction as with
  | nil => simp; omega
  | cons a as ih => simp only [List.cons_append,listBits_cons_length]; omega

theorem listBits_reverse_length {α : Type} (e : α → List Bool) (as : List α) :
    (listBits e as.reverse).length = (listBits e as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons]
    have h := listBits_append_length e as.reverse [a]
    simp only [listBits_cons_length, listBits_nil, List.length_singleton, ih] at h ⊢
    omega

namespace ListProject

def trans (left right : Bool) (defaultCode : List Bool) (q : Option (Fin 3)) (b : Bool) :
    Option (Fin 3) × List Bool :=
  match q with
  | none => if b then (some 0,[]) else (some 2,defaultCode)
  | some q => let r := Project.trans left right q b; (some r.1,r.2)

theorem bound (left right : Bool) (d : List Bool) (q : Option (Fin 3)) (b : Bool) :
    (trans left right d q b).2.length ≤ max 1 d.length := by
  cases q with
  | none => cases b <;> simp [trans]
  | some q => exact (Project.bound left right q b).trans (Nat.le_max_left _ _)

theorem normal (left right : Bool) (d : List Bool) (q : Fin 3) (xs : List Bool) :
    Stream.output (trans left right d) (fun _ => []) (some q) xs =
      Stream.output (Project.trans left right) (fun _ => []) q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output,trans,ih]

theorem encoded {α : Type} (e : α → List Bool) (left right : Bool) (d : List Bool) (xs : List α) :
    Stream.output (trans left right d) (fun _ => []) none (listBits e xs) =
      match xs with
      | [] => d
      | a::as => (if left then e a else []) ++ (if right then listBits e as else []) := by
  cases xs with
  | nil => simp [listBits, Stream.output, trans]
  | cons a as =>
    change Stream.output (trans left right d) (fun _ => []) (some 0)
      (pairBits (e a) (listBits e as)) = _
    rw [normal, Project.framed]
end ListProject

noncomputable def Poly.listCons {α : Type} (e : α → List Bool) :
    Poly (prodBits e (listBits e)) (listBits e) (fun p : α × List α => p.1::p.2) :=
  (Poly.cons true).realizes (fun _ => rfl)

noncomputable def Poly.listTail {α : Type} (e : α → List Bool) :
    Poly (listBits e) (listBits e) List.tail :=
  (Stream.poly none (ListProject.trans false true [false]) (fun _ => []) (max 1 [false].length)
    (ListProject.bound false true [false]) (by simp)).realizes (fun xs => by
      rw [ListProject.encoded]
      cases xs <;> simp)

noncomputable def Poly.listHeadD {α : Type} (e : α → List Bool) (a : α) :
    Poly (listBits e) e (fun xs => xs.headD a) :=
  (Stream.poly none (ListProject.trans true false (e a)) (fun _ => []) (max 1 (e a).length)
    (ListProject.bound true false (e a)) (by simp)).realizes (fun xs => by
      rw [ListProject.encoded]
      cases xs <;> simp)

noncomputable def Poly.listHasHead {α : Type} (e : α → List Bool) :
    Poly (listBits e) boolBits (fun xs => !xs.isEmpty) :=
  (Poly.headD false).encodeCongr (listBits e) (fun _ => rfl) (fun xs => by cases xs <;> rfl)

noncomputable def Poly.swap {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) (prodBits eb ea) Prod.swap :=
  ((Poly.snd ea eb).pair (Poly.fst ea eb)).congr (fun _ => rfl)

abbrev flagBits {α : Type} (e : α → List Bool) (p : Bool × α) : List Bool := p.1::e p.2

noncomputable def Poly.flag {α : Type} (e : α → List Bool) :
    Poly (prodBits boolBits e) (flagBits e) id :=
  Poly.append.encodeCongr (fun p => (boolBits p.1,e p.2)) (fun _ => rfl) (fun _ => rfl)

noncomputable def Poly.flagPair {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → Bool} {g : α → β} (cf : Poly ea boolBits f) (cg : Poly ea eb g) :
    Poly ea (flagBits eb) (fun a => (f a,g a)) :=
  ((cf.pair cg).comp (Poly.flag eb)).congr (fun _ => rfl)

namespace Fold
variable {α β : Type} (f : β × α → β)

def body : β × List α → Bool × (β × List α)
  | (b,[]) => (false,(b,[]))
  | (b,a::as) => (true,(f (b,a),as))

noncomputable def bodyPoly (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    (cf : Poly (prodBits eb ea) eb f) :
    Poly (prodBits eb (listBits ea)) (flagBits (prodBits eb (listBits ea))) (body f) := by
  let left := Poly.fst eb (listBits ea)
  let right := Poly.snd eb (listBits ea)
  let test := right.comp (Poly.listHasHead ea)
  let head := right.comp (Poly.listHeadD ea a₀)
  let tail := right.comp (Poly.listTail ea)
  let next := ((left.pair head).comp cf).pair tail
  exact (test.flagPair (test.ite next (Poly.identity _))).congr (by
    intro ⟨b,as⟩; cases as <;> rfl)

theorem run (ea : α → List Bool) (eb : β → List Bool) (b : β) (xs : List α) (B : ℕ)
    (bound : ∀ pre suf, pre++suf=xs →
      (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) b,suf)).length ≤ B) :
    BoundedRun (prodBits eb (listBits ea)) (body f) B (b,xs)
      (xs.foldl (fun b a => f (b,a)) b,[]) (xs.length+1) := by
  induction xs generalizing b with
  | nil => exact .stop _ (bound [] [] rfl) rfl
  | cons a as ih =>
    have htail : ∀ pre suf, pre++suf=as →
        (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) (f (b,a)),suf)).length ≤ B := by
      intro pre suf h
      exact bound (a::pre) suf (by simp [h])
    exact .next _ _ _ (bound [] (a::as) rfl) rfl (ih (f (b,a)) htail)
end Fold

noncomputable def Poly.fold {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    {f : β × α → β} (cf : Poly (prodBits eb ea) eb f) (size : Polynomial ℕ)
    (bound : ∀ b xs pre suf, pre++suf=xs →
      (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) b,suf)).length ≤
        size.eval (prodBits eb (listBits ea) (b,xs)).length) :
    Poly (prodBits eb (listBits ea)) eb (fun p => p.2.foldl (fun b a => f (b,a)) p.1) := by
  let result : β × List α → β × List α := fun p => (p.2.foldl (fun b a => f (b,a)) p.1,[])
  let c := (Fold.bodyPoly f ea eb a₀ cf).loop result size (Polynomial.X+1) (by
    intro ⟨b,xs⟩
    refine ⟨xs.length+1,?_, Fold.run f ea eb b xs _ (bound b xs)⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, prodBits, pairBits_length]
    have h := list_length_le_bits ea xs
    omega)
  exact (c.comp (Poly.fst eb (listBits ea))).congr (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
