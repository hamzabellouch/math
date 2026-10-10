import Mathlib
import OAI.Computability.VertexCover.Machines.Primitive

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
open Turing

noncomputable def Poly.realizes {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : List Bool → List Bool} {g : α → β} (c : Poly id id f)
    (h : ∀ a, f (ea a) = eb (g a)) : Poly ea eb g where
  computation := { c.computation with
    outputsFun := fun a => by
      have run := c.computation.outputsFun (ea a)
      simpa only [id_eq, h a] using run }
  finiteAlphabet := c.finiteAlphabet

noncomputable def Poly.congr {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f g : α → β} (c : Poly ea eb f) (h : ∀ a, f a = g a) : Poly ea eb g where
  computation := { c.computation with
    outputsFun := fun a => by
      simpa only [h a] using c.computation.outputsFun a }
  finiteAlphabet := c.finiteAlphabet

noncomputable def Poly.encodeCongr {α β γ δ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {ed : δ → List Bool} {f : α → β} {g : γ → δ}
    (c : Poly ea eb f) (lift : γ → α) (hi : ∀ a, ea (lift a) = ec a)
    (ho : ∀ a, eb (f (lift a)) = ed (g a)) : Poly ec ed g where
  computation := { c.computation with
    outputsFun := fun a => by
      simpa only [hi a, ho a] using c.computation.outputsFun (lift a) }
  finiteAlphabet := c.finiteAlphabet

abbrev prodBits {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (p : α × β) : List Bool :=
  pairBits (ea p.1) (eb p.2)

noncomputable def Poly.identity {α : Type} (ea : α → List Bool) : Poly ea ea id := by
  let δ : Unit → Bool → Unit × List Bool := fun _ b => ((),[b])
  have h (q : Unit) (s : List Bool) : Stream.output δ (fun _ => []) q s = s := by
    induction s generalizing q with
    | nil => rfl
    | cons b bs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly () δ (fun _ => []) 1 (by simp [δ]) (by simp)).realizes
    (fun a => h () (ea a))

noncomputable def Poly.const {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (b : β) : Poly ea eb (fun _ => b) := by
  let δ : Unit → Bool → Unit × List Bool := fun _ _ => ((),[])
  have h (q : Unit) (s : List Bool) : Stream.output δ (fun _ => eb b) q s = eb b := by
    induction s generalizing q with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly () δ (fun _ => eb b) (eb b).length (by simp [δ]) (by simp)).realizes
    (fun a => h () (ea a))

namespace Project
                                                                                
def trans (left right : Bool) (q : Fin 3) (b : Bool) : Fin 3 × List Bool :=
  if q = 0 then (if b then 1 else 2, [])
  else if q = 1 then (0, if left then [b] else [])
  else (2, if right then [b] else [])

theorem bound (left right : Bool) (q : Fin 3) (b : Bool) :
    (trans left right q b).2.length ≤ 1 := by
  unfold trans; split <;> try split <;> cases left <;> cases right <;> simp_all

theorem tail (left right : Bool) (s : List Bool) :
    Stream.output (trans left right) (fun _ => []) 2 s = if right then s else [] := by
  induction s with
  | nil => simp [Stream.output]
  | cons b bs ih => cases right <;> simp [Stream.output, trans, ih]

theorem framed (left right : Bool) (a b : List Bool) :
    Stream.output (trans left right) (fun _ => []) 0 (pairBits a b) =
      (if left then a else []) ++ (if right then b else []) := by
  induction a with
  | nil => simpa [pairBits, frame, Stream.output, trans] using tail left right b
  | cons x xs ih =>
    simp only [pairBits, frame, List.cons_append, Stream.output, trans, ↓reduceIte,
      Fin.reduceEq, List.nil_append] at ih ⊢
    cases left <;> simp_all
end Project

noncomputable def Poly.fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) ea Prod.fst :=
  (Stream.poly 0 (Project.trans true false) (fun _ => []) 1
    (Project.bound true false) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true, List.append_nil] using
        Project.framed true false (ea p.1) (eb p.2))

noncomputable def Poly.snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) eb Prod.snd :=
  (Stream.poly 0 (Project.trans false true) (fun _ => []) 1
    (Project.bound false true) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true, List.nil_append] using
        Project.framed false true (ea p.1) (eb p.2))

noncomputable def Poly.append : Poly (prodBits id id) id (fun p : List Bool × List Bool => p.1++p.2) :=
  (Stream.poly 0 (Project.trans true true) (fun _ => []) 1
    (Project.bound true true) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, prodBits, id_eq] using Project.framed true true p.1 p.2)

noncomputable def Poly.cons (b : Bool) : Poly id id (List.cons b) := by
  let δ : Bool → Bool → Bool × List Bool := fun first x => (false, if first then [b,x] else [x])
  let last : Bool → List Bool := fun first => if first then [b] else []
  have noPrefix (s : List Bool) : Stream.output δ last false s = s := by
    induction s with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, last, ih]
  have yesPrefix (s : List Bool) : Stream.output δ last true s = b::s := by
    cases s with
    | nil => rfl
    | cons x xs => simp [Stream.output, δ, noPrefix]
  exact (Stream.poly true δ last 2 (by intro q x; cases q <;> simp [δ])
    (by intro q; cases q <;> simp [last])).realizes yesPrefix

noncomputable def Poly.tail : Poly id id List.tail := by
  let δ : Bool → Bool → Bool × List Bool := fun first x => (false, if first then [] else [x])
  have rest (s : List Bool) : Stream.output δ (fun _ => []) false s = s := by
    induction s with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, ih]
  have first (s : List Bool) : Stream.output δ (fun _ => []) true s = s.tail := by
    cases s with
    | nil => rfl
    | cons x xs => simp [Stream.output, δ, rest]
  exact (Stream.poly true δ (fun _ => []) 1 (by intro q x; cases q <;> simp [δ])
    (by simp)).realizes first

abbrev boolBits (b : Bool) : List Bool := [b]

noncomputable def Poly.isEmpty : Poly id boolBits List.isEmpty := by
  let δ : Bool → Bool → Bool × List Bool := fun _ _ => (false,[])
  have h (q : Bool) (s : List Bool) :
      Stream.output δ boolBits q s = [q && s.isEmpty] := by
    induction s generalizing q with
    | nil => simp [Stream.output, boolBits]
    | cons x xs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly true δ boolBits 1 (by simp [δ]) (by simp [boolBits])).realizes
    (fun s => by simpa only [Bool.true_and, boolBits, id_eq] using h true s)

noncomputable def Poly.headD (b : Bool) : Poly id boolBits (fun s => s.headD b) := by
  let δ : Option Bool → Bool → Option Bool × List Bool := fun q x => (q.or (some x),[])
  let last : Option Bool → List Bool := fun q => [q.getD b]
  have h (q : Option Bool) (s : List Bool) :
      Stream.output δ last q s = [(q.or s.head?).getD b] := by
    induction s generalizing q with
    | nil => simp [Stream.output, last]
    | cons x xs ih =>
      simp only [Stream.output, δ, List.nil_append, ih]
      cases q <;> simp
  exact (Stream.poly none δ last 1 (by simp [δ]) (by simp [last])).realizes
    (fun s => by have hh := h none s; cases s <;> simpa [boolBits] using hh)

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
