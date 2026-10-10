import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceOccurrences
import OAI.Computability.VertexCover.Reduction.ConditionNested
import OAI.Computability.VertexCover.Machines.Primitives

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

namespace BoundedMemory
abbrev Memory (B : ℕ) := {s : List Bool // s.length ≤ B}

noncomputable instance (B : ℕ) : Fintype (Memory B) := by
  let f : (Σ n : Fin (B+1), List.Vector Bool n.val) → Memory B :=
    fun p => ⟨p.2.val, by have h := p.2.property; omega⟩
  have hf : Function.Surjective f := by
    intro ⟨s,hs⟩
    exact ⟨⟨⟨s.length, by omega⟩,⟨s,rfl⟩⟩,rfl⟩
  letI : Finite (Memory B) := Finite.of_surjective f hf
  exact Fintype.ofFinite _

noncomputable def next (B : ℕ) (q : Option (Memory B)) (b : Bool) :
    Option (Memory B) × List Bool :=
  (q.bind (fun p => if h : (p.val++[b]).length ≤ B then some ⟨p.val++[b],h⟩ else none), [])

theorem output (B : ℕ) (last : Option (Memory B) → List Bool) (s xs : List Bool)
    (h : (s++xs).length ≤ B) :
    Stream.output (next B) last (some ⟨s, by simp only [List.length_append] at h; omega⟩) xs =
      last (some ⟨s++xs,h⟩) := by
  induction xs generalizing s with
  | nil => simp only [Stream.output, List.append_nil]
  | cons b bs ih =>
    have hs : (s++[b]).length ≤ B := by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    simp only [Stream.output, next, Option.bind_some, dite_eq_left hs, List.nil_append]
    rw [ih (s++[b]) (by simpa only [List.append_assoc, List.singleton_append] using h)]
    simp only [List.append_assoc, List.singleton_append]

end BoundedMemory

noncomputable def Poly.finite {α β : Type} [Fintype α]
    (ea : α → List Bool) (eb : β → List Bool) (hc : Function.Injective ea)
    (f : α → β) : Poly ea eb f := by
  classical
  let B := Finset.univ.sup (fun a : α => (ea a).length)
  let W := Finset.univ.sup (fun a : α => (eb (f a)).length)
  let last : Option (BoundedMemory.Memory B) → List Bool := fun q =>
    match q with
    | none => []
    | some s => if h : ∃ a, ea a = s.val then eb (f h.choose) else []
  have hl : ∀ q, (last q).length ≤ W := by
    intro q
    cases q with
    | none => exact Nat.zero_le _
    | some s =>
      dsimp [last]
      split
      · exact Finset.le_sup (f := fun a : α => (eb (f a)).length) (Finset.mem_univ _)
      · exact Nat.zero_le _
  let c := Stream.poly (some (⟨[],by simp⟩ : BoundedMemory.Memory B))
    (BoundedMemory.next B) last W (by intro q b; simp [BoundedMemory.next]) hl
  apply c.realizes
  intro a
  have ha : (ea a).length ≤ B := Finset.le_sup (f := fun a : α => (ea a).length) (Finset.mem_univ a)
  rw [BoundedMemory.output B last [] (ea a) (by simpa using ha)]
  dsimp [last]
  split
  · rename_i h
    rw [hc h.choose_spec]
  · rename_i h
    exact False.elim (h ⟨a,rfl⟩)

noncomputable def Poly.bool (f : Bool → Bool) : Poly boolBits boolBits f :=
  Poly.finite boolBits boolBits (by intro a b h; simpa [boolBits] using h) f

namespace Select

def trans (s : Fin 6 × Bool) (b : Bool) : (Fin 6 × Bool) × List Bool :=
  if s.1 = 0 then ((1,s.2),[])
  else if s.1 = 1 then ((2,b),[])
  else if s.1 = 2 then ((3,s.2),[])
  else if s.1 = 3 then ((if b then 4 else 5,s.2),[])
  else if s.1 = 4 then ((3,s.2),if s.2 then [b] else [])
  else ((5,s.2),if s.2 then [] else [b])

def emb (q : Fin 3) (b : Bool) : Fin 6 × Bool := (⟨q.val+3,by omega⟩,b)

theorem bound (s : Fin 6 × Bool) (b : Bool) : (trans s b).2.length ≤ 1 := by
  rcases s with ⟨q,f⟩
  fin_cases q <;> cases f <;> cases b <;> decide

theorem trans_emb (q : Fin 3) (flag b : Bool) :
    trans (emb q flag) b =
      (emb (Project.trans flag (!flag) q b).1 flag, (Project.trans flag (!flag) q b).2) := by
  fin_cases q <;> cases flag <;> cases b <;> rfl

theorem normal (q : Fin 3) (flag : Bool) (xs : List Bool) :
    Stream.output trans (fun _ => []) (emb q flag) xs =
      Stream.output (Project.trans flag (!flag)) (fun _ => []) q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output, trans_emb, ih]

theorem encoded (flag : Bool) (a b : List Bool) :
    Stream.output trans (fun _ => []) (0,false) (pairBits [flag] (pairBits a b)) =
      if flag then a else b := by
  change Stream.output trans (fun _ => []) (emb 0 flag) (pairBits a b) = _
  rw [normal, Project.framed]
  cases flag <;> simp
end Select

noncomputable def Poly.select {α : Type} (e : α → List Bool) :
    Poly (prodBits boolBits (prodBits e e)) e
      (fun p : Bool × (α × α) => if p.1 then p.2.1 else p.2.2) :=
  (Stream.poly (0,false) Select.trans (fun _ => []) 1 Select.bound (by simp)).realizes
    (fun p => by simpa only [prodBits, boolBits, apply_ite] using
      Select.encoded p.1 (e p.2.1) (e p.2.2))

noncomputable def Poly.ite {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {test : α → Bool} {yes no : α → β} (ct : Poly ea boolBits test)
    (cy : Poly ea eb yes) (cn : Poly ea eb no) :
    Poly ea eb (fun a => if test a then yes a else no a) :=
  ((ct.pair (cy.pair cn)).comp (Poly.select eb)).congr (fun _ => rfl)

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
