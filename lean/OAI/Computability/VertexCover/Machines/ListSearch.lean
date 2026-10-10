import Mathlib
import OAI.Computability.VertexCover.Machines.ListNat
import OAI.Computability.VertexCover.Machines.NatDiv

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

 theorem foldl_bits_le {α β : Type} (eb : β → List Bool)
    (f : β × α → β) (h : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length)
    (xs : List α) (b : β) :
    (eb (xs.foldl (fun b a => f (b,a)) b)).length ≤ (eb b).length := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => exact (ih (f (b,a))).trans (h b a)

noncomputable def Poly.foldNonincreasing {α β : Type} (ea : α → List Bool)
    (eb : β → List Bool) (a₀ : α) {f : β × α → β}
    (cf : Poly (prodBits eb ea) eb f)
    (h : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length) :
    Poly (prodBits eb (listBits ea)) eb (fun p => p.2.foldl (fun b a => f (b,a)) p.1) :=
  Poly.fold ea eb a₀ cf Polynomial.X (by
    intro b xs pre suf he
    have hf := foldl_bits_le eb f h pre b
    have hx := listBits_append_length ea pre suf
    have hp := listBits_length_pos ea pre
    rw [he] at hx
    simp only [Polynomial.eval_X,prodBits,pairBits_length]
    omega)

noncomputable def Poly.listAnd : Poly (listBits boolBits) boolBits (fun xs => xs.foldl (· && ·) true) :=
  (((Poly.const (listBits boolBits) boolBits true).pair (Poly.identity (listBits boolBits))).comp
    (Poly.foldNonincreasing boolBits boolBits false (Poly.bool₂ (fun p => p.1 && p.2))
      (by intros; rfl))).congr (fun _ => rfl)

noncomputable def Poly.listAny {α : Type} (ea : α → List Bool) (a₀ : α)
    {f : α → Bool} (cf : Poly ea boolBits f) :
    Poly (listBits ea) boolBits (fun xs => (xs.map f).foldl (· || ·) false) := by
  let c := Poly.foldNonincreasing boolBits boolBits false (Poly.bool₂ (fun p => p.1 || p.2))
    (by intros; rfl)
  exact ((Poly.listMap ea boolBits a₀ false cf).comp
    (((Poly.const (listBits boolBits) boolBits false).pair (Poly.identity (listBits boolBits))).comp c)).congr (fun _ => rfl)

noncomputable def Poly.listIsEmpty {α : Type} (ea : α → List Bool) :
    Poly (listBits ea) boolBits List.isEmpty :=
  ((Poly.listHasHead ea).comp (Poly.bool not)).congr (fun xs => by cases xs <;> rfl)

namespace ListCompare
variable {α : Type} [DecidableEq α]
def step (p : (List α × Bool) × α) : List α × Bool :=
  (p.1.1.tail, p.1.2 && match p.1.1 with | [] => false | b::_ => decide (p.2=b))

theorem result (xs ys : List α) (b : Bool) :
    let p := xs.foldl (fun p a => step (p,a)) (ys,b)
    (p.2 && p.1.isEmpty) = (b && decide (xs=ys)) := by
  induction xs generalizing ys b with
  | nil => cases ys <;> simp
  | cons a xs ih =>
    dsimp only
    trans ((step ((ys,b),a)).2 && decide (xs=(step ((ys,b),a)).1))
    · exact ih _ _
    · cases ys with
      | nil => simp [step]
      | cons y ys =>
        by_cases h : a=y <;> simp [step,h]

noncomputable def poly (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => decide (p.1=p.2))) :
    Poly (prodBits (prodBits (listBits ea) boolBits) ea)
      (prodBits (listBits ea) boolBits) step := by
  let s := Poly.fst (prodBits (listBits ea) boolBits) ea
  let ys := s.comp (Poly.fst (listBits ea) boolBits)
  let b := s.comp (Poly.snd (listBits ea) boolBits)
  let a := Poly.snd (prodBits (listBits ea) boolBits) ea
  let test := ys.comp (Poly.listIsEmpty ea)
  let cmp := (a.pair (ys.comp (Poly.listHeadD ea a₀))).comp ce
  let flag := (b.pair (test.ite (Poly.const _ boolBits false) cmp)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
  exact ((ys.comp (Poly.listTail ea)).pair flag).congr (fun ⟨⟨ys,b⟩,a⟩ => by
    cases ys <;> rfl)
end ListCompare

noncomputable def Poly.listEq {α : Type} [DecidableEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => decide (p.1=p.2))) :
    Poly (prodBits (listBits ea) (listBits ea)) boolBits
      (fun p : List α × List α => decide (p.1=p.2)) := by
  let e := prodBits (listBits ea) boolBits
  let c := Poly.foldNonincreasing ea e a₀ (ListCompare.poly ea a₀ ce) (by
    intro ⟨ys,b⟩ a
    have ht := listBits_tail_length_le ea ys
    simp only [e,prodBits,pairBits_length,ListCompare.step,boolBits,List.length_singleton]
    omega)
  let input := ((Poly.snd (listBits ea) (listBits ea)).pair
    (Poly.const _ boolBits true)).pair (Poly.fst (listBits ea) (listBits ea))
  let finish := ((Poly.snd (listBits ea) boolBits).pair
    ((Poly.fst (listBits ea) boolBits).comp (Poly.listIsEmpty ea))).comp
      (Poly.bool₂ (fun p => p.1 && p.2))
  exact ((input.comp c).comp finish).congr (fun p => by
    simpa only [Function.comp_apply,Bool.true_and] using ListCompare.result p.1 p.2 true)

noncomputable def Poly.rawEq : Poly (prodBits id id) boolBits
    (fun p : List Bool × List Bool => decide (p.1=p.2)) := by
  let a := (Poly.fst id id).comp Poly.rawToList
  let b := (Poly.snd id id).comp Poly.rawToList
  exact (a.pair b).comp (Poly.listEq boolBits false (Poly.bool₂ (fun p => decide (p.1=p.2))))

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
