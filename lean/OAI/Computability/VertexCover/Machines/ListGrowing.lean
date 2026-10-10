import Mathlib
import OAI.Computability.VertexCover.Machines.ListParam
import OAI.Computability.VertexCover.Machines.ListSearch

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

noncomputable def Poly.foldGrowing {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : β × α → β} (cf : Poly (prodBits eb ea) eb f) (K : ℕ)
    (hstep : ∀ b a, (eb (f (b,a))).length ≤ (eb b).length + K * (2*(ea a).length+2)) :
    Poly (prodBits eb (listBits ea)) eb (fun p : β × List α => p.2.foldl (fun b a => f (b,a)) p.1) := by
  have grow (xs : List α) (b : β) :
      (eb (xs.foldl (fun b a => f (b,a)) b)).length ≤ (eb b).length+K*(listBits ea xs).length := by
    induction xs generalizing b with
    | nil => simp
    | cons a xs ih =>
      have hh := hstep b a
      have ht := ih (f (b,a))
      simp only [List.foldl_cons,listBits_cons_length]
      nlinarith
  exact Poly.fold ea eb a₀ cf (Polynomial.C (2*K+3)*Polynomial.X+3) (by
    intro b xs pre suf h
    have hg := grow pre b
    have hp := listBits_append_length ea pre suf
    rw [h] at hp
    have hpos := listBits_length_pos ea pre
    have hpos₂ := listBits_length_pos ea suf
    simp only [prodBits,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat]
    nlinarith)

 theorem foldl_or_any {α : Type} (f : α → Bool) (xs : List α) (b : Bool) :
    (xs.map f).foldl (· || ·) b = (b || xs.any f) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.or_assoc]

noncomputable def Poly.listAny' {α : Type} (ea : α → List Bool) (a₀ : α)
    {f : α → Bool} (cf : Poly ea boolBits f) :
    Poly (listBits ea) boolBits (fun xs => xs.any f) :=
  (Poly.listAny ea a₀ cf).congr (fun xs => by simp only [foldl_or_any,Bool.false_or])

noncomputable def Poly.listContains {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits ea (listBits ea)) boolBits (fun p : α × List α => p.2.any (p.1 == ·)) :=
  ((Poly.withParam ea ea a₀ a₀).comp (Poly.listAny' (prodBits ea ea) (a₀,a₀) ce)).congr
    (fun p => by
      change (p.2.map (p.1,·)).any (fun q => q.1 == q.2) = _
      simp only [List.any_map,Function.comp_def])

namespace Dedup
variable {α : Type} [BEq α]
def step (p : List α × α) : List α := if p.1.any (p.2 == ·) then p.1 else p.2::p.1

theorem fold (xs out : List α) :
    (xs.foldl (fun s a => step (s,a)) out).reverse = List.eraseDupsBy.loop (· == ·) xs out := by
  induction xs generalizing out with
  | nil => rfl
  | cons a xs ih =>
    change (xs.foldl (fun s a => step (s,a)) (step (out,a))).reverse = _
    rw [ih]
    simp only [step,List.eraseDupsBy.loop]
    cases h : out.any (a == ·) <;> rfl

noncomputable def poly (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (prodBits (listBits ea) ea) (listBits ea) step :=
  (((Poly.swap (listBits ea) ea).comp (Poly.listContains ea a₀ ce)).ite
    (Poly.fst (listBits ea) ea) ((Poly.swap (listBits ea) ea).comp (Poly.listCons ea))).congr
      (fun _ => rfl)
end Dedup

noncomputable def Poly.eraseDups {α : Type} [BEq α] (ea : α → List Bool) (a₀ : α)
    (ce : Poly (prodBits ea ea) boolBits (fun p : α × α => p.1 == p.2)) :
    Poly (listBits ea) (listBits ea) List.eraseDups := by
  let c := Poly.foldGrowing ea (listBits ea) a₀ (Dedup.poly ea a₀ ce) 1 (by
    intro out a
    simp only [Dedup.step]
    split
    · omega
    · rw [listBits_cons_length]; omega)
  exact ((((Poly.const (listBits ea) (listBits ea) []).pair (Poly.identity (listBits ea))).comp c).comp
    (Poly.listReverse ea a₀)).congr (fun xs => Dedup.fold xs [])

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
