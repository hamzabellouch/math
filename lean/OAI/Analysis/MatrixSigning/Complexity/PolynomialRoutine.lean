import Mathlib
import OAI.Analysis.MatrixSigning.Realization.Realization
import OAI.Analysis.MatrixSigning.Realization.RoutineLength
import OAI.Analysis.MatrixSigning.Complexity.NaturalPolynomial

namespace OAI

namespace KS.W23.NaturalPolynomial

def comp : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | .constant n,_ => .constant n
  | .variable,q => q
  | .add p r,q => p.comp q+r.comp q
  | .mul p r,q => p.comp q*r.comp q
  | .power p n,q => (p.comp q)^n
@[simp] lemma eval_comp (p q : NaturalPolynomial) (x : ℕ) : (p.comp q).eval x=p.eval (q.eval x) := by
  induction p with
  | constant n => rfl
  | «variable» => rfl
  | add p r hp hr => simp only [comp,eval,eval_add,hp,hr]
  | mul p r hp hr => simp only [comp,eval,eval_mul,hp,hr]
  | power p n hp => simp only [comp,eval,eval_power,hp]
end KS.W23.NaturalPolynomial

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

class PolyTime (r : Realizes ea eb f) : Prop where
  bound : ∃ p : NaturalPolynomial,∀ x,r.cost x≤p.eval (ea x).length

lemma Realizes.output_length (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length (r.routine.spec x) 0
  simpa only [io_zero] using h

lemma prodCode_length (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega
lemma le_prodCode_right (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega

instance poly_identity (ea : α → Word) : PolyTime (identity ea) := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_constant (ea : α → Word) (eb : β → Word) (y : β) : PolyTime (constant ea eb y) :=
  ⟨⟨X+NaturalPolynomial.constant ((eb y).length+2),by intro x;change (ea x).length+1+((eb y).length+1)≤_;simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_constant];omega⟩⟩
instance poly_first (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length x
  have hs := (hq (f x)).trans (q.eval_mono (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
instance poly_congr {g : α → β} (r : Realizes ea eb f) (h : ∀ x,f x=g x) [PolyTime r] :
    PolyTime (r.congr h) := by
  have he : f=g := funext h
  subst g
  exact ‹PolyTime r›
instance poly_changeOutput (r : Realizes ea eb f) (ed : δ → Word) (g : α → δ)
    (h : ∀ x,eb (f x)=ed (g x)) [PolyTime r] : PolyTime (r.changeOutput ed g h) :=
  ⟨PolyTime.bound (r:=r)⟩
instance poly_reindex (r : Realizes ea eb f) (ed : δ → Word) (g : δ → α)
    (h : ∀ x,ed x=ea (g x)) [PolyTime r] : PolyTime (r.reindex ed g h) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  refine ⟨⟨p,?_⟩⟩
  intro x
  simp only [h x]
  exact hp (g x)

end CurrentKS.Realization

end OAI
