import Mathlib
import OAI.Computability.QuantumFactoring.BitStackBasicProcedures
import OAI.Computability.QuantumFactoring.BitStackBooleans
import OAI.Computability.QuantumFactoring.BitStackIteration

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def scanStep (f g : α→α) : List Bool×α→List Bool×α
  | ([],a)=>([],a)
  | (b::bs,a)=>(bs,if b then g a else f a)

def bitAction (f g : α→α) (a : α) (b : Bool) : α := if b then g a else f a

lemma scanStep_iterate (f g : α→α) (i : ℕ) (xs : List Bool) (a : α) :
    (scanStep f g)^[i] (xs,a)=(xs.drop i,(xs.take i).foldl (bitAction f g) a) := by
  induction i generalizing xs a with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [scanStep] using ih [] a
    | cons b bs=>simpa [scanStep,bitAction] using ih bs (if b then g a else f a)

lemma foldl_measure {m : α→ℕ} {f g : α→α} {c : ℕ}
    (hf : ∀a,m (f a)≤ m a+c) (hg : ∀a,m (g a)≤ m a+c) (xs : List Bool) (a : α) :
    m (xs.foldl (bitAction f g) a)≤ m a+xs.length*c := by
  induction xs generalizing a with
  | nil=>simp
  | cons b bs ih=>
    simp only [List.foldl_cons,List.length_cons]
    have hh : m (bitAction f g a b)≤ m a+c:=by cases b <;> simp [bitAction,hf,hg]
    have hi:=ih (bitAction f g a b)
    nlinarith

namespace Procedure
variable {ea : α→List Bool} {f g : α→α}
noncomputable def scan (p : Procedure ea ea f) (q : Procedure ea ea g) :
    Procedure (prodCode id ea) (prodCode id ea) (scanStep f g) := by
  let fst:=first (id : List Bool→List Bool) ea
  let snd:=second (id : List Bool→List Bool) ea
  let upd:=(choose p q).comp ((head.comp fst).pair snd)
  let body:=(tail.comp fst).pair upd
  let pp:=(choose body (identity (prodCode id ea))).comp
    ((isEmpty.comp fst).pair (identity (prodCode id ea)))
  exact pp.congrFun (by
    rintro ⟨xs,a⟩
    cases xs <;> rfl)

/-- Fold a variable Boolean word. The bound covers every actual intermediate
state; all pairing, data movement and loop iterations are charged. -/
noncomputable def foldBits (p : Procedure ea ea f) (q : Procedure ea ea g)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List Bool) a i,(ea ((xs.take i).foldl (bitAction f g) a)).length≤
      bound.eval (xs.length+(ea a).length)) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) := by
  let s:=scan p q
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [scanStep_iterate]
    simp only [prodCode,pairBits_length,id_eq,List.length_drop]
    have hs:=hsize x.1 x.2 i
    have hm:=eval_nat_mono bound (by omega :
      x.1.length+(ea x.2).length≤n+(2*x.1.length+(ea x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let start:=(length.comp (first (id : List Bool→List Bool) ea)).pair (identity (prodCode id ea))
  exact ((second (id : List Bool→List Bool) ea).comp (rep.comp start)).congrFun (by
    rintro ⟨xs,a⟩
    change ((scanStep f g)^[xs.length] (xs,a)).2=xs.foldl (bitAction f g) a
    rw [scanStep_iterate,List.take_length])

noncomputable def foldBitsLinear (p : Procedure ea ea f) (q : Procedure ea ea g) (c : ℕ)
    (hf : ∀a,(ea (f a)).length≤(ea a).length+c)
    (hg : ∀a,(ea (g a)).length≤(ea a).length+c) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) :=
  foldBits p q (Polynomial.C (c+1)*Polynomial.X) (by
    intro xs a i
    have hh:=foldl_measure (m:=fun a=>(ea a).length) (f:=f) (g:=g) (c:=c) hf hg (xs.take i) a
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
