import Mathlib
import OAI.Combinatorics.UniformKServer.LiteralPartrec

namespace OAI

noncomputable section

namespace UniformKServer.StackPrimitive
open StackCompiler Primrec
open scoped Classical

abbrev Config (q m g : ℕ) := Fin q × (Fin m→List (Fin g)) × Bool

def ofState {q m g : ℕ} (s : State q m g) : Config q m g :=
  (s.control,s.store,s.yielded)

def data {q m g : ℕ} (P : Processor q m g)
    (x : Fin q × (Fin m→Option (Fin g))) : Fin q × (Fin m→Option (Option (Fin g))) × Bool :=
  let a:=P.transition x.1 none x.2 false
  (a.control,(fun i=>match a.stackOp i with | .keep=>none | .pop=>some none | .push b=>some (some b)),a.yield)

def apply {alphabetSize : ℕ} (a : Option (Option (Fin alphabetSize)))
    (s : List (Fin alphabetSize)) : List (Fin alphabetSize) :=
  match a with | none=>s | some none=>s.tail | some (some b)=>b::s

def advance {q m g : ℕ} (P : Processor q m g) (s : Config q m g) : Config q m g :=
  bif s.2.2 then s else
    let a:=data P (s.1,fun i=>(s.2.1 i).head?)
    (a.1,(fun i=>apply (a.2.1 i) (s.2.1 i)),a.2.2)

def Deterministic {q m g : ℕ} (P : Processor q m g) : Prop :=
  ∀c input h coin,P.transition c input h coin=P.transition c none h false

 theorem ofState_step {q m g : ℕ} (P : Processor q m g) (hp : Deterministic P)
    (s : State q m g) (b : Bool) :
    ofState (StackCompiler.step P s b)=advance P (ofState s) := by
  unfold StackCompiler.step advance ofState
  rw [Bool.cond_eq_ite]
  split_ifs with hy
  · rfl
  · rw [hp]
    dsimp only [data]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp only [applyOp]
        cases (P.transition s.control none (fun i=> (s.store i).head?) false).stackOp i <;> rfl
      · rfl

 theorem apply_primitive {alphabetSize : ℕ} : Primrec₂ (@apply alphabetSize) := by
  have h : Primrec (fun p : ((Option (Option (Fin alphabetSize)))×List (Fin alphabetSize))×Option (Fin alphabetSize)=>
      Option.casesOn (motive:=fun _=>List (Fin alphabetSize)) p.2 p.1.2.tail (fun b=>b::p.1.2)) := by
    exact Primrec.option_casesOn Primrec.snd (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂
  have h₀:=Primrec.option_casesOn Primrec.fst Primrec.snd h.to₂
  refine h₀.of_eq ?_
  intro p
  rcases p with ⟨a,s⟩
  cases a with
  | none=>rfl
  | some a=>cases a <;> rfl

 theorem advance_primitive {q m g : ℕ} (P : Processor q m g) : Primrec (advance P) := by
  have hd : Primrec (fun s : Config q m g=>data P (s.1,fun i=>(s.2.1 i).head?)) := by
    apply (Primrec.dom_finite (data P)).comp
    apply Primrec.pair Primrec.fst
    apply Primrec.fin_curry.mpr
    exact Primrec.list_head?.comp (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  unfold advance
  apply Primrec.cond (Primrec.snd.comp Primrec.snd) Primrec.id
  apply Primrec.pair (Primrec.fst.comp hd)
  apply Primrec.pair
  · apply Primrec.fin_curry.mpr
    exact apply_primitive.comp
      (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp (hd.comp Primrec.fst))) Primrec.snd)
      (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  · exact Primrec.snd.comp (Primrec.snd.comp hd)

 theorem iter_primitive {q m g : ℕ} (P : Processor q m g) :
    Primrec₂ (fun t : ℕ=>fun s : Config q m g=>(advance P)^[t] s) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd ((advance_primitive P).comp Primrec.snd).to₂

 theorem ofState_run {q m g : ℕ} (P : Processor q m g) (hp : Deterministic P)
    (s : State q m g) (bs : List Bool) :
    ofState (run P s bs)=(advance P)^[bs.length] (ofState s) := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    rw [run_cons,ih,ofState_step P hp,List.length_cons,Function.iterate_succ_apply]

 theorem literal_deterministic (c : Turing.ToPartrec.Code) :
    Deterministic (LiteralPartrec.processor c) := by intro c input h coin;rfl

end UniformKServer.StackPrimitive

end

end OAI
