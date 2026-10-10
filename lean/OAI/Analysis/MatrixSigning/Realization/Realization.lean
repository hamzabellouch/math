import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FoldRoutine
import OAI.Analysis.MatrixSigning.Encoding.WirePrimitives

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

structure Realizes {α β : Type*} (encA : α → Word) (encB : β → Word) (f : α → β) where
  cost : α → ℕ
  routine : Routine encA (fun x => encB (f x)) cost

variable {α β γ δ : Type*} {encA : α → Word} {encB : β → Word}
  {encC : γ → Word} {encD : δ → Word}

def prodCode (ea : α → Word) (eb : β → Word) (p : α×β) : Word := PairRoutine.pair (ea p.1) (eb p.2)
def listCode (ea : α → Word) : List α → Word := FramedMapRoutine.tape ea

def identity (ea : α → Word) : Realizes ea ea id where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W20.Wire.halt 0
    spec := fun x => KS.W20.Wire.halt_spec 0 (io (ea x)) }

def constant (ea : α → Word) (eb : β → Word) (y : β) : Realizes ea eb (fun _ => y) where
  cost := fun x => (ea x).length+1+((eb y).length+1)
  routine := {
    scratch := 0
    program := KS.W29.FixedSequential.compose (KS.W04.BinaryStackMoves.clearProgram 0)
      (KS.W20.Wire.writeBits 0 (eb y))
    spec := fun x => by
      have hc : KS.W03.MachineCombinators.RunSpec (KS.W04.BinaryStackMoves.clearProgram (0 : Fin 1))
          (io (ea x)) (io []) ((ea x).length+1) := by
        have h := KS.W15.RationalMultiply.clear_spec (0 : Fin 1) (io (ea x))
        convert h using 1 <;> (try rfl)
        funext j;fin_cases j;rfl
      have hw : KS.W03.MachineCombinators.RunSpec (KS.W20.Wire.writeBits (0 : Fin 1) (eb y))
          (io []) (io (eb y)) ((eb y).length+1) := by
        have h := KS.W20.Wire.writeBits_spec (0 : Fin 1) (eb y) (io [])
        convert h using 1
        funext j;fin_cases j;simp [io,Function.update]
      exact hc.compose hw }

def Realizes.then {f : α → β} {g : β → γ} (r : Realizes encA encB f)
    (s : Realizes encB encC g) : Realizes encA encC (fun x => g (f x)) where
  cost := fun x => r.cost x+s.cost (f x)
  routine := r.routine.compose (s.routine.reindex f)

def Realizes.both {f : α → β} {g : α → γ} (r : Realizes encA encB f)
    (s : Realizes encA encC g) : Realizes encA (prodCode encB encC) (fun x => (f x,g x)) where
  cost := PairRoutine.pairingTicks encA (fun x => encB (f x)) r.cost s.cost
  routine := PairRoutine.pairing r.routine s.routine

def first (ea : α → Word) (eb : β → Word) : Realizes (prodCode ea eb) ea Prod.fst where
  cost := fun p => 5*(ea p.1).length+(eb p.2).length+5
  routine := PairRoutine.fstRoutine.reindex (fun p : α×β => (ea p.1,eb p.2))

def second (ea : α → Word) (eb : β → Word) : Realizes (prodCode ea eb) eb Prod.snd where
  cost := fun p => 4*(ea p.1).length+3
  routine := PairRoutine.sndRoutine.reindex (fun p : α×β => (ea p.1,eb p.2))

def Realizes.congr {f g : α → β} (r : Realizes encA encB f) (h : ∀ x,f x=g x) :
    Realizes encA encB g := by
  have he : f=g := funext h
  exact he ▸ r

def Realizes.map {f : α → β} (r : Realizes encA encB f) :
    Realizes (listCode encA) (listCode encB) (List.map f) where
  cost := FramedMapRoutine.ticks encA (fun x => encB (f x)) r.cost
  routine := by
    have h := FramedMapRoutine.routine r.routine
    refine { scratch := h.scratch, program := h.program, spec := ?_ }
    intro xs
    simpa only [listCode,FramedMapRoutine.tape,List.flatMap_map,Function.comp_def] using h.spec xs

def Realizes.fold {f : α×β → α} (r : Realizes (prodCode encA encB) encA f) :
    Realizes (prodCode encA (listCode encB)) encA
      (fun p : α×List β => p.2.foldl (fun a b => f (a,b)) p.1) where
  cost := fun p => FoldRoutine.ticks encA encB (fun a b => f (a,b)) r.cost p.1 p.2
  routine := FoldRoutine.routine r.routine

def Realizes.changeOutput {f : α → β} (r : Realizes encA encB f)
    (ed : δ → Word) (g : α → δ) (h : ∀ x,encB (f x)=ed (g x)) :
    Realizes encA ed g where
  cost := r.cost
  routine := {
    scratch := r.routine.scratch
    program := r.routine.program
    spec := fun x => by simpa only [h x] using r.routine.spec x }

def Realizes.reindex {f : α → β} (r : Realizes encA encB f)
    (ed : δ → Word) (g : δ → α) (h : ∀ x,ed x=encA (g x)) :
    Realizes ed encB (fun x => f (g x)) where
  cost := fun x => r.cost (g x)
  routine := {
    scratch := r.routine.scratch
    program := r.routine.program
    spec := fun x => by simpa only [h x] using r.routine.spec (g x) }

end CurrentKS.Realization

end OAI
