import Mathlib
import OAI.Computability.QuantumFactoring.NetworkPredicateEmission
import OAI.Computability.QuantumFactoring.CircuitCleanEmission
import OAI.Computability.QuantumFactoring.NetworkDependentEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def foldReverseCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl (fun a b=>compPack b a) x.2):=
  foldPack (by intros;change _+_=_+_;omega)
    (compPackP.comp ((second packCode packCode).pair (first packCode packCode)))
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma anyOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.any (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (q x)).foldr borPack (constantPack (n x) false),
    (ofProcedure Emission.anyPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact anyPack_value _ _ (ofFn_forall₂ _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩))
lemma iterate {f : ∀x,BooleanNetwork (n x) (n x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>(f x).iterate (k x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨pp⟩:=hp.comp (BitStackProgram.Emits.id (prodCode unaryCode ea)).snd
  have hps:=(ofProcedure (Procedure.tabulate (f:=fun x _=>p x) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (fun _=>p x)).foldr compPack (identityPack (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.compPackP)).comp
      (hps.pair ((ofProcedure Emission.identityPackP).comp hn)),?_⟩
  intro x
  suffices ∀j,(((List.range j).map (fun _=>p x)).foldr compPack (identityPack (n x))).val.value=
      erase ((f x).iterate j) from this (k x)
  intro j
  simp only [List.map_const',List.length_range,BooleanNetwork.iterate]
  induction j with
  | zero=>exact identityPack_value _
  | succ j ih=>
    simp only [List.replicate_succ,List.foldr_cons,BooleanNetwork.sequence] at *
    exact compPack_spec _ _ _ _ (he x) ih
lemma ite {c : α→Bool} {f g : ∀x,BooleanNetwork (n x) (m x)}
    (hc : Emits ea Procedure.boolCode c) (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>if c x then f x else g x):=by
  obtain ⟨p,hp,he⟩:=hf;obtain ⟨q,hq,eq⟩:=hg
  exact ⟨fun x=>if c x then p x else q x,hc.ite hp hq,by
    intro x;dsimp only;split
    · exact he x
    · exact eq x⟩
lemma add (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>BitArithmetic.add (n x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.add (n x),
    (ofProcedure AIGNetworkEmission.Emission.addPackP).comp hn,fun _=>AIGNetworkEmission.addPack_value _⟩
lemma wordLt {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLt (a x) (b x)):=(ha.pair hb).comp (ult hm)
lemma wordLe {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLe (a x) (b x)):=(wordLt hb ha hm).bnot
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
