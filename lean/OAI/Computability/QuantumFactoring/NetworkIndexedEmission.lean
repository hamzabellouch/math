import Mathlib
import OAI.Computability.QuantumFactoring.NetworkExpressionEmission
import OAI.Computability.QuantumFactoring.NetworkLoopEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma ofFn_forall₂ {α β : Type} {k : ℕ} (f : Fin k→α) (g : Fin k→β)
    (R : α→β→Prop) (h : ∀i,R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g):=by
  induction k with
  | zero=>simp
  | succ k ih=>rw [List.ofFn_succ,List.ofFn_succ];exact .cons (h 0) (ih _ _ (fun i=>h i.succ))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma allIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (f x))):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (p x)).foldr bandPack (constantPack (n x) true),
    (ofProcedure Emission.allPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact allPack_value _ _ (ofFn_forall₂ _ _ _ (he x))
lemma vectorIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.vector (f x)):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>vectorPack (n x) ((List.range (k x)).map (p x)),
    (ofProcedure Emission.vectorPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact vectorPack_value _ _ (he x)
lemma selectSlice (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m)
    {s : α→ℕ} (hs : Emits ea Nat.bits s) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : ∀x i,(is x i).val=s x+i.val) : NetEmits ea (fun x=>BooleanNetwork.select (is x)):=by
  apply select hn is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hm))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma rewireSlice {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f)
    (hk : Emits ea unaryCode k) {s : α→ℕ} (hs : Emits ea Nat.bits s)
    (is : ∀x,Fin (k x)→Fin (m x)) (hi : ∀x i,(is x i).val=s x+i.val) :
    NetEmits ea (fun x=>(f x).rewire (is x)):=by
  apply hf.rewire is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hk))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma padRight (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BooleanNetwork.padRight (n x) (m x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=he.fst.unaryNat
  have hN:=hn.comp he.snd
  have hc:=(ofProcedure Procedure.binaryLt).comp (hi.pair hN.unaryNat)
  obtain ⟨pc⟩:=hc
  obtain ⟨pa⟩:=(ofProcedure Emission.bitPackP).comp (hN.pair hi)
  obtain ⟨pb⟩:=(ofProcedure Emission.constantPackP).comp (hN.pair (const _ _ false))
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=
    ofProcedure ((Procedure.conditional pc pa pb).congrFun (by intro x;simp only [p,decide_eq_true_eq]))
  exact vectorIndexed hn (hn.unaryAdd hm) p hp (by
    intro x i
    dsimp only [p]
    split
    · rename_i hi
      simpa only [BooleanNetwork.padRight,hi,dite_true] using bitPack_value (⟨i.val,hi⟩ : Fin (n x))
    · rename_i hi
      exact constantPack_value _ _)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
