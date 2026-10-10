import Mathlib
import OAI.Computability.QuantumFactoring.EmissionGeneralStages
import OAI.Computability.QuantumFactoring.NetworkListOperationsEmission
import OAI.Computability.QuantumFactoring.DescendingFilter

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
lemma recode {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→β} {g : α→γ} (h : Emits ea eb f) (he : ∀x,eb (f x)=ec (g x)) : Emits ea ec g:=by
  obtain ⟨p⟩:=h;exact ⟨p.result he⟩
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
abbrev filterCode := prodCode unaryCode (prodCode packCode (listCode packCode))
def FilterState.positiveView {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0<r.depth) :
    Σs,BooleanNetwork k (w (s+1)) × List (BooleanNetwork k 1):=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>exact ⟨s,v,ps⟩
lemma FilterState.positiveView_eq {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0<r.depth) :
    (⟨(r.positiveView h).1+1,(r.positiveView h).2.1,(r.positiveView h).2.2⟩ : FilterState k w)=r:=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>rfl
namespace NetsEmits
lemma foldlBand {α : Type} {ea : α→List Bool} {k : α→ℕ}
    {f : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>(f x).foldl BooleanNetwork.band (BooleanNetwork.constant true)):=by
  let p:=Emission.foldRightPack (f:=fun a b=>bandPack b a) 4 (by intro a b; dsimp [bandPack,compPack,pairPack,nodePack]; omega)
    (Emission.bandPackP.comp ((Procedure.second packCode packCode).pair (Procedure.first packCode packCode)))
  have hi:=(ofProcedure Emission.constantPackP).comp (hk.pair (const _ _ true))
  have hr:=(ofProcedure (Procedure.listReverse packCode emptyPack)).comp hf
  refine ⟨fun x=>((f x).map erasePack).foldl bandPack (constantPack (k x) true),
    ((ofProcedure p).comp (hr.pair hi)).congr (fun x=>by dsimp only;rw [List.foldr_reverse]),?_⟩
  intro x
  dsimp only
  have hgen : ∀(fs:List (BooleanNetwork (k x) 1)) (a:Pack) (b:BooleanNetwork (k x) 1),a.val.value=erase b→
      ((fs.map erasePack).foldl bandPack a).val.value=erase (fs.foldl BooleanNetwork.band b):=by
    intro fs
    induction fs with
    | nil=>intro a b h;exact h
    | cons c cs ih=>intro a b h;exact ih _ _ (bandPack_value _ _ _ _ h rfl)
  exact hgen _ _ _ (constantPack_value _ true)
end NetsEmits
lemma filterPrefixEmitter {α : Type} {ea : α→List Bool} {k S B C W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hc : ∀x s,s<S x→∀v: BooleanNetwork (k x) (w x (s+1)),v.net.count≤B x→(keep x s v).net.count≤C x)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x))) (hv : ∀x,(v x).net.count≤B x)
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hB : PolyAt (fun x=>(ea x).length) B) (hC : PolyAt (fun x=>(ea x).length) C)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hstep : Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let R:=fun x i=>(filterStep (prev x) (keep x))^[i] (⟨S x,v x,[]⟩ : FilterState (k x) (w x))
  have h0 : Emits ea filterCode (fun x=>(R x 0).code):=
    hS.pair (hV.canonical.pair (const _ _ []))
  have hs : Emits (fun x:Σa,Fin (S a)=>prodCode ea (prodCode unaryCode filterCode) (x.1,(x.2.val,(R x.1 x.2.val).code)))
      filterCode (fun x=>(R x.1 (x.2.val+1)).code):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode filterCode))).precompose
      (fun x:Σa,Fin (S a)=>(x.1,(x.2.val,(R x.1 x.2.val).code)))
    let g : (Σa,Fin (S a))→Σa,{r:FilterState (k a) (w a) // 0<r.depth}:=fun x=>⟨x.1,R x.1 x.2.val,by
      dsimp only [R];rw [filterRun_depth];dsimp only;exact Nat.sub_pos_of_lt x.2.isLt⟩
    have hh:=hstep.comp ((hx.fst.pair hx.snd.snd).recode (g:=g) (fun _=>rfl))
    exact hh.congr (fun x=>by dsimp only [g,R];rw [Function.iterate_succ_apply'])
  have hb : PolyAt (fun x:Σa,Fin (S a+1)=>(ea x.1).length) (fun x=>(filterCode (R x.1 x.2.val).code).length):=by
    have hs:=hS.unaryPoly
    have hh:=hk.unaryPoly
    let P:= (PolyAt.const _ 104).mul ((((hh.add hB).add hW).add (PolyAt.const _ 1)).pow 2)
    let Q:= (PolyAt.const _ 104).mul ((((hh.add hC).add (PolyAt.const _ 1)).add (PolyAt.const _ 1)).pow 2)
    apply (((PolyAt.const _ 2).mul hs).add (((PolyAt.const _ 2).mul P).add
      ((hs.mul (((PolyAt.const _ 2).mul Q).add (PolyAt.const _ 2))).add (PolyAt.const _ 5)))).pull
        (fun x:Σa,Fin (S a+1)=>x.1) |>.of_le
    intro x
    obtain ⟨hd,hr,hl,hls⟩:=filterRun_bounds (prev x.1) (keep x.1) (hp x.1) (S x.1) (B x.1) (C x.1) (hc x.1) (v x.1) (hv x.1) x.2.val
    have ht:=hw x.1 (R x.1 x.2.val).depth hd
    have hraw:=packCode_bound (erasePack (R x.1 x.2.val).raw)
    have hraw' : (packCode (erasePack (R x.1 x.2.val).raw)).length≤104*(k x.1+B x.1+W x.1+1)^2:=
      hraw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [erasePack,R] at *;omega) 2))
    have hlist:=listCode_length_bound packCode ((R x.1 x.2.val).pending.map erasePack) (104*(k x.1+C x.1+1+1)^2) (by
      intro a ha;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
      exact (packCode_bound _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
        have hh:=hls b hb;dsimp only [erasePack];omega) 2)))
    simp only [filterCode,FilterState.code,prodCode,pairBits_length,unaryCode,List.length_replicate,List.length_map] at hlist ⊢
    dsimp only [R] at *
    have hi:=x.2.isLt
    nlinarith
  have hf:=BitStackProgram.Emits.stages (F:=fun x i=>(R x i).code) hS h0 hs hb
  exact (NetsEmits.foldlBand hk hf.snd.snd).congr (fun x=>filterRun_result (prev x) (keep x) (S x) (v x))
end ExactQuantumFactoring.NetworkEmission

end



end OAI
