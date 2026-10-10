import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionCombinators
import OAI.Computability.QuantumFactoring.ExpressionTemplateEmission
import OAI.Computability.QuantumFactoring.EmissionLists

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma precompose {β : Type} {eb : β→List Bool} {n m : β→ℕ}
    {f : ∀x,BooleanNetwork (n x) (m x)} (h : NetEmits eb f) (g : α→β) :
    NetEmits (fun x=>eb (g x)) (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=h
  exact ⟨fun x=>p (g x),hp.precompose g,fun x=>he (g x)⟩
lemma congr {f g : ∀x,BooleanNetwork (n x) (w x)} (h : NetEmits ea f) (he : ∀x,f x=g x) :
    NetEmits ea g:=by
  obtain ⟨p,hp,hh⟩:=h
  exact ⟨p,hp,fun x=>(hh x).trans (congrArg erase (he x))⟩
lemma bor {f g : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>BooleanNetwork.bor (f x) (g x)):=((hf.bnot).band hg.bnot).bnot
lemma compile {k : ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hw : BitStackProgram.Emits ea unaryCode w)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (w x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).compile (fs x)):=by
  classical
  choose p hp ep using hf
  let ps (x:α):=List.ofFn (fun i=>p i x)
  have hps : BitStackProgram.Emits ea (listCode packCode) ps:=BitStackProgram.Emits.ofFn hp
  let out (x:α):=exprPack (n x) (w x) (fun i:Fin k=>Emission.envVars (ps x) i.val) (e x)
  refine ⟨out,(ofProcedure (Emission.genericExprPackP Fin.val)).comp ((hn.pair (hw.pair hps)).pair he),?_⟩
  intro x
  apply exprPack_value
  intro i
  have hh : Emission.envVars (ps x) i.val=p i x:=by
    simp [Emission.envVars,ps,List.headD_eq_head?_getD,List.head?_drop,i.isLt]
  rw [hh];exact ep i x
lemma template {k : ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).template (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact compile he hn hw (fun i=>(hf i).comp (resize hb hw))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
